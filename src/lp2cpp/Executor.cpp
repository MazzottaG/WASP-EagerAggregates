#include "Executor.h"

#include "utils/ConstantsManager.h"

#include "DLV2libs/input/InputDirector.h"

#include "parsing/AspCore2InstanceBuilder.h"

#include "datastructures/ReasonTable.h"

#include "datastructures/PostponedReasons.h"

#include "../util/WaspTrace.h"

#include "../util/WaspOptions.h"

#include "datastructures/DynamicTrie.h"

#include "datastructures/VariablesMapping.h"

#include "datastructures/VarsIndex.h"

#include "datastructures/TupleFactory.h"

#include "datastructures/AuxiliaryMapSmart.h"

#include "datastructures/VectorAsSet.h"

#include<ctime>

#include<ctime>

#include<map>

namespace aspc {
extern "C" Executor* create_object() {
    return new Executor;
}
extern "C" void destroy_object( Executor* object ) {
    delete object;
}
Executor::Executor() {
}
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
const std::string _aggr_id0 = "aggr_id0";
const std::string _aggr_id1 = "aggr_id1";
const std::string _aggr_set0 = "aggr_set0";
const std::string _aggr_set1 = "aggr_set1";
const std::string _leafPos = "leafPos";
const std::string _location = "location";
const std::string _max_total_weight = "max_total_weight";
const std::string _scost = "scost";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,VectorAsSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
bool unRoll=false;
unsigned conflictCount=0;
Executor::~Executor() {
}


const std::vector<int> EMPTY_TUPLES;
std::unordered_map<std::string, const std::string * > stringToUniqueStringPointer;
TupleFactory factory;
const std::string* parseTuple(const std::string & literalString,std::vector<int>& terms) {
    std::string predicateName;
    unsigned i = 0;
    for (i = 0; i < literalString.size(); i++) {
        if (literalString[i] == '(') {
            predicateName = literalString.substr(0, i);
            break;
        }
        if (i == literalString.size() - 1) {
            predicateName = literalString.substr(0);
        }
    }
    for (; i < literalString.size(); i++) {
        char c = literalString[i];
        if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '-') {
            int start = i;
            int openBrackets = 0;
            while ((c != ' ' && c != ',' && c != ')') || openBrackets > 0) {
                if (c == '(') {
                    openBrackets++;
                    } else if (c == ')') {
                    openBrackets--;
                    }
                i++;
                c = literalString[i];
            }
            terms.push_back(ConstantsManager::getInstance().mapConstant(literalString.substr(start, i - start)));
        }
    }
    return stringToUniqueStringPointer[predicateName];
}
//only ground lit function calls are not known a priori
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<0> pscost_({});
AuxMap<0> uscost_({});
AuxMap<0> fscost_({});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<0> pmax_total_weight_({});
AuxMap<0> umax_total_weight_({});
AuxMap<0> fmax_total_weight_({});
AuxMap<0> paggr_set1_({});
AuxMap<0> uaggr_set1_({});
AuxMap<0> faggr_set1_({});
AuxMap<0> pleafPos_({});
AuxMap<0> uleafPos_({});
AuxMap<0> fleafPos_({});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<32> paggr_id1_0_({0});
AuxMap<32> uaggr_id1_0_({0});
AuxMap<32> faggr_id1_0_({0});
AuxMap<32> paggr_set1_1_({1});
AuxMap<32> uaggr_set1_1_({1});
AuxMap<32> faggr_set1_1_({1});
AuxMap<0> plocation_({});
AuxMap<0> ulocation_({});
AuxMap<0> flocation_({});
void Executor::handleConflict(int literal,std::vector<int>& propagatedLiterals){
    if(currentDecisionLevel == -1){
        propagatedLiterals.push_back(1);
        return;
    }

    std::unordered_set<int> visitedLiterals;
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    explainExternalLiteral(literal,conflictReason,visitedLiterals,true);
    explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);
    propagatedLiterals.push_back(1);
    reasonForLiteral[literal].clear();
}
int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,std::unordered_set<int>& visitedLiteral,bool propagatorCall){
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        int internalVar = factory.getTupleFromWASPID(uVar)->getId();
        var = var>0 ? internalVar : -internalVar;
    }
    std::vector<int> stack;
    stack.push_back(var);
    while(!stack.empty()){
        int lit = stack.back();
        stack.pop_back();
        unsigned currentReasonSize=reasonForLiteral[lit].size();
        for(unsigned i = 0; i<currentReasonSize; i++){
            int reasonLiteral=reasonForLiteral[lit][i];
            if(visitedLiteral.count(reasonLiteral) == 0){
                Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);
                visitedLiteral.insert(reasonLiteral);
                if(literal->getWaspID()==0){
                    stack.push_back(reasonLiteral);
                }else{
                    int sign = reasonLiteral>0 ? 1 : -1;
                    reas.insert(sign * literal->getWaspID());
                }
            }
        }
    }
    return 0;
}
void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){
    return;
}
void Executor::executeFromFile(const char* filename) {
    DLV2::InputDirector director;
    AspCore2InstanceBuilder* builder = new AspCore2InstanceBuilder();
    director.configureBuilder(builder);
    std::vector<const char*> fileNames;
    fileNames.push_back(filename);
    director.parse(fileNames);
    executeProgramOnFacts(builder->getProblemInstance());
    delete builder;
}

inline void insertFalse(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_leafPos){
        fleafPos_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_location){
        flocation_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2(*insertResult.first);
        faggr_id1_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_max_total_weight){
        fmax_total_weight_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set1){
        faggr_set1_.insert2(*insertResult.first);
        faggr_set1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_scost){
        fscost_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_leafPos){
        pleafPos_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_location){
        plocation_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2(*insertResult.first);
        paggr_id1_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_max_total_weight){
        pmax_total_weight_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set1){
        paggr_set1_.insert2(*insertResult.first);
        paggr_set1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_scost){
        pscost_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_leafPos){
        uleafPos_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_location){
        ulocation_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2(*insertResult.first);
        uaggr_id1_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_max_total_weight){
        umax_total_weight_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set1){
        uaggr_set1_.insert2(*insertResult.first);
        uaggr_set1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_scost){
        uscost_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
    }
}
inline void Executor::onLiteralTrue(const aspc::Literal* l) {
}
inline void Executor::onLiteralUndef(const aspc::Literal* l) {
}
inline void Executor::onLiteralTrue(int var, const std::string& literalString) {
    std::vector<int> terms;
    const std::string* predicate = parseTuple(literalString,terms);
    Tuple* tuple = factory.addNewTuple(terms,predicate,var);
    TruthStatus truth = var>0 ? True : False;
    const auto& insertResult = tuple->setStatus(truth);
    if(insertResult.second){
        factory.removeFromCollisionsList(tuple->getId());
        if (var > 0) {
            insertTrue(insertResult);
        }else{
            insertFalse(insertResult);
        }
    }
}
inline void Executor::onLiteralTrue(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    std::string minus = var < 0 ? "-" : "";
    std::unordered_map<const std::string*,int>::iterator sum_it;
    TruthStatus truth = var>0 ? True : False;
    const auto& insertResult = tuple->setStatus(truth);
    if(insertResult.second){
        factory.removeFromCollisionsList(tuple->getId());
        if (var > 0) {
            insertTrue(insertResult);
        }else{
            insertFalse(insertResult);
        }
    }
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    int internalVar = var > 0 ? tuple->getId() : -tuple->getId();
    reasonForLiteral[internalVar].clear();
    std::string minus = var < 0 ? "-" : "";
    const auto& insertResult = tuple->setStatus(Undef);
    if (insertResult.second) {
        factory.removeFromCollisionsList(tuple->getId());
        insertUndef(insertResult);
    }
    if(currentDecisionLevel >= 0){
    }
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    std::cout<<"MinConflict: "<<minConflict<<std::endl;
    std::cout<<"MinHeapSize: "<<minHeapSize<<std::endl;
    std::cout<<"MaxHeapSize: "<<maxHeapSize<<std::endl;
    std::cout<<"HeapSize: "<<heapSize<<std::endl;
    undefinedLoaded=true;
    {
        const std::vector<int>* tuples = &pleafPos_.getValues({});
        const std::vector<int>* tuplesU = &uleafPos_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
                Tuple* head = factory.addNewInternalTuple({tuple->at(0),tuple->at(1)},&_aggr_set1);
                const auto& insertResult = head->setStatus(True);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(head->getId());
                    insertTrue(insertResult);
                }
            }else{
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                Tuple* head = factory.addNewInternalTuple({tuple->at(0),tuple->at(1)},&_aggr_set1);
                const auto& insertResult = head->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(head->getId());
                    insertUndef(insertResult);
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &plocation_.getValues({});
        const std::vector<int>* tuplesU = &ulocation_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            }else{
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            }
            Tuple* head = factory.addNewInternalTuple({tuple->at(0)},&_aggr_id1);
            const auto& insertResult = head->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pscost_.getValues({});
        const std::vector<int>* tuplesU = &uscost_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
                Tuple* head = factory.addNewInternalTuple({tuple->at(0),tuple->at(1),tuple->at(2)},&_aggr_set0);
                const auto& insertResult = head->setStatus(True);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(head->getId());
                    insertTrue(insertResult);
                }
            }else{
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                Tuple* head = factory.addNewInternalTuple({tuple->at(0),tuple->at(1),tuple->at(2)},&_aggr_set0);
                const auto& insertResult = head->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(head->getId());
                    insertUndef(insertResult);
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pmax_total_weight_.getValues({});
        const std::vector<int>* tuplesU = &umax_total_weight_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            }else{
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            }
            Tuple* head = factory.addNewInternalTuple({tuple->at(0)},&_aggr_id0);
            const auto& insertResult = head->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* aggregateIds = &uaggr_id0_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
            const std::vector<int>* aggrSetTuples = &uaggr_set0_.getValues({});
            int& possSum = possibleSum[it];
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possSum+=factory.getTupleFromInternalID(aggrSetTuples->at(j))->at(0);
        }
    }
}
inline void Executor::addedVarName(int var, const std::string & atom) {
    std::vector<int> terms;
    const std::string* predicate = parseTuple(atom,terms);
    Tuple* t = factory.addNewTuple(terms,predicate,var);
}
void Executor::clearPropagations() {
    propagatedLiteralsAndReasons.clear();
}
void Executor::clear() {
    failedConstraints.clear();
    paggr_id1_.clear();
    paggr_id1_0_.clear();
    paggr_id0_.clear();
    paggr_set1_.clear();
    paggr_set1_1_.clear();
    paggr_set0_.clear();
    faggr_id1_.clear();
    faggr_id1_0_.clear();
    faggr_id0_.clear();
    faggr_set1_.clear();
    faggr_set1_1_.clear();
    faggr_set0_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["aggr_set1"] = &_aggr_set1;
    stringToUniqueStringPointer["leafPos"] = &_leafPos;
    stringToUniqueStringPointer["location"] = &_location;
    stringToUniqueStringPointer["max_total_weight"] = &_max_total_weight;
    stringToUniqueStringPointer["scost"] = &_scost;
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,std::vector<int> & propagatedLiterals,std::unordered_set<int> & remainingPropagatingLiterals,const Solver* solver,PropComparator& propComparison,unsigned minConflict, unsigned minHeapSize, unsigned maxHeapSize, unsigned heapSize){
    if(tupleU->getWaspID() == 0){
        bool propagated=false;
        Tuple* realTupleU=factory.find(*tupleU);
        if(isNegated == asNegative){
            if(realTupleU->isFalse()){
                return true;
            }else if(realTupleU->isUndef()){
                const auto& insertResult = realTupleU->setStatus(True);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(realTupleU->getId());
                    insertTrue(insertResult);
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    propagated = true;
                }
            }
        }else{
            if(realTupleU->isTrue()){
                return true;
            }else if(realTupleU->isUndef()){
                const auto& insertResult = realTupleU->setStatus(False);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(realTupleU->getId());
                    insertFalse(insertResult);
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    propagated = true;
                }
            }
        }
        if(propagated){
            int it = tupleU->getId();
            int sign = isNegated != asNegative ? -1 : 1;
            stack.push_back(sign*it);
            levelToIntLiterals[currentDecisionLevel].push_back(sign*it);
        }
    }else{
        int it = tupleU->getWaspID();
        int sign = isNegated == asNegative ? 1 : -1;
        if(remainingPropagatingLiterals.count(it*sign)==0){
            remainingPropagatingLiterals.insert(it*sign);
            propagatedLiterals.push_back(it*sign);
            if(conflictCount > minConflict){
                if(propagatedLiterals.size() == heapSize){/*std::cout<<"Heap size: "<<heapSize<<std::endl;*/std::make_heap(propagatedLiterals.begin(),propagatedLiterals.end(),propComparison);/*for(int i=0; i < heapSize && i < propagatedLiterals.size(); i++)std::cout<<solver->getActivityForLiteral(propagatedLiterals[i])<<" ";std::cout<<std::endl;*/}
                if(propagatedLiterals.size() > heapSize){
                    int heapMinimum = propagatedLiterals.front();
                    Activity heapMinimumWeight = solver->getActivityForLiteral(heapMinimum);
                    Activity currentWeight = solver->getActivityForLiteral(propagatedLiterals.back());
                    if(currentWeight > heapMinimumWeight){
                        std::pop_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);
                        std::swap(propagatedLiterals[heapSize-1],propagatedLiterals[propagatedLiterals.size()-1]);
                        std::push_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);
                    }
                }
            }
        }
    }
    return false;
}
void Executor::printInternalLiterals(){
}
void Executor::unRollToLevel(int decisionLevel){
    conflictCount++;
    for(int literealToProp : remainingPropagatingLiterals){
        int var = literealToProp > 0 ? literealToProp : -literealToProp;
        Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
        int internalLit = literealToProp > 0 ? literalNotPropagated->getId() : -literalNotPropagated->getId();
        if(literalNotPropagated!=NULL)
            reasonForLiteral[internalLit].clear();
    }
    remainingPropagatingLiterals.clear();
    while(currentDecisionLevel > decisionLevel){
        while(!levelToIntLiterals[currentDecisionLevel].empty()){
            int var = levelToIntLiterals[currentDecisionLevel].back();
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral[var].clear();
            int uVar = var>0 ? var : -var;
            Tuple* tuple = factory.getTupleFromInternalID(uVar);
            const auto& insertResult = tuple->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(tuple->getId());
                insertUndef(insertResult);
            }
            if(tuple->getPredicateName() == &_aggr_set0){
                {
                    const std::vector<int>* aggrIds = &paggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
            }
        }
        levelToIntLiterals.erase(currentDecisionLevel);
        currentDecisionLevel--;
    }
    clearConflictReason();
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts,std::vector<int>& propagatedLiterals) {
    int decisionLevel = facts[0];
    currentDecisionLevel=decisionLevel;
    clearPropagations();
    std::vector<int> propagationStack;
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
        int factVar = facts[i]>0 ? facts[i] : -facts[i];
        int minus = facts[i]<0 ? -1 : 1;
        propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());
        remainingPropagatingLiterals.erase(facts[i]);
    }
    if(decisionLevel>-1) {
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            const std::vector<int>* trueHeads = &paggr_set0_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
                int C = head->at(0);
                int P = head->at(1);
                int I = head->at(2);
                const Tuple* tuple = factory.find({C,P,I},&_scost);
                if(!tuple->isTrue()){
                    if(!tuple->isUndef()){
                        propagatedLiterals.push_back(1);
                    }else{
                        propUndefined(tuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                }
            }
            const std::vector<int>* undefHeads = &uaggr_set0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
                int C = head->at(0);
                int P = head->at(1);
                int I = head->at(2);
                const Tuple* tuple = factory.find({C,P,I},&_scost);
                if(!tuple->isTrue()){
                    if(!tuple->isUndef()){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* falseHeads = &faggr_set0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
                int C = head->at(0);
                int P = head->at(1);
                int I = head->at(2);
                const Tuple* tuple = factory.find({C,P,I},&_scost);
                if(!tuple->isTrue()){
                    if(tuple->isUndef()){
                        propUndefined(tuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    propagatedLiterals.push_back(1);
                }
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < M+1-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= M+1-posSum+currentJoinTuple->at(0)) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= M+1){
                    propagatedLiterals.push_back(1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= M+1-currentJoinTuple->at(0)){
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i);
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    int it = tuplesF->at(i);
                                    reason.push_back(-it);
                                    reasonForLiteral[-itProp].insert(-it);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= M+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < M+1 - posSum){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<int>* trueHeads = &paggr_set1_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = head->at(0);
                int P = head->at(1);
                const Tuple* tuple = factory.find({X,P},&_leafPos);
                if(!tuple->isTrue()){
                    if(!tuple->isUndef()){
                        propagatedLiterals.push_back(1);
                    }else{
                        propUndefined(tuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                }
            }
            const std::vector<int>* undefHeads = &uaggr_set1_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
                int X = head->at(0);
                int P = head->at(1);
                const Tuple* tuple = factory.find({X,P},&_leafPos);
                if(!tuple->isTrue()){
                    if(!tuple->isUndef()){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* falseHeads = &faggr_set1_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
                int X = head->at(0);
                int P = head->at(1);
                const Tuple* tuple = factory.find({X,P},&_leafPos);
                if(!tuple->isTrue()){
                    if(tuple->isUndef()){
                        propUndefined(tuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    propagatedLiterals.push_back(1);
                }
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id1_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(joinTuples->size() + joinTuplesU->size() < 2){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 2){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(joinTuples->size() >= 2){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 2 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));
                        if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i);
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i);
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(joinTuples->size() >= 2){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &plocation_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulocation_.getValues({});
                else if(tupleU->getPredicateName() == &_location && !tupleUNegated)
                    undeRepeated.push_back(tupleU);
                unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                for(unsigned i = 0; i<totalSize; i++){
                    unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                    if(totalSize>currentSize){
                        i-=totalSize-currentSize;
                        totalSize=currentSize;
                    }
                    if(tuplesU!=&EMPTY_TUPLES)
                        tupleU = NULL;
                    const Tuple* tuple0 = NULL;
                    if(i<tuples->size())
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int P = tuple0->at(0);
                        const Tuple* tuple1 = factory.find({P},&_aggr_id1);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_aggr_id1 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else{
                                propagatedLiterals.push_back(1);
                            }
                        }
                    }
                }
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &pmax_total_weight_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &umax_total_weight_.getValues({});
                else if(tupleU->getPredicateName() == &_max_total_weight && !tupleUNegated)
                    undeRepeated.push_back(tupleU);
                unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                for(unsigned i = 0; i<totalSize; i++){
                    unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                    if(totalSize>currentSize){
                        i-=totalSize-currentSize;
                        totalSize=currentSize;
                    }
                    if(tuplesU!=&EMPTY_TUPLES)
                        tupleU = NULL;
                    const Tuple* tuple0 = NULL;
                    if(i<tuples->size())
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int M = tuple0->at(0);
                        const Tuple* tuple1 = factory.find({M},&_aggr_id0);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_aggr_id0 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else{
                                propagatedLiterals.push_back(1);
                            }
                        }
                    }
                }
            }
        }
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aggr_set0){
            int C = starter[0];
            int P = starter[1];
            int I = starter[2];
            const Tuple* tuple = factory.find({C,P,I}, &_scost);
            if(startVar > 0){
                if(tuple->isFalse()){
                    int it = tuple->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it, propagatedLiterals);
                    return;
                }else{
                    if(tuple->isUndef()){
                        int it = tuple->getId();
                        if(reasonForLiteral.count(it) == 0 || reasonForLiteral[it].empty())
                            reasonForLiteral[it].insert(startVar);
                        propUndefined(tuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuple->isTrue()){
                    int it = tuple->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(tuple->isUndef()){
                        int it = tuple->getId();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(tuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_scost){
            int C = starter[0];
            int P = starter[1];
            int I = starter[2];
            if(startVar > 0){
                Tuple* head = factory.find({C,P,I}, &_aggr_set0);
                if(!head->isTrue() && !head->isUndef()){
                    int it = head->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it, propagatedLiterals);
                    return;
                }else if(head->isUndef()){
                    int it = head->getId();
                    if(reasonForLiteral.count(it) == 0  || reasonForLiteral[it].empty())
                        reasonForLiteral[it].insert(startVar);
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                Tuple* head = factory.find({C,P,I}, &_aggr_set0);
                if(head != NULL && head->isTrue()){
                    int it = head->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(head != NULL && head->isUndef()){
                        int it = head->getId();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            int M = starter[0];
            std::vector<int> sharedVar({});
            const std::vector<int>* tuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<int>* tuplesU = &uaggr_set0_.getValues(sharedVar);
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=M+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else{
                    std::vector<int> reason;
                    for(int index=0; index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actSum >= M+1-currentTuple->at(0)){
                            int itProp =currentTuple->getId();
                            if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].empty()){
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        int it = tuples->at(i);
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    reason.push_back(startVar);
                                    reasonForLiteral[-itProp].insert(startVar);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }else{
                int& actSum = actualSum[uStartVar];
                int& posSum = possibleSum[uStartVar];
                if(actSum+posSum < M+1){
                    const std::vector<int>* tuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actSum < M+1-posSum+currentTuple->at(0)){
                            int itProp = tuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                                const std::vector<int>* tuplesF = &faggr_set0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < M+1-posSum){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= M+1-posSum+currentJoinTuple->at(0)) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= M+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= M+1-currentJoinTuple->at(0)){
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i);
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    int it = tuplesF->at(i);
                                    reason.push_back(-it);
                                    reasonForLiteral[-itProp].insert(-it);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= M+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < M+1 - posSum){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id0 && startVar > 0){
                int M = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({M},&_max_total_weight);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_max_total_weight || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_max_total_weight && startVar > 0){
                int M = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({M},&_aggr_id0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aggr_id0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_set1){
            int X = starter[0];
            int P = starter[1];
            const Tuple* tuple = factory.find({X,P}, &_leafPos);
            if(startVar > 0){
                if(tuple->isFalse()){
                    int it = tuple->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it, propagatedLiterals);
                    return;
                }else{
                    if(tuple->isUndef()){
                        int it = tuple->getId();
                        if(reasonForLiteral.count(it) == 0 || reasonForLiteral[it].empty())
                            reasonForLiteral[it].insert(startVar);
                        propUndefined(tuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuple->isTrue()){
                    int it = tuple->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(tuple->isUndef()){
                        int it = tuple->getId();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(tuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_leafPos){
            int X = starter[0];
            int P = starter[1];
            if(startVar > 0){
                Tuple* head = factory.find({X,P}, &_aggr_set1);
                if(!head->isTrue() && !head->isUndef()){
                    int it = head->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it, propagatedLiterals);
                    return;
                }else if(head->isUndef()){
                    int it = head->getId();
                    if(reasonForLiteral.count(it) == 0  || reasonForLiteral[it].empty())
                        reasonForLiteral[it].insert(startVar);
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                Tuple* head = factory.find({X,P}, &_aggr_set1);
                if(head != NULL && head->isTrue()){
                    int it = head->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(head != NULL && head->isUndef()){
                        int it = head->getId();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id1){
            int P = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<int>* tuples = &paggr_set1_1_.getValues(sharedVar);
            const std::vector<int>* tuplesU = &uaggr_set1_1_.getValues(sharedVar);
            if(startVar < 0){
                if(tuples->size()>=2){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 2 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].empty()){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 2){
                    const std::vector<int>* tuplesF = &faggr_set1_1_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() + tuplesU->size() == 2){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* tuplesF = &faggr_set1_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set1){
            const std::vector<int>* tuples = &paggr_id1_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 2){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(joinTuples->size() >= 2){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() == 2 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));
                        if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i);
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i);
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(joinTuples->size() >= 2){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id1 && startVar > 0){
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({P},&_location);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_location || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_location && startVar > 0){
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({P},&_aggr_id1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aggr_id1 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
        }
    }
    if(!propagatedLiterals.empty()){
        if(solver->getActivityForLiteral(propagatedLiterals.front()) < 1){
            if(heapSize > minHeapSize)heapSize--;
        }else if(heapSize < Executor::maxHeapSize) heapSize++;
    }
    if(conflictCount > minConflict && propagatedLiterals.size() >= heapSize){/*std::cout<<"sort heap"<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);}
}
}
