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

#include<memory>

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
const std::string _location = "location";
const std::string _max_total_weight = "max_total_weight";
const std::string _leafPos = "leafPos";
const std::string _scost = "scost";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
bool unRoll=false;
unsigned conflictCount=0;
Executor::~Executor() {
}


const std::vector<int> EMPTY_TUPLES_VEC;
const std::set<int,AggregateSetCmp> EMPTY_TUPLES_SET;
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
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<0> pscost_({});
AuxMap<0> uscost_({});
AuxMap<0> fscost_({});
AuxMap<0> pmax_total_weight_({});
AuxMap<0> umax_total_weight_({});
AuxMap<0> fmax_total_weight_({});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<32> paggr_id1_0_({0});
AuxMap<32> uaggr_id1_0_({0});
AuxMap<32> faggr_id1_0_({0});
AuxMap<32> pleafPos_1_({1});
AuxMap<32> uleafPos_1_({1});
AuxMap<32> fleafPos_1_({1});
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
    reasonForLiteral[literal].get()->clear();
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
        VectorAsSet<int>* currentReas = reasonForLiteral[lit].get();
        unsigned currentReasonSize= currentReas != NULL ? currentReas->size() : 0;
        for(unsigned i = 0; i<currentReasonSize; i++){
            int reasonLiteral=currentReas->at(i);
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
        fleafPos_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_scost){
        fscost_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_location){
        flocation_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2Vec(*insertResult.first);
        faggr_id1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_max_total_weight){
        fmax_total_weight_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_leafPos){
        pleafPos_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_scost){
        pscost_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_location){
        plocation_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2Vec(*insertResult.first);
        paggr_id1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_max_total_weight){
        pmax_total_weight_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_leafPos){
        uleafPos_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_scost){
        uscost_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_location){
        ulocation_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2Vec(*insertResult.first);
        uaggr_id1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_max_total_weight){
        umax_total_weight_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2Vec(*insertResult.first);
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
    if(tuple->getPredicateName() == &_scost){
        {
            const std::vector<int>* aggrIds = &paggr_id0_.getValuesVec({});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(0);
                possibleSum[itAggrId]-=tuple->at(0);
            }
        }
        {
            const std::vector<int>* aggrIds = &uaggr_id0_.getValuesVec({});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(0);
                possibleSum[itAggrId]-=tuple->at(0);
            }
        }
        {
            const std::vector<int>* aggrIds = &faggr_id0_.getValuesVec({});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(0);
                possibleSum[itAggrId]-=tuple->at(0);
            }
        }
    }
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    int internalVar = var > 0 ? tuple->getId() : -tuple->getId();
    VectorAsSet<int>* reas = reasonForLiteral[internalVar].get();
    if(reas!=NULL)reas->clear();
    std::string minus = var < 0 ? "-" : "";
    const auto& insertResult = tuple->setStatus(Undef);
    if (insertResult.second) {
        factory.removeFromCollisionsList(tuple->getId());
        insertUndef(insertResult);
    }
    if(currentDecisionLevel >= 0){
        if(tuple->getPredicateName() == &_scost){
            {
                const std::vector<int>* aggrIds = &paggr_id0_.getValuesVec({});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<int>* aggrIds = &uaggr_id0_.getValuesVec({});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<int>* aggrIds = &faggr_id0_.getValuesVec({});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
        }
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
        const std::vector<int>* tuples = &plocation_.getValuesVec({});
        const std::vector<int>* tuplesU = &ulocation_.getValuesVec({});
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
        const std::vector<int>* tuples = &pmax_total_weight_.getValuesVec({});
        const std::vector<int>* tuplesU = &umax_total_weight_.getValuesVec({});
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
        const std::vector<int>* aggregateIds = &uaggr_id0_.getValuesVec({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(it);
            const std::set<int,AggregateSetCmp>* aggrSetTuples = &uscost_.getValuesSet({});
            int& possSum = possibleSum[it];
            for(auto itUndef=aggrSetTuples->begin(); itUndef!=aggrSetTuples->end(); itUndef++){
                possSum+=factory.getTupleFromInternalID(*itUndef)->at(0);
            }
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
    faggr_id1_.clear();
    faggr_id1_0_.clear();
    faggr_id0_.clear();
}
void Executor::init() {
    std::cout<<"Init"<<std::endl;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["location"] = &_location;
    stringToUniqueStringPointer["max_total_weight"] = &_max_total_weight;
    stringToUniqueStringPointer["leafPos"] = &_leafPos;
    stringToUniqueStringPointer["scost"] = &_scost;
    factory.setIndexForAggregateSet(0,&_scost);
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
                    if(tupleU->getPredicateName() == &_scost){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_.getValuesVec({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_.getValuesVec({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_.getValuesVec({});
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
                    if(tupleU->getPredicateName() == &_scost){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_.getValuesVec({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_.getValuesVec({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_.getValuesVec({});
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
                if(propagatedLiterals.size() > heapSize){
                    int heapMinimum = propagatedLiterals.front();
                    Activity heapMinimumWeight = solver->getActivityForLiteral(heapMinimum);
                    Activity currentWeight = solver->getActivityForLiteral(propagatedLiterals.back());
                    if(currentWeight > heapMinimumWeight){
                        std::pop_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);
                        std::swap(propagatedLiterals[heapSize-1],propagatedLiterals[propagatedLiterals.size()-1]);
                        std::push_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);
                    }
                }else{
                    std::push_heap(propagatedLiterals.begin(),propagatedLiterals.end(),propComparison);
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
            reasonForLiteral[internalLit].get()->clear();
    }
    remainingPropagatingLiterals.clear();
    while(currentDecisionLevel > decisionLevel){
        while(!levelToIntLiterals[currentDecisionLevel].empty()){
            int var = levelToIntLiterals[currentDecisionLevel].back();
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral[var].get()->clear();
            int uVar = var>0 ? var : -var;
            Tuple* tuple = factory.getTupleFromInternalID(uVar);
            const auto& insertResult = tuple->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(tuple->getId());
                insertUndef(insertResult);
            }
            if(tuple->getPredicateName() == &_scost){
                {
                    const std::vector<int>* aggrIds = &paggr_id0_.getValuesVec({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id0_.getValuesVec({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id0_.getValuesVec({});
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
            const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::set<int,AggregateSetCmp>* joinTuples = &pscost_.getValuesSet(sharedVar);
                const std::set<int,AggregateSetCmp>* joinTuplesU = &uscost_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < M+1-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*index);
                        if(actSum >= M+1-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *index;
                        if(shared_reason.get()->empty()){
                            const std::set<int,AggregateSetCmp>* joinTuplesF = &fscost_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                            reasonForLiteral[itProp]=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int M = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::set<int,AggregateSetCmp>* joinTuples = &pscost_.getValuesSet(sharedVar);
                const std::set<int,AggregateSetCmp>* joinTuplesU = &uscost_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= M+1){
                    propagatedLiterals.push_back(1);
                }else{
                    for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*index);
                        int itProp = *index;
                        if(actSum < M+1-currentJoinTuple->at(0))break;
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                if(shared_reason.get()->empty()){
                                    for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){
                                        int it = *i;
                                        shared_reason.get()->insert(it);
                                    }
                                    int it = tuplesF->at(i);
                                    shared_reason.get()->insert(-it);
                                }
                                reasonForLiteral[-itProp]=shared_reason;
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                    int M = currentTuple->at(0);
                    std::vector<int> sharedVar({});
                    const std::set<int,AggregateSetCmp>* joinTuples = &pscost_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uscost_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesU->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum >= M+1){
                        int itProp = tuplesU->at(i);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                            for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                int it = *j;
                                shared_reason.get()->insert(it);
                            }
                            reasonForLiteral[itProp]=shared_reason;
                        }
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else if(actSum < M+1 - posSum){
                        int itProp = tuplesU->at(i);
                        if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                            const std::set<int,AggregateSetCmp>* joinTuplesF = &fscost_.getValuesSet(sharedVar);
                            for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                                int it = *j;
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-itProp]=shared_reason;
                        }
                        propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        i++;
                    }
                }//close undef for
            }//close aggr set starter
            {
                const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int P = currentTuple->at(0);
                    std::vector<int> sharedVar({currentTuple->at(0)});
                    const std::vector<int>* joinTuples = &pleafPos_1_.getValuesVec(sharedVar);
                    const std::vector<int>* joinTuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                    int aggrIdIt=tuples->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(joinTuples->size() + joinTuplesU->size() < 2){
                        propagatedLiterals.push_back(1);
                    }else if(joinTuples->size() + joinTuplesU->size() == 2){
                        if(!joinTuplesU->empty()){
                            const std::vector<int>* joinTuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        for(unsigned index=0; index<joinTuplesU->size(); index++){
                            int itProp = joinTuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                reasonForLiteral[itProp]=shared_reason;
                            }
                            propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                    int P = currentTuple->at(0);
                    std::vector<int> sharedVar({currentTuple->at(0)});
                    const std::vector<int>* joinTuples = &pleafPos_1_.getValuesVec(sharedVar);
                    const std::vector<int>* joinTuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                    int aggrIdIt=tuplesF->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(joinTuples->size() >= 2){
                        propagatedLiterals.push_back(1);
                    }else if(joinTuples->size() == 2 -1){
                        for(unsigned index=0; index<joinTuplesU->size(); index++){
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                            int itProp = joinTuplesU->at(index);
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                if(shared_reason.get()->empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i);
                                        shared_reason.get()->insert(it);
                                    }
                                    int it = tuplesF->at(i);
                                    shared_reason.get()->insert(-it);
                                }
                                reasonForLiteral[-itProp]=shared_reason;
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                    int P = currentTuple->at(0);
                    std::vector<int> sharedVar({currentTuple->at(0)});
                    const std::vector<int>* joinTuples = &pleafPos_1_.getValuesVec(sharedVar);
                    const std::vector<int>* joinTuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                    int aggrIdIt=tuplesU->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(joinTuples->size() >= 2){
                        int itProp = tuplesU->at(i);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                            for(unsigned j = 0; j < joinTuples->size(); j++){
                                int it = joinTuples->at(j);
                                shared_reason.get()->insert(it);
                            }
                            reasonForLiteral[itProp]=shared_reason;
                        }
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else if(joinTuples->size() + joinTuplesU->size() < 2){
                        int itProp = tuplesU->at(i);
                        if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                            const std::vector<int>* joinTuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                            for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                int it = joinTuplesF->at(j);
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-itProp]=shared_reason;
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
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &plocation_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ulocation_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_location && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                        if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                                    if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0)
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                    else internalProps.push_back({tupleU,tupleUNegated});
                                }else{
                                    propagatedLiterals.push_back(1);
                                }
                            }
                        }
                    }
                    for(auto pair : internalProps)
                        propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &pmax_total_weight_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &umax_total_weight_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_max_total_weight && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                        if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                                    if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0)
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                    else internalProps.push_back({tupleU,tupleUNegated});
                                }else{
                                    propagatedLiterals.push_back(1);
                                }
                            }
                        }
                    }
                    for(auto pair : internalProps)
                        propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }//close decision level == -1
        while(!propagationStack.empty()){
            int startVar = propagationStack.back();
            int uStartVar = startVar<0 ? -startVar : startVar;
            Tuple starter (*factory.getTupleFromInternalID(uStartVar));
            std::string minus = startVar < 0 ? "not " : "";
            propagationStack.pop_back();
            if(starter.getPredicateName() == &_aggr_id0){
                int M = starter[0];
                std::vector<int> sharedVar({});
                const std::set<int,AggregateSetCmp>* tuples = &pscost_.getValuesSet(sharedVar);
                const std::set<int,AggregateSetCmp>* tuplesU = &uscost_.getValuesSet(sharedVar);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(startVar < 0){
                    int& actSum = actualSum[uStartVar];
                    if(actSum>=M+1){
                        for(auto i =tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }else{
                        if(!tuplesU->empty()){
                            for(auto i = tuples->begin(); i != tuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            shared_reason.get()->insert(startVar);
                        }
                        for(auto itUndef = tuplesU->begin(); itUndef != tuplesU->end(); itUndef++){
                            const Tuple* currentTuple = factory.getTupleFromInternalID(*itUndef);
                            if(actSum >= M+1-currentTuple->at(0)){
                                int itProp = currentTuple->getId();
                                if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty())
                                    reasonForLiteral[-itProp]=shared_reason;
                                propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else break;
                        }
                    }
                }else{
                    int& actSum = actualSum[uStartVar];
                    int& posSum = possibleSum[uStartVar];
                    if(actSum+posSum < M+1){
                        const std::set<int,AggregateSetCmp>* tuplesF = &fscost_.getValuesSet(sharedVar);
                        for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }else{
                        for(auto index=tuplesU->begin(); index != tuplesU->end(); index++){
                            const Tuple* currentTuple = factory.getTupleFromInternalID(*index);
                            if(actSum < M+1-posSum+currentTuple->at(0)){
                                int itProp = currentTuple->getId();
                                if(shared_reason.get()->empty()){
                                    const std::set<int,AggregateSetCmp>* tuplesF = &fscost_.getValuesSet(sharedVar);
                                    for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                                        int it = *i;
                                        shared_reason.get()->insert(-it);
                                    }
                                    shared_reason.get()->insert(startVar);
                                }
                                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                    reasonForLiteral[itProp]=shared_reason;
                                }
                                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else break;
                        }
                    }
                }
            }//close aggr id starter
            if(starter.getPredicateName() == &_scost){
                const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
                const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int M = currentTuple->at(0);
                    std::vector<int> sharedVar({});
                    const std::set<int,AggregateSetCmp>* joinTuples = &pscost_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uscost_.getValuesSet(sharedVar);
                    int aggrIdIt=tuples->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum < M+1-posSum){
                        int itProp = tuples->at(i);
                        const std::set<int,AggregateSetCmp>* joinTuplesF = &fscost_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itProp]=shared_reason;
                        handleConflict(-itProp, propagatedLiterals);
                        return;
                    }else{
                        for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*index);
                            if(actSum >= M+1-posSum+currentJoinTuple->at(0)) {break;}
                            int itProp = *index;
                            if(shared_reason.get()->empty()){
                                const std::set<int,AggregateSetCmp>* joinTuplesF = &fscost_.getValuesSet(sharedVar);
                                for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(-it);
                                }
                                int itAggrId = tuples->at(i);
                                shared_reason.get()->insert(itAggrId);
                            }
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                reasonForLiteral[itProp]=shared_reason;
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                    int M = currentTuple->at(0);
                    std::vector<int> sharedVar({});
                    const std::set<int,AggregateSetCmp>* joinTuples = &pscost_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uscost_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesF->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    if(actSum >= M+1){
                        int itProp = tuplesF->at(i);
                        for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[itProp]=shared_reason;
                        handleConflict(itProp, propagatedLiterals);
                        return;
                    }else{
                        for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*index);
                            int itProp = *index;
                            if(actSum < M+1-currentJoinTuple->at(0))break;
                                if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                    if(shared_reason.get()->empty()){
                                        for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){
                                            int it = *i;
                                            shared_reason.get()->insert(it);
                                        }
                                        int it = tuplesF->at(i);
                                        shared_reason.get()->insert(-it);
                                    }
                                    reasonForLiteral[-itProp]=shared_reason;
                                }
                                propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }//close false for
                    for(unsigned i = 0; i<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                        int M = currentTuple->at(0);
                        std::vector<int> sharedVar({});
                        const std::set<int,AggregateSetCmp>* joinTuples = &pscost_.getValuesSet(sharedVar);
                        const std::set<int,AggregateSetCmp>* joinTuplesU = &uscost_.getValuesSet(sharedVar);
                        int aggrIdIt=tuplesU->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        int& posSum = possibleSum[aggrIdIt];
                        if(actSum >= M+1){
                            int itProp = tuplesU->at(i);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                    int it = *j;
                                    shared_reason.get()->insert(it);
                                }
                                reasonForLiteral[itProp]=shared_reason;
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else if(actSum < M+1 - posSum){
                            int itProp = tuplesU->at(i);
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                const std::set<int,AggregateSetCmp>* joinTuplesF = &fscost_.getValuesSet(sharedVar);
                                for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                                    int it = *j;
                                    shared_reason.get()->insert(-it);
                                }
                                reasonForLiteral[-itProp]=shared_reason;
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
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].get() == NULL || reasonForLiteral[var].get()->empty()){
                                    {
                                        int it = starter.getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[var]=shared_reason;
                                }else{
                                }
                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                                return;
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                    if(starter.getPredicateName() == &_max_total_weight && startVar > 0){
                        int M = starter[0];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].get() == NULL || reasonForLiteral[var].get()->empty()){
                                    {
                                        int it = starter.getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[var]=shared_reason;
                                }else{
                                }
                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                                return;
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
                if(starter.getPredicateName() == &_aggr_id1){
                    int P = starter[0];
                    std::vector<int> sharedVar({starter[0]});
                    const std::vector<int>* tuples = &pleafPos_1_.getValuesVec(sharedVar);
                    const std::vector<int>* tuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(startVar < 0){
                        if(tuples->size()>=2){
                            for(unsigned i =0; i< tuples->size(); i++){
                                int it = tuples->at(i);
                                shared_reason.get()->insert(it);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }else if(tuples->size() == 2 -1){
                            for(unsigned i =0; i< tuples->size(); i++){
                                int it = tuples->at(i);
                                shared_reason.get()->insert(it);
                            }
                            shared_reason.get()->insert(startVar);
                            for(unsigned i =0; i<tuplesU->size(); i++){
                                int itProp = tuplesU->at(i);
                                if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                    reasonForLiteral[-itProp]=shared_reason;
                                }
                                propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }else{
                        if(tuples->size()+tuplesU->size() < 2){
                            const std::vector<int>* tuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }else if(tuples->size() + tuplesU->size() == 2){
                            if(!tuplesU->empty()){
                                const std::vector<int>* tuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    shared_reason.get()->insert(-it);
                                }
                                shared_reason.get()->insert(startVar);
                            }
                            for(unsigned index=0;index<tuplesU->size();index++){
                                int itProp = tuplesU->at(index);
                                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                    reasonForLiteral[itProp]=shared_reason;
                                }
                                propUndefined(factory.getTupleFromInternalID(tuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }
                }//close aggr id starter
                if(starter.getPredicateName() == &_leafPos){
                    const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
                    const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
                    const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
                    for(unsigned i = 0; i<tuples->size(); i++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                        int P = currentTuple->at(0);
                        std::vector<int> sharedVar({currentTuple->at(0)});
                        const std::vector<int>* joinTuples = &pleafPos_1_.getValuesVec(sharedVar);
                        const std::vector<int>* joinTuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                        int aggrIdIt=tuples->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(joinTuples->size() + joinTuplesU->size() < 2){
                            int itProp = tuples->at(i);
                            const std::vector<int>* joinTuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                            for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                int it = joinTuplesF->at(j);
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-itProp]=shared_reason;
                            handleConflict(-itProp, propagatedLiterals);
                            return;
                        }else if(joinTuples->size() + joinTuplesU->size() == 2){
                            if(!joinTuplesU->empty()){
                                const std::vector<int>* joinTuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                                for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                    int it = joinTuplesF->at(i);
                                    shared_reason.get()->insert(-it);
                                }
                                int itAggrId = tuples->at(i);
                                shared_reason.get()->insert(itAggrId);
                            }
                            for(unsigned index=0; index<joinTuplesU->size(); index++){
                                int itProp = joinTuplesU->at(index);
                                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                    reasonForLiteral[itProp]=shared_reason;
                                }
                                propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }//close true for
                    for(unsigned i = 0; i<tuplesF->size(); i++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                        int P = currentTuple->at(0);
                        std::vector<int> sharedVar({currentTuple->at(0)});
                        const std::vector<int>* joinTuples = &pleafPos_1_.getValuesVec(sharedVar);
                        const std::vector<int>* joinTuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                        int aggrIdIt=tuplesF->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(joinTuples->size() >= 2){
                            int itProp = tuplesF->at(i);
                            for(unsigned j =0; j< joinTuples->size(); j++){
                                int it = joinTuples->at(j);
                                shared_reason.get()->insert(it);
                            }
                            reasonForLiteral[itProp]=shared_reason;
                            handleConflict(itProp, propagatedLiterals);
                            return;
                        }else if(joinTuples->size() == 2 -1){
                            for(unsigned index=0; index<joinTuplesU->size(); index++){
                                const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                                int itProp = joinTuplesU->at(index);
                                if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                    if(shared_reason.get()->empty()){
                                        for(unsigned i =0; i< joinTuples->size(); i++){
                                            int it = joinTuples->at(i);
                                            shared_reason.get()->insert(it);
                                        }
                                        int it = tuplesF->at(i);
                                        shared_reason.get()->insert(-it);
                                    }
                                    reasonForLiteral[-itProp]=shared_reason;
                                }
                                propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }//close false for
                    for(unsigned i = 0; i<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                        int P = currentTuple->at(0);
                        std::vector<int> sharedVar({currentTuple->at(0)});
                        const std::vector<int>* joinTuples = &pleafPos_1_.getValuesVec(sharedVar);
                        const std::vector<int>* joinTuplesU = &uleafPos_1_.getValuesVec(sharedVar);
                        int aggrIdIt=tuplesU->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(joinTuples->size() >= 2){
                            int itProp = tuplesU->at(i);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){
                                for(unsigned j = 0; j < joinTuples->size(); j++){
                                    int it = joinTuples->at(j);
                                    shared_reason.get()->insert(it);
                                }
                                reasonForLiteral[itProp]=shared_reason;
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else if(joinTuples->size() + joinTuplesU->size() < 2){
                            int itProp = tuplesU->at(i);
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){
                                const std::vector<int>* joinTuplesF = &fleafPos_1_.getValuesVec(sharedVar);
                                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                    int it = joinTuplesF->at(j);
                                    shared_reason.get()->insert(-it);
                                }
                                reasonForLiteral[-itProp]=shared_reason;
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
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].get() == NULL || reasonForLiteral[var].get()->empty()){
                                    {
                                        int it = starter.getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[var]=shared_reason;
                                }else{
                                }
                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                                return;
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                    if(starter.getPredicateName() == &_location && startVar > 0){
                        int P = starter[0];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].get() == NULL || reasonForLiteral[var].get()->empty()){
                                    {
                                        int it = starter.getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[var]=shared_reason;
                                }else{
                                }
                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                                return;
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
        }
        }
