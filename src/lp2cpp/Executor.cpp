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
const std::string _aggr_set0 = "aggr_set0";
const std::string _aux0 = "aux0";
const std::string _factor = "factor";
const std::string _has = "has";
const std::string _pen = "pen";
const std::string _remain = "remain";
const std::string _stat = "stat";
const std::string _td = "td";
const std::string _tot_penalty = "tot_penalty";
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
AuxMap<0> ptd_({});
AuxMap<0> utd_({});
AuxMap<0> ftd_({});
AuxMap<32> pfactor_0_({0});
AuxMap<32> ufactor_0_({0});
AuxMap<32> ffactor_0_({0});
AuxMap<96> paux0_0_1_2_({0,1,2});
AuxMap<96> uaux0_0_1_2_({0,1,2});
AuxMap<96> faux0_0_1_2_({0,1,2});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<96> paux0_1_2_3_({1,2,3});
AuxMap<96> uaux0_1_2_3_({1,2,3});
AuxMap<96> faux0_1_2_3_({1,2,3});
AuxMap<0> pfactor_({});
AuxMap<0> ufactor_({});
AuxMap<0> ffactor_({});
AuxMap<64> paux0_0_1_({0,1});
AuxMap<64> uaux0_0_1_({0,1});
AuxMap<64> faux0_0_1_({0,1});
AuxMap<32> ptd_0_({0});
AuxMap<32> utd_0_({0});
AuxMap<32> ftd_0_({0});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<0> premain_({});
AuxMap<0> uremain_({});
AuxMap<0> fremain_({});
AuxMap<0> ppen_({});
AuxMap<0> upen_({});
AuxMap<0> fpen_({});
AuxMap<0> pstat_({});
AuxMap<0> ustat_({});
AuxMap<0> fstat_({});
AuxMap<0> phas_({});
AuxMap<0> uhas_({});
AuxMap<0> fhas_({});
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
    if(insertResult.first->getPredicateName() == &_stat){
        fstat_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_remain){
        fremain_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_has){
        fhas_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2(*insertResult.first);
        faux0_0_1_.insert2(*insertResult.first);
        faux0_0_1_2_.insert2(*insertResult.first);
        faux0_1_2_3_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_factor){
        ffactor_.insert2(*insertResult.first);
        ffactor_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pen){
        fpen_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_td){
        ftd_.insert2(*insertResult.first);
        ftd_0_.insert2(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_stat){
        pstat_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_remain){
        premain_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_has){
        phas_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2(*insertResult.first);
        paux0_0_1_.insert2(*insertResult.first);
        paux0_0_1_2_.insert2(*insertResult.first);
        paux0_1_2_3_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_factor){
        pfactor_.insert2(*insertResult.first);
        pfactor_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pen){
        ppen_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_td){
        ptd_.insert2(*insertResult.first);
        ptd_0_.insert2(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_stat){
        ustat_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_remain){
        uremain_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_has){
        uhas_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2(*insertResult.first);
        uaux0_0_1_.insert2(*insertResult.first);
        uaux0_0_1_2_.insert2(*insertResult.first);
        uaux0_1_2_3_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_factor){
        ufactor_.insert2(*insertResult.first);
        ufactor_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pen){
        upen_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_td){
        utd_.insert2(*insertResult.first);
        utd_0_.insert2(*insertResult.first);
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
        const std::vector<int>* tuples = &ptd_.getValues({});
        const std::vector<int>* tuplesU = &utd_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int J = tuple->at(0);
            int T = tuple->at(1);
            int N = tuple->at(2);
            const std::vector<int>* tuples = &pfactor_0_.getValues({J});
            const std::vector<int>* tuplesU = &ufactor_0_.getValues({J});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(tuple->at(0) == J){
                    int I = tuple->at(1);
                    Tuple* aux = factory.addNewInternalTuple({I,J,N,T}, &_aux0);
                    const auto& insertResult = aux->setStatus(Undef);
                    if (insertResult.second) {
                        factory.removeFromCollisionsList(aux->getId());
                        insertUndef(insertResult);
                        {
                            Tuple* head = factory.addNewInternalTuple({I,J,N},&_aggr_set0);
                            const auto& headInsertResult = head->setStatus(Undef);
                            if (headInsertResult.second) {
                                factory.removeFromCollisionsList(head->getId());
                                insertUndef(headInsertResult);
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &premain_.getValues({});
        const std::vector<int>* tuplesU = &uremain_.getValues({});
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
    paggr_id0_.clear();
    paggr_set0_.clear();
    faggr_id0_.clear();
    faggr_set0_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    stringToUniqueStringPointer["factor"] = &_factor;
    stringToUniqueStringPointer["has"] = &_has;
    stringToUniqueStringPointer["pen"] = &_pen;
    stringToUniqueStringPointer["remain"] = &_remain;
    stringToUniqueStringPointer["stat"] = &_stat;
    stringToUniqueStringPointer["td"] = &_td;
    stringToUniqueStringPointer["tot_penalty"] = &_tot_penalty;
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
    {
        std::set<std::vector<int>> trueHeads;
        const std::vector<int>* tuples = &ppen_.getValues({});
        for(unsigned i=0; i<tuples->size();i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int P = currentTuple->at(0);
            std::set<std::vector<int>> aggrSetKey;
            int aggregateValue=0;
            const std::vector<int>* tuples = &ptd_.getValues({});
            for(unsigned i=0; i<tuples->size() && aggregateValue < P;i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int J = currentTuple->at(0);
                int T = currentTuple->at(1);
                int N = currentTuple->at(2);
                const std::vector<int>* tuples = &pfactor_0_.getValues({J});
                for(unsigned i=0; i<tuples->size() && aggregateValue < P;i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int I = currentTuple->at(1);
                    std::vector<int> aggrKey({I,J,N});
                    if(aggrSetKey.count(aggrKey)==0){
                        aggrSetKey.insert(aggrKey);
                        aggregateValue+=aggrKey[0];
                    }
                }
            }
            if(aggregateValue >= P){
                std::vector<int> head({P});
                std::cout<<"has("<<head[0]<<")"<<std::endl;
                Tuple* tupleHead = factory.addNewInternalTuple(head,&_has);
                const auto& insertResult = tupleHead->setStatus(True);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(tupleHead->getId());
                    insertTrue(insertResult);
                }
            }
        }
    }
    {
        std::set<std::vector<int>> trueHeads;
        const std::vector<int>* tuples = &pstat_.getValues({});
        for(unsigned i=0; i<tuples->size();i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int Q = currentTuple->at(0);
            const std::vector<int>* tuples = &phas_.getValues({});
            for(unsigned i=0; i<tuples->size();i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int P = currentTuple->at(0);
                int W = P + Q;
                int P1 = P + 1;
                Tuple* boundTuple = factory.find({P1},&_has);
                if(boundTuple == NULL or boundTuple->isFalse()){
                    std::vector<int> head({W});
                    std::cout<<"tot_penalty("<<head[0]<<")"<<std::endl;
                }
            }
        }
    }
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
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < P+1-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= P+1-posSum+currentJoinTuple->at(0)) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reas->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reas->insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= P+1){
                    propagatedLiterals.push_back(1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= P+1-currentJoinTuple->at(0)){
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                                VectorAsSet<int>* reas = &reasonForLiteral[-itProp];
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i);
                                        reason.push_back(it);
                                        reas->insert(it);
                                    }
                                    int it = tuplesF->at(i);
                                    reason.push_back(-it);
                                    reas->insert(-it);
                                }else{
                                    for(int reasonLit : reason)
                                        reas->insert(reasonLit);
                                }
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= P+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reas->insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < P+1 - posSum){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        VectorAsSet<int>* reas = &reasonForLiteral[-itProp];
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reas->insert(-it);
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
                const std::vector<int>* tuples = &premain_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uremain_.getValues({});
                else if(tupleU->getPredicateName() == &_remain && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({P},&_aggr_id0);
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
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &ptd_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &utd_.getValues({});
                else if(tupleU->getPredicateName() == &_td && !tupleUNegated)
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
                        int J = tuple0->at(0);
                        int T = tuple0->at(1);
                        int N = tuple0->at(2);
                        const std::vector<int>* tuples = &pfactor_0_.getValues({J});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ufactor_0_.getValues({J});
                        else if(tupleU->getPredicateName() == &_factor && !tupleUNegated)
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
                            const Tuple* tuple1 = NULL;
                            if(i<tuples->size())
                                tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == J)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int I = tuple1->at(1);
                                Tuple negativeTuple({I,J,N,T},&_aux0);
                                const Tuple* tuple2 = factory.find(negativeTuple);
                                if(tuple2 == NULL)
                                    tuple2 = &negativeTuple;
                                else{
                                    if(tuple2->isTrue())
                                        tuple2 = NULL;
                                    else if(tuple2->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple2;
                                            tupleUNegated=true;
                                        }else{
                                            if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
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
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &paux0_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_.getValues({});
                else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
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
                        int I = tuple0->at(0);
                        int J = tuple0->at(1);
                        int N = tuple0->at(2);
                        int T = tuple0->at(3);
                        Tuple negativeTuple({J,I},&_factor);
                        const Tuple* tuple1 = factory.find(negativeTuple);
                        if(tuple1 == NULL)
                            tuple1 = &negativeTuple;
                        else{
                            if(tuple1->isTrue())
                                tuple1 = NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=true;
                                }else{
                                    if(tupleU->getPredicateName() != &_factor || !tupleUNegated || !(*tupleU == *tuple1))
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
                const std::vector<int>* tuples = &paux0_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_.getValues({});
                else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
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
                        int I = tuple0->at(0);
                        int J = tuple0->at(1);
                        int N = tuple0->at(2);
                        int T = tuple0->at(3);
                        Tuple negativeTuple({J,T,N},&_td);
                        const Tuple* tuple1 = factory.find(negativeTuple);
                        if(tuple1 == NULL)
                            tuple1 = &negativeTuple;
                        else{
                            if(tuple1->isTrue())
                                tuple1 = NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=true;
                                }else{
                                    if(tupleU->getPredicateName() != &_td || !tupleUNegated || !(*tupleU == *tuple1))
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
            const std::vector<int>* trueHeads = &paggr_set0_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
                int I = head->at(0);
                int J = head->at(1);
                int N = head->at(2);
                const std::vector<int>* tuples = &paux0_0_1_2_.getValues({I,J,N});
                const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
                if(tuples->size() == 0){
                    if(tuplesU->size() == 0){
                        propagatedLiterals.push_back(1);
                    }else if(tuplesU->size() == 1){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                }
            }
            const std::vector<int>* undefHeads = &uaggr_set0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
                int I = head->at(0);
                int J = head->at(1);
                int N = head->at(2);
                const std::vector<int>* tuples = &paux0_0_1_2_.getValues({I,J,N});
                if(tuples->size() == 0){
                    const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
                    if(tuplesU->size() == 0){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* falseHeads = &faggr_set0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
                int I = head->at(0);
                int J = head->at(1);
                int N = head->at(2);
                const std::vector<int>* tuples = &paux0_0_1_2_.getValues({I,J,N});
                if(tuples->size() == 0){
                    const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
                    for(unsigned j = 0; j < tuplesU->size();){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(j)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    propagatedLiterals.push_back(1);
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
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            const std::vector<int>* tuples = &paux0_0_1_2_.getValues({I,J,N});
            const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
            if(startVar > 0){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<int>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
                    VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reas->insert(-it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));
                    int itProp = tuplesU->at(0);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
                        VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            reas->insert(-it);
                        }
                        reas->insert(startVar);
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                if(tuples->size()>0){
                    int it = tuples->at(0);
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        int it = tuplesU->back();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux0){
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            if(startVar > 0){
                Tuple* head = factory.find({I,J,N}, &_aggr_set0);
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
                Tuple* head = factory.find({I,J,N}, &_aggr_set0);
                const std::vector<int>* tuples = &paux0_0_1_2_.getValues({I,J,N});
                const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
                if(head != NULL && head->isTrue()){
                    if(tuples->size()==0 && tuplesU->size()==0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
                        VectorAsSet<int>* reas = &reasonForLiteral[-itHead];
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reas->insert(-it);
                        }
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
                            VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                reas->insert(-it);
                            }
                            int it = head->getId();
                            reas->insert(it);
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else{
                    if(head != NULL && head->isUndef() && tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        if(reasonForLiteral.count(-itHead) == 0  || reasonForLiteral[-itHead].empty()){
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
                            VectorAsSet<int>* reas = &reasonForLiteral[-itHead];
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                reas->insert(-it);
                            }
                        }
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_td && startVar < 0){
                int J = starter[0];
                int T = starter[1];
                int N = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &paux0_1_2_3_.getValues({J,N,T});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_1_2_3_.getValues({J,N,T});
                else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
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
                    const Tuple* tuple1 = NULL;
                    if(i<tuples->size())
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == J && tupleU->at(2) == N && tupleU->at(3) == T)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int I = tuple1->at(0);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                VectorAsSet<int>* reas = &reasonForLiteral[var];
                                {
                                    int it = starter.getId();
                                    reas->insert(it*-1);
                                }
                                if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reas->insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else{
                            VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reas->insert(it*1);
                            }
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                int I = starter[0];
                int J = starter[1];
                int N = starter[2];
                int T = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({J,T,N},&_td);
                const Tuple* tuple1 = factory.find(negativeTuple);
                if(tuple1 == NULL)
                    tuple1 = &negativeTuple;
                else{
                    if(tuple1->isTrue())
                        tuple1 = NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=true;
                        }else{
                            if(tupleU->getPredicateName() != &_td || !tupleUNegated || !(*tupleU == *tuple1))
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
                            VectorAsSet<int>* reas = &reasonForLiteral[var];
                            {
                                int it = starter.getId();
                                reas->insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reas->insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reas->insert(it*-1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_factor && startVar < 0){
                int J = starter[0];
                int I = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &paux0_0_1_.getValues({I,J});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_0_1_.getValues({I,J});
                else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
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
                    const Tuple* tuple1 = NULL;
                    if(i<tuples->size())
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == I && tupleU->at(1) == J)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int N = tuple1->at(2);
                        int T = tuple1->at(3);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                VectorAsSet<int>* reas = &reasonForLiteral[var];
                                {
                                    int it = starter.getId();
                                    reas->insert(it*-1);
                                }
                                if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reas->insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else{
                            VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reas->insert(it*1);
                            }
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                int I = starter[0];
                int J = starter[1];
                int N = starter[2];
                int T = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({J,I},&_factor);
                const Tuple* tuple1 = factory.find(negativeTuple);
                if(tuple1 == NULL)
                    tuple1 = &negativeTuple;
                else{
                    if(tuple1->isTrue())
                        tuple1 = NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=true;
                        }else{
                            if(tupleU->getPredicateName() != &_factor || !tupleUNegated || !(*tupleU == *tuple1))
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
                            VectorAsSet<int>* reas = &reasonForLiteral[var];
                            {
                                int it = starter.getId();
                                reas->insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reas->insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reas->insert(it*-1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aux0 && startVar < 0){
                int I = starter[0];
                int J = starter[1];
                int N = starter[2];
                int T = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({J,T,N},&_td);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_td || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({J,I},&_factor);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_factor || tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                VectorAsSet<int>* reas = &reasonForLiteral[var];
                                {
                                    int it = starter.getId();
                                    reas->insert(it*-1);
                                }
                                if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reas->insert(it*1);
                                }
                                if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reas->insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else{
                            VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reas->insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reas->insert(it*1);
                            }
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_factor && startVar > 0){
                int J = starter[0];
                int I = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &ptd_0_.getValues({J});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &utd_0_.getValues({J});
                else if(tupleU->getPredicateName() == &_td && !tupleUNegated)
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
                    const Tuple* tuple1 = NULL;
                    if(i<tuples->size())
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == J)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T = tuple1->at(1);
                        int N = tuple1->at(2);
                        Tuple negativeTuple({I,J,N,T},&_aux0);
                        const Tuple* tuple2 = factory.find(negativeTuple);
                        if(tuple2 == NULL)
                            tuple2 = &negativeTuple;
                        else{
                            if(tuple2->isTrue())
                                tuple2 = NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=true;
                                }else{
                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                    VectorAsSet<int>* reas = &reasonForLiteral[var];
                                    {
                                        int it = starter.getId();
                                        reas->insert(it*1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reas->insert(it*1);
                                    }
                                    if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reas->insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else{
                                VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reas->insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reas->insert(it*-1);
                                }
                                handleConflict(-startVar, propagatedLiterals);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_td && startVar > 0){
                int J = starter[0];
                int T = starter[1];
                int N = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &pfactor_0_.getValues({J});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ufactor_0_.getValues({J});
                else if(tupleU->getPredicateName() == &_factor && !tupleUNegated)
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
                    const Tuple* tuple1 = NULL;
                    if(i<tuples->size())
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == J)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int I = tuple1->at(1);
                        Tuple negativeTuple({I,J,N,T},&_aux0);
                        const Tuple* tuple2 = factory.find(negativeTuple);
                        if(tuple2 == NULL)
                            tuple2 = &negativeTuple;
                        else{
                            if(tuple2->isTrue())
                                tuple2 = NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=true;
                                }else{
                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                    VectorAsSet<int>* reas = &reasonForLiteral[var];
                                    {
                                        int it = starter.getId();
                                        reas->insert(it*1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reas->insert(it*1);
                                    }
                                    if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reas->insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else{
                                VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reas->insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reas->insert(it*-1);
                                }
                                handleConflict(-startVar, propagatedLiterals);
                                return;
                            }
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            int P = starter[0];
            std::vector<int> sharedVar({});
            const std::vector<int>* tuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<int>* tuplesU = &uaggr_set0_.getValues(sharedVar);
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=P+1){
                    VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reas->insert(it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else{
                    std::vector<int> reason;
                    for(int index=0; index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actSum >= P+1-currentTuple->at(0)){
                            int itProp =currentTuple->getId();
                            if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].empty()){
                                VectorAsSet<int>* reas = &reasonForLiteral[-itProp];
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        int it = tuples->at(i);
                                        reason.push_back(it);
                                        reas->insert(it);
                                    }
                                    reason.push_back(startVar);
                                    reas->insert(startVar);
                                }else{
                                    for(int reasonLit : reason)
                                        reas->insert(reasonLit);
                                }
                            }
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }else{
                int& actSum = actualSum[uStartVar];
                int& posSum = possibleSum[uStartVar];
                if(actSum+posSum < P+1){
                    const std::vector<int>* tuplesF = &faggr_set0_.getValues(sharedVar);
                    VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reas->insert(-it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actSum < P+1-posSum+currentTuple->at(0)){
                            int itProp = tuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                                const std::vector<int>* tuplesF = &faggr_set0_.getValues(sharedVar);
                                VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    reas->insert(-it);
                                }
                                reas->insert(startVar);
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
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < P+1-posSum){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                    VectorAsSet<int>* reas = &reasonForLiteral[-itProp];
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reas->insert(-it);
                    }
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= P+1-posSum+currentJoinTuple->at(0)) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reas->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reas->insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= P+1){
                    int itProp = tuplesF->at(i);
                    VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reas->insert(it);
                    }
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actSum >= P+1-currentJoinTuple->at(0)){
                            if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                                VectorAsSet<int>* reas = &reasonForLiteral[-itProp];
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i);
                                        reason.push_back(it);
                                        reas->insert(it);
                                    }
                                    int it = tuplesF->at(i);
                                    reason.push_back(-it);
                                    reas->insert(-it);
                                }else{
                                    for(int reasonLit : reason)
                                        reas->insert(reasonLit);
                                }
                            }
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::vector<int>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= P+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        VectorAsSet<int>* reas = &reasonForLiteral[itProp];
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reas->insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < P+1 - posSum){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        VectorAsSet<int>* reas = &reasonForLiteral[-itProp];
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reas->insert(-it);
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
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({P},&_remain);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_remain || tupleUNegated || !(*tupleU == *tuple1))
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
                            VectorAsSet<int>* reas = &reasonForLiteral[var];
                            {
                                int it = starter.getId();
                                reas->insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reas->insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reas->insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_remain && startVar > 0){
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({P},&_aggr_id0);
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
                            VectorAsSet<int>* reas = &reasonForLiteral[var];
                            {
                                int it = starter.getId();
                                reas->insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reas->insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else{
                        VectorAsSet<int>* reas = &reasonForLiteral[-startVar];
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reas->insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
        }
    }
    if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
}
}
