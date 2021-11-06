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
const std::set<int,std::greater<int>> EMPTY_TUPLES_SET;
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
        auto itReason = reasonForLiteral.find(lit);
        VectorAsSet<int>* currentReas = itReason != reasonForLiteral.end() ? itReason->second.get() : NULL;
        unsigned currentReasonSize= itReason != reasonForLiteral.end() ? currentReas->size() : 0;
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
    if(insertResult.first->getPredicateName() == &_stat){
        fstat_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_remain){
        fremain_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_has){
        fhas_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2Vec(*insertResult.first);
        faux0_0_1_.insert2Vec(*insertResult.first);
        faux0_0_1_2_.insert2Vec(*insertResult.first);
        faux0_1_2_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_factor){
        ffactor_.insert2Vec(*insertResult.first);
        ffactor_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pen){
        fpen_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_td){
        ftd_.insert2Vec(*insertResult.first);
        ftd_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_stat){
        pstat_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_remain){
        premain_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_has){
        phas_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2Vec(*insertResult.first);
        paux0_0_1_.insert2Vec(*insertResult.first);
        paux0_0_1_2_.insert2Vec(*insertResult.first);
        paux0_1_2_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_factor){
        pfactor_.insert2Vec(*insertResult.first);
        pfactor_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pen){
        ppen_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_td){
        ptd_.insert2Vec(*insertResult.first);
        ptd_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_stat){
        ustat_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_remain){
        uremain_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_has){
        uhas_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2Vec(*insertResult.first);
        uaux0_0_1_.insert2Vec(*insertResult.first);
        uaux0_0_1_2_.insert2Vec(*insertResult.first);
        uaux0_1_2_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_factor){
        ufactor_.insert2Vec(*insertResult.first);
        ufactor_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pen){
        upen_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_td){
        utd_.insert2Vec(*insertResult.first);
        utd_0_.insert2Vec(*insertResult.first);
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
    auto reas = reasonForLiteral.find(internalVar);
    if(reas!=reasonForLiteral.end())reas->second.get()->clear();
    std::string minus = var < 0 ? "-" : "";
    const auto& insertResult = tuple->setStatus(Undef);
    if (insertResult.second) {
        factory.removeFromCollisionsList(tuple->getId());
        insertUndef(insertResult);
    }
    if(currentDecisionLevel >= 0){
    }
}
bool compTuple(const int& l1,const int& l2){
    Tuple* first = factory.getTupleFromInternalID(l1);
    unsigned firstAggrVarIndex = factory.getIndexForAggrSet(first->getPredicateName());
    int w = first->at(firstAggrVarIndex)-factory.getTupleFromInternalID(l2)->at(firstAggrVarIndex);
    return w==0 ? l1 > l2 : w > 0;
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {
        const std::vector<int>* tuples = &ptd_.getValuesVec({});
        const std::vector<int>* tuplesU = &utd_.getValuesVec({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int J = tuple->at(0);
            int T = tuple->at(1);
            int N = tuple->at(2);
            const std::vector<int>* tuples = &pfactor_0_.getValuesVec({J});
            const std::vector<int>* tuplesU = &ufactor_0_.getValuesVec({J});
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
        const std::vector<int>* tuples = &premain_.getValuesVec({});
        const std::vector<int>* tuplesU = &uremain_.getValuesVec({});
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
            const std::set<int,std::greater<int>>* aggrSetTuples = &uaggr_set0_.getValuesSet({});
            int& possSum = possibleSum[it];
            for(auto itUndef=aggrSetTuples->begin(); itUndef!=aggrSetTuples->end(); itUndef++){
                possSum+=factory.getTupleFromInternalID(*itUndef)->at(0);
            }
        }
    }
    std::vector<int> ordered_ids;
    std::vector<int> tuplesIdOrdered;
    std::map<int, Tuple*> idToTuples;
    int currentIdIndex=0;
    {
        std::cout<<"Ordering"<<std::endl;
        const std::set<int,greater<int>> tuples = uaggr_set0_.getValuesSet({});
        ordered_ids.reserve(tuples.size());
        tuplesIdOrdered.reserve(tuples.size());
        for(int id :tuples){
            tuplesIdOrdered.push_back(id);
            ordered_ids.push_back(id);
            idToTuples[id]=factory.getTupleFromInternalID(id);
            factory.removeFromCollisionsList(id);
            idToTuples[id]->setStatus(UNKNOWN);
        }
        std::stable_sort(tuplesIdOrdered.begin(),tuplesIdOrdered.end(),compTuple);
        for(int id: tuplesIdOrdered){
            Tuple* t=idToTuples[id];
            factory.setId(t,ordered_ids[currentIdIndex++]);
            const auto& insertResult = t->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(t->getId());
                insertUndef(insertResult);
            }
        }
        ordered_ids.clear();
        tuplesIdOrdered.clear();
        idToTuples.clear();
        currentIdIndex=0;
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
    factory.setIndexForAggregateSet(0,&_aggr_set0);
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
                    if(tupleU->getPredicateName() == &_aggr_set0){
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
    {
        std::set<std::vector<int>> trueHeads;
        const std::vector<int>* tuples = &ppen_.getValuesVec({});
        for(unsigned i=0; i<tuples->size();i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int P = currentTuple->at(0);
            std::set<std::vector<int>> aggrSetKey;
            int aggregateValue=0;
            const std::vector<int>* tuples = &ptd_.getValuesVec({});
            for(unsigned i=0; i<tuples->size() && aggregateValue < P;i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int J = currentTuple->at(0);
                int T = currentTuple->at(1);
                int N = currentTuple->at(2);
                const std::vector<int>* tuples = &pfactor_0_.getValuesVec({J});
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
        const std::vector<int>* tuples = &pstat_.getValuesVec({});
        for(unsigned i=0; i<tuples->size();i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int Q = currentTuple->at(0);
            const std::vector<int>* tuples = &phas_.getValuesVec({});
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
            if(tuple->getPredicateName() == &_aggr_set0){
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
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::set<int,std::greater<int>>* joinTuples = &paggr_set0_.getValuesSet(sharedVar);
                const std::set<int,std::greater<int>>* joinTuplesU = &uaggr_set0_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < P+1-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= P+1-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const std::set<int,std::greater<int>>* joinTuplesF = &faggr_set0_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::set<int,std::greater<int>>* joinTuples = &paggr_set0_.getValuesSet(sharedVar);
                const std::set<int,std::greater<int>>* joinTuplesU = &uaggr_set0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= P+1){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < P+1-currentJoinTuple->at(0))break;
                            if(shared_reason.get()->empty()){
                                for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(it);
                                }
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                    int P = currentTuple->at(0);
                    std::vector<int> sharedVar({});
                    const std::set<int,std::greater<int>>* joinTuples = &paggr_set0_.getValuesSet(sharedVar);
                    const std::set<int,std::greater<int>>* joinTuplesU = &uaggr_set0_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesU->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum >= P+1){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else if(actSum < P+1 - posSum){
                        int itProp = tuplesU->at(i);
                        const std::set<int,std::greater<int>>* joinTuplesF = &faggr_set0_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
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
                    const std::vector<int>* tuples = &premain_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uremain_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_remain && !tupleUNegated)
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
                                    if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
                    const std::vector<int>* tuples = &ptd_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &utd_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_td && !tupleUNegated)
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
                            int J = tuple0->at(0);
                            int T = tuple0->at(1);
                            int N = tuple0->at(2);
                            const std::vector<int>* tuples = &pfactor_0_.getValuesVec({J});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ufactor_0_.getValuesVec({J});
                            else if(tupleU->getPredicateName() == &_factor && !tupleUNegated)
                                undeRepeated.push_back(tupleU);
                            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                                            if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                            else internalProps.push_back({tupleU,tupleUNegated});
                                        }else{
                                            propagatedLiterals.push_back(1);
                                        }
                                    }
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
                    const std::vector<int>* tuples = &paux0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
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
                                    if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
                    const std::vector<int>* tuples = &paux0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
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
                                    if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
                const std::set<int,std::greater<int>>* trueHeads = &paggr_set0_.getValuesSet({});
                for(auto itTrueHead = trueHeads->begin();itTrueHead != trueHeads->end(); itTrueHead++){
                    const Tuple* currentHead = factory.getTupleFromInternalID(*itTrueHead);
                    int I = currentHead->at(0);
                    int J = currentHead->at(1);
                    int N = currentHead->at(2);
                    const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({I, J, N});
                    const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({I, J, N});
                    if(tuples->size()==0){
                        if(tuplesU->size() == 0){
                            propagatedLiterals.push_back(1);
                            return;
                        }else if(tuplesU->size()==1){
                            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }
                const std::set<int,std::greater<int>>* falseHeads = &faggr_set0_.getValuesSet({});
                for(auto itFalseHead = falseHeads->begin();itFalseHead != falseHeads->end(); itFalseHead++){
                    const Tuple* currentHead = factory.getTupleFromInternalID(*itFalseHead);
                    int I = currentHead->at(0);
                    int J = currentHead->at(1);
                    int N = currentHead->at(2);
                    const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({I, J, N});
                    const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({I, J, N});
                    if(tuples->size()>0){
                        propagatedLiterals.push_back(1);
                        return;
                    }else{
                    while(!tuplesU->empty()){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const std::set<int,std::greater<int>>* undefHeads = &uaggr_set0_.getValuesSet({});
            std::vector<std::pair<const Tuple*,bool>> props0;
            for(auto itUndefHead = undefHeads->begin(); itUndefHead != undefHeads->end(); itUndefHead++){
                const Tuple* currentHead = factory.getTupleFromInternalID(*itUndefHead);
                int I = currentHead->at(0);
                int J = currentHead->at(1);
                int N = currentHead->at(2);
                const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({I, J, N});
                const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({I, J, N});
                if(tuples->size() > 0)
                    props0.push_back({currentHead,false});
                else if(tuplesU->size()==0)
                    props0.push_back({currentHead,true});
            }
            for(auto pair : props0)
                propUndefined(pair.first,false,propagationStack,pair.second,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aux0){
            int I = starter.at(0);
            int J = starter.at(1);
            int N = starter.at(2);
            int T = starter.at(3);
            Tuple* head = factory.find({I,J,N}, &_aggr_set0);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar>0){
                if(head == NULL || (!head->isTrue() && !head->isUndef())){
                    int it = head->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[it]=shared_reason;
                    handleConflict(it, propagatedLiterals);
                    return;
                }else if(head !=NULL && head->isUndef()){
                    int it = head->getId();
                    shared_reason.get()->insert(startVar);
                    auto itReason = reasonForLiteral.emplace(it,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({I, J, N});
                const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({I, J, N});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({I, J, N});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({I, J, N});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int it = head->getId();
                        shared_reason.get()->insert(it);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else if( head != NULL && head->isUndef() ){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({I, J, N});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itHead,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }else if(starter.getPredicateName() == &_aggr_set0){
            int I = starter.at(0);
            int J = starter.at(1);
            int N = starter.at(2);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({I,J,N});
            const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({I,J,N});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({I,J,N});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }else if(tuplesU->size()==1){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));
                        int itProp = currentTuple->getId();
                        const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({I,J,N});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        shared_reason.get()->insert(startVar);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()>0){
                    int it = tuples->at(0);
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[-it]=shared_reason;
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                shared_reason.get()->insert(startVar);
                while(!tuplesU->empty()){
                    int it = tuplesU->back();
                    auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(factory.getTupleFromInternalID(it),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
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
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &paux0_1_2_3_.getValuesVec({J,N,T});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux0_1_2_3_.getValuesVec({J,N,T});
            else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
                undeRepeated.push_back(tupleU);
            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        {
                            int it = starter.getId();
                            shared_reason.get()->insert(it*-1);
                        }
                        if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
            }
            for(auto pair : internalProps)
                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
        if(starter.getPredicateName() == &_aux0 && startVar > 0){
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    {
                        int it = starter.getId();
                        shared_reason.get()->insert(it*1);
                    }
                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                        int it = tuple1->getId();
                        shared_reason.get()->insert(it*-1);
                    }
                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    else internalProps.push_back({tupleU,tupleUNegated});
                }else{
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(tuple1!=NULL){
                        int it = tuple1->getId();
                        shared_reason.get()->insert(it*-1);
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
    {
        if(starter.getPredicateName() == &_factor && startVar < 0){
            int J = starter[0];
            int I = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({I,J});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux0_0_1_.getValuesVec({I,J});
            else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
                undeRepeated.push_back(tupleU);
            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        {
                            int it = starter.getId();
                            shared_reason.get()->insert(it*-1);
                        }
                        if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
            }
            for(auto pair : internalProps)
                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
        if(starter.getPredicateName() == &_aux0 && startVar > 0){
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    {
                        int it = starter.getId();
                        shared_reason.get()->insert(it*1);
                    }
                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                        int it = tuple1->getId();
                        shared_reason.get()->insert(it*-1);
                    }
                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    else internalProps.push_back({tupleU,tupleUNegated});
                }else{
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(tuple1!=NULL){
                        int it = tuple1->getId();
                        shared_reason.get()->insert(it*-1);
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
    {
        if(starter.getPredicateName() == &_aux0 && startVar < 0){
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        {
                            int it = starter.getId();
                            shared_reason.get()->insert(it*-1);
                        }
                        if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                            int it = tuple2->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        if(tuple2!=NULL){
                            int it = tuple2->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
            for(auto pair : internalProps)
                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
        if(starter.getPredicateName() == &_factor && startVar > 0){
            int J = starter[0];
            int I = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &ptd_0_.getValuesVec({J});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &utd_0_.getValuesVec({J});
            else if(tupleU->getPredicateName() == &_td && !tupleUNegated)
                undeRepeated.push_back(tupleU);
            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            {
                                int it = starter.getId();
                                shared_reason.get()->insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }
                    }
                }
            }
            for(auto pair : internalProps)
                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
        if(starter.getPredicateName() == &_td && startVar > 0){
            int J = starter[0];
            int T = starter[1];
            int N = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &pfactor_0_.getValuesVec({J});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &ufactor_0_.getValuesVec({J});
            else if(tupleU->getPredicateName() == &_factor && !tupleUNegated)
                undeRepeated.push_back(tupleU);
            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                if(tuplesU!=&EMPTY_TUPLES_VEC)
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
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            {
                                int it = starter.getId();
                                shared_reason.get()->insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                            return;
                        }
                    }
                }
            }
            for(auto pair : internalProps)
                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
    }
    if(starter.getPredicateName() == &_aggr_id0){
        int P = starter[0];
        std::vector<int> sharedVar({});
        const std::set<int,std::greater<int>>* tuples = &paggr_set0_.getValuesSet(sharedVar);
        const std::set<int,std::greater<int>>* tuplesU = &uaggr_set0_.getValuesSet(sharedVar);
        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
        if(startVar < 0){
            int& actSum = actualSum[uStartVar];
            if(actSum>=P+1){
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
                while(!tuplesU->empty()){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                    if(actSum >= P+1-currentTuple->at(0)){
                        int itProp =currentTuple->getId();
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else break;
                }
            }
        }else{
            int& actSum = actualSum[uStartVar];
            int& posSum = possibleSum[uStartVar];
            if(actSum+posSum < P+1){
                const std::set<int,std::greater<int>>* tuplesF = &faggr_set0_.getValuesSet(sharedVar);
                for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                    int it = *i;
                    shared_reason.get()->insert(-it);
                }
                reasonForLiteral[-startVar]=shared_reason;
                handleConflict(-startVar, propagatedLiterals);
                return;
            }else{
                while(!tuplesU->empty()){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                    if(actSum < P+1-posSum+currentTuple->at(0)){
                        int itProp = *tuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const std::set<int,std::greater<int>>* tuplesF = &faggr_set0_.getValuesSet(sharedVar);
                            for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            shared_reason.get()->insert(startVar);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else break;
                }
            }
        }
    }//close aggr id starter
    if(starter.getPredicateName() == &_aggr_set0){
        const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
        const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
        for(unsigned i = 0; i<tuples->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int P = currentTuple->at(0);
            std::vector<int> sharedVar({});
            const std::set<int,std::greater<int>>* joinTuples = &paggr_set0_.getValuesSet(sharedVar);
            const std::set<int,std::greater<int>>* joinTuplesU = &uaggr_set0_.getValuesSet(sharedVar);
            int aggrIdIt=tuples->at(i);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            int& actSum = actualSum[aggrIdIt];
            int& posSum = possibleSum[aggrIdIt];
            if(actSum < P+1-posSum){
                int itProp = tuples->at(i);
                const std::set<int,std::greater<int>>* joinTuplesF = &faggr_set0_.getValuesSet(sharedVar);
                for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                    int it = *j;
                    shared_reason.get()->insert(-it);
                }
                reasonForLiteral[-itProp]=shared_reason;
                handleConflict(-itProp, propagatedLiterals);
                return;
            }else{
                while(!joinTuplesU->empty()){
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                    if(actSum >= P+1-posSum+currentJoinTuple->at(0)) {break;}
                    int itProp = *joinTuplesU->begin();
                    if(shared_reason.get()->empty()){
                        const std::set<int,std::greater<int>>* joinTuplesF = &faggr_set0_.getValuesSet(sharedVar);
                        for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
            int P = currentTuple->at(0);
            std::vector<int> sharedVar({});
            const std::set<int,std::greater<int>>* joinTuples = &paggr_set0_.getValuesSet(sharedVar);
            const std::set<int,std::greater<int>>* joinTuplesU = &uaggr_set0_.getValuesSet(sharedVar);
            int aggrIdIt=tuplesF->at(i);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            int& actSum = actualSum[aggrIdIt];
            if(actSum >= P+1){
                int itProp = tuplesF->at(i);
                for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){
                    int it = *j;
                    shared_reason.get()->insert(it);
                }
                reasonForLiteral[itProp]=shared_reason;
                handleConflict(itProp, propagatedLiterals);
                return;
            }else{
                while(!joinTuplesU->empty()){
                    int itProp = *joinTuplesU->begin();
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                    if(actSum < P+1-currentJoinTuple->at(0))break;
                        if(shared_reason.get()->empty()){
                            for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int P = currentTuple->at(0);
                std::vector<int> sharedVar({});
                const std::set<int,std::greater<int>>* joinTuples = &paggr_set0_.getValuesSet(sharedVar);
                const std::set<int,std::greater<int>>* joinTuplesU = &uaggr_set0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= P+1){
                    int itProp = tuplesU->at(i);
                    for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < P+1 - posSum){
                    int itProp = tuplesU->at(i);
                    const std::set<int,std::greater<int>>* joinTuplesF = &faggr_set0_.getValuesSet(sharedVar);
                    for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(-it);
                    }
                    auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
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
                std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        {
                            int it = starter.getId();
                            shared_reason.get()->insert(it*1);
                        }
                        if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
            if(starter.getPredicateName() == &_remain && startVar > 0){
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
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
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        {
                            int it = starter.getId();
                            shared_reason.get()->insert(it*1);
                        }
                        if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
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
