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
const std::string _aggr_set0 = "aggr_set0";
const std::string _assign = "assign";
const std::string _aux1 = "aux1";
const std::string _aux_val0 = "aux_val0";
const std::string _body0 = "body0";
const std::string _component = "component";
const std::string _costs = "costs";
const std::string _user = "user";
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
AuxMap<0> paux_val0_({});
AuxMap<0> uaux_val0_({});
AuxMap<0> faux_val0_({});
AuxMap<0> puser_({});
AuxMap<0> uuser_({});
AuxMap<0> fuser_({});
AuxMap<0> pbody0_({});
AuxMap<0> ubody0_({});
AuxMap<0> fbody0_({});
AuxMap<0> passign_({});
AuxMap<0> uassign_({});
AuxMap<0> fassign_({});
AuxMap<32> pcomponent_0_({0});
AuxMap<32> ucomponent_0_({0});
AuxMap<32> fcomponent_0_({0});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<64> paggr_set0_1_2_({1,2});
AuxMap<64> uaggr_set0_1_2_({1,2});
AuxMap<64> faggr_set0_1_2_({1,2});
AuxMap<0> pcomponent_({});
AuxMap<0> ucomponent_({});
AuxMap<0> fcomponent_({});
AuxMap<64> paggr_set0_0_1_({0,1});
AuxMap<64> uaggr_set0_0_1_({0,1});
AuxMap<64> faggr_set0_0_1_({0,1});
AuxMap<32> passign_0_({0});
AuxMap<32> uassign_0_({0});
AuxMap<32> fassign_0_({0});
AuxMap<64> paux1_0_1_({0,1});
AuxMap<64> uaux1_0_1_({0,1});
AuxMap<64> faux1_0_1_({0,1});
AuxMap<0> paux1_({});
AuxMap<0> uaux1_({});
AuxMap<0> faux1_({});
AuxMap<32> paux1_0_({0});
AuxMap<32> uaux1_0_({0});
AuxMap<32> faux1_0_({0});
AuxMap<96> paux1_1_2_3_({1,2,3});
AuxMap<96> uaux1_1_2_3_({1,2,3});
AuxMap<96> faux1_1_2_3_({1,2,3});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<32> paggr_id0_1_({1});
AuxMap<32> uaggr_id0_1_({1});
AuxMap<32> faggr_id0_1_({1});
AuxMap<32> paggr_set0_2_({2});
AuxMap<32> uaggr_set0_2_({2});
AuxMap<32> faggr_set0_2_({2});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<32> paggr_id1_1_({1});
AuxMap<32> uaggr_id1_1_({1});
AuxMap<32> faggr_id1_1_({1});
AuxMap<0> pcosts_({});
AuxMap<0> ucosts_({});
AuxMap<0> fcosts_({});
AuxMap<32> pcosts_0_({0});
AuxMap<32> ucosts_0_({0});
AuxMap<32> fcosts_0_({0});
AuxMap<32> puser_0_({0});
AuxMap<32> uuser_0_({0});
AuxMap<32> fuser_0_({0});
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
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2Vec(*insertResult.first);
        faggr_id1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2Vec(*insertResult.first);
        faggr_id0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        faux1_.insert2Vec(*insertResult.first);
        faux1_0_.insert2Vec(*insertResult.first);
        faux1_0_1_.insert2Vec(*insertResult.first);
        faux1_1_2_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_costs){
        fcosts_.insert2Vec(*insertResult.first);
        fcosts_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2Set(*insertResult.first);
        faggr_set0_0_1_.insert2Set(*insertResult.first);
        faggr_set0_1_2_.insert2Set(*insertResult.first);
        faggr_set0_2_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_component){
        fcomponent_.insert2Vec(*insertResult.first);
        fcomponent_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        fassign_.insert2Vec(*insertResult.first);
        fassign_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        fbody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        fuser_.insert2Vec(*insertResult.first);
        fuser_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        faux_val0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2Vec(*insertResult.first);
        paggr_id1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2Vec(*insertResult.first);
        paggr_id0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        paux1_.insert2Vec(*insertResult.first);
        paux1_0_.insert2Vec(*insertResult.first);
        paux1_0_1_.insert2Vec(*insertResult.first);
        paux1_1_2_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_costs){
        pcosts_.insert2Vec(*insertResult.first);
        pcosts_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2Set(*insertResult.first);
        paggr_set0_0_1_.insert2Set(*insertResult.first);
        paggr_set0_1_2_.insert2Set(*insertResult.first);
        paggr_set0_2_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_component){
        pcomponent_.insert2Vec(*insertResult.first);
        pcomponent_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        passign_.insert2Vec(*insertResult.first);
        passign_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        pbody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        puser_.insert2Vec(*insertResult.first);
        puser_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        paux_val0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2Vec(*insertResult.first);
        uaggr_id1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2Vec(*insertResult.first);
        uaggr_id0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        uaux1_.insert2Vec(*insertResult.first);
        uaux1_0_.insert2Vec(*insertResult.first);
        uaux1_0_1_.insert2Vec(*insertResult.first);
        uaux1_1_2_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_costs){
        ucosts_.insert2Vec(*insertResult.first);
        ucosts_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2Set(*insertResult.first);
        uaggr_set0_0_1_.insert2Set(*insertResult.first);
        uaggr_set0_1_2_.insert2Set(*insertResult.first);
        uaggr_set0_2_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_component){
        ucomponent_.insert2Vec(*insertResult.first);
        ucomponent_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        uassign_.insert2Vec(*insertResult.first);
        uassign_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        ubody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        uuser_.insert2Vec(*insertResult.first);
        uuser_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        uaux_val0_.insert2Vec(*insertResult.first);
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
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    std::cout<<"MinConflict: "<<minConflict<<std::endl;
    std::cout<<"MinHeapSize: "<<minHeapSize<<std::endl;
    std::cout<<"MaxHeapSize: "<<maxHeapSize<<std::endl;
    std::cout<<"HeapSize: "<<heapSize<<std::endl;
    undefinedLoaded=true;
    std::map<std::vector<int>,std::unordered_set<int>> possibleValuesSetaux_val0;
    std::map<std::vector<int>,std::vector<int>> possibleValuesaux_val0;
    {
        const std::vector<int>* tuples = &passign_.getValuesVec({});
        const std::vector<int>* tuplesU = &uassign_.getValuesVec({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int C = tuple->at(0);
            int U = tuple->at(1);
            const std::vector<int>* tuples = &pcomponent_0_.getValuesVec({C});
            const std::vector<int>* tuplesU = &ucomponent_0_.getValuesVec({C});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(tuple->at(0) == C){
                    int P = tuple->at(1);
                    Tuple* aux = factory.addNewInternalTuple({P,C,U}, &_aggr_set0);
                    const auto& insertResult = aux->setStatus(Undef);
                    if (insertResult.second) {
                        {
                            std::vector<int> key({aux->at(2)});
                            std::vector<int>* possibleSums = &possibleValuesaux_val0[key];
                            std::unordered_set<int>* possibleSumsSet = &possibleValuesSetaux_val0[key];
                            if(possibleSums->empty()){
                                possibleSums->push_back(0);
                                Tuple* aux_val = factory.addNewInternalTuple({0},&_aux_val0);
                                const auto& insertResult = aux_val->setStatus(True);
                                if(insertResult.second){
                                    factory.removeFromCollisionsList(aux_val->getId());
                                    insertTrue(insertResult);
                                }
                            }
                            unsigned size = possibleSums->size();
                            for(unsigned i = 0; i<size; i++){
                                if(possibleSumsSet->count(possibleSums->at(i)+aux->at(0))==0){
                                    possibleSumsSet->insert(possibleSums->at(i)+aux->at(0));
                                    possibleSums->push_back(possibleSums->at(i)+aux->at(0));
                                    Tuple* aux_val = factory.addNewInternalTuple({possibleSums->back()},&_aux_val0);
                                    const auto& insertResult = aux_val->setStatus(True);
                                    if(insertResult.second){
                                        factory.removeFromCollisionsList(aux_val->getId());
                                        insertTrue(insertResult);
                                    }
                                }
                            }
                        }
                        factory.removeFromCollisionsList(aux->getId());
                        insertUndef(insertResult);
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &paux_val0_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaux_val0_.getValuesVec({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int Cost = tuple->at(0);
            const std::vector<int>* tuples = &puser_.getValuesVec({});
            const std::vector<int>* tuplesU = &uuser_.getValuesVec({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int U = tuple->at(0);
                int MIN = tuple->at(1);
                int MAX = tuple->at(2);
                Tuple* aux = factory.addNewInternalTuple({Cost,U,MIN,MAX}, &_aux1);
                const auto& insertResult = aux->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(aux->getId());
                    insertUndef(insertResult);
                    {
                        Tuple* head = factory.addNewInternalTuple({Cost,U},&_body0);
                        const auto& headInsertResult = head->setStatus(Undef);
                        if (headInsertResult.second) {
                            factory.removeFromCollisionsList(head->getId());
                            insertUndef(headInsertResult);
                        }
                        Tuple* aggr_id7 = factory.addNewInternalTuple({Cost,U},&_aggr_id0);
                        const auto& aggrIdInsertResult7 = aggr_id7->setStatus(Undef);
                        if (aggrIdInsertResult7.second) {
                            factory.removeFromCollisionsList(aggr_id7->getId());
                            insertUndef(aggrIdInsertResult7);
                        }
                        Tuple* aggr_id8 = factory.addNewInternalTuple({Cost,U},&_aggr_id1);
                        const auto& aggrIdInsertResult8 = aggr_id8->setStatus(Undef);
                        if (aggrIdInsertResult8.second) {
                            factory.removeFromCollisionsList(aggr_id8->getId());
                            insertUndef(aggrIdInsertResult8);
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pbody0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ubody0_.getValuesVec({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int Cost = tuple->at(0);
            int U = tuple->at(1);
            Tuple* boundTuple = factory.find({Cost,U}, &_aggr_id0);
            if(boundTuple != NULL  && !boundTuple->isFalse()){
                Tuple* boundTuple = factory.find({Cost,U}, &_aggr_id1);
                if(boundTuple == NULL || !boundTuple->isTrue()){
                    Tuple* aux = factory.addNewInternalTuple({U,Cost}, &_costs);
                    const auto& insertResult = aux->setStatus(Undef);
                    if (insertResult.second) {
                        factory.removeFromCollisionsList(aux->getId());
                        insertUndef(insertResult);
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* aggregateIds = &uaggr_id0_.getValuesVec({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(it);
            const std::set<int,AggregateSetCmp>* aggrSetTuples = &uaggr_set0_2_.getValuesSet({currentTuple->at(1)});
            int& possSum = possibleSum[it];
            for(auto itUndef=aggrSetTuples->begin(); itUndef!=aggrSetTuples->end(); itUndef++){
                possSum+=factory.getTupleFromInternalID(*itUndef)->at(0);
            }
        }
    }
    {
        const std::vector<int>* aggregateIds = &uaggr_id1_.getValuesVec({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(it);
            const std::set<int,AggregateSetCmp>* aggrSetTuples = &uaggr_set0_2_.getValuesSet({currentTuple->at(1)});
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
    paggr_id1_1_.clear();
    paggr_id0_.clear();
    paggr_id0_1_.clear();
    pbody0_.clear();
    faggr_id1_.clear();
    faggr_id1_1_.clear();
    faggr_id0_.clear();
    faggr_id0_1_.clear();
    fbody0_.clear();
}
void Executor::init() {
    std::cout<<"Init"<<std::endl;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["assign"] = &_assign;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    stringToUniqueStringPointer["aux_val0"] = &_aux_val0;
    stringToUniqueStringPointer["body0"] = &_body0;
    stringToUniqueStringPointer["component"] = &_component;
    stringToUniqueStringPointer["costs"] = &_costs;
    stringToUniqueStringPointer["user"] = &_user;
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
                            const std::vector<int>* aggrIds = &paggr_id0_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id1_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id1_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id1_1_.getValuesVec({tupleU->at(2)});
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
                            const std::vector<int>* aggrIds = &paggr_id0_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id1_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id1_1_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id1_1_.getValuesVec({tupleU->at(2)});
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
    for(int internalId : pcosts_.getValuesVec({})){
        factory.getTupleFromInternalID(internalId)->print();
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
                    const std::vector<int>* aggrIds = &paggr_id0_1_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id0_1_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id0_1_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
            }
            if(tuple->getPredicateName() == &_aggr_set0){
                {
                    const std::vector<int>* aggrIds = &paggr_id1_1_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id1_1_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id1_1_.getValuesVec({tuple->at(2)});
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
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &puser_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uuser_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_user && !tupleUNegated)
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
                        int U = tuple0->at(0);
                        int MIN = tuple0->at(1);
                        int MAX = tuple0->at(2);
                        const std::vector<int>* tuples = &pcosts_0_.getValuesVec({U});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucosts_0_.getValuesVec({U});
                        else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                                if(tupleU->at(0) == U)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int Cost = tuple1->at(1);
                                if(Cost > MAX){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &puser_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uuser_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_user && !tupleUNegated)
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
                        int U = tuple0->at(0);
                        int MIN = tuple0->at(1);
                        int MAX = tuple0->at(2);
                        const std::vector<int>* tuples = &pcosts_0_.getValuesVec({U});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucosts_0_.getValuesVec({U});
                        else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                                if(tupleU->at(0) == U)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int Cost = tuple1->at(1);
                                if(Cost < MIN){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &pbody0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        int Cost = tuple0->at(0);
                        int U = tuple0->at(1);
                        const Tuple* tuple1 = factory.find({Cost,U},&_aggr_id0);
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
                            Tuple negativeTuple({Cost,U},&_aggr_id1);
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
                                        if(tupleU->getPredicateName() != &_aggr_id1 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({U,Cost},&_costs);
                                const Tuple* tuple3 = factory.find(negativeTuple);
                                if(tuple3 == NULL)
                                    tuple3 = &negativeTuple;
                                else{
                                    if(tuple3->isTrue())
                                        tuple3 = NULL;
                                    else if(tuple3->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple3;
                                            tupleUNegated=true;
                                        }else{
                                            if(tupleU->getPredicateName() != &_costs || !tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &pcosts_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucosts_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                        int U = tuple0->at(0);
                        int Cost = tuple0->at(1);
                        const Tuple* tuple1 = factory.find({Cost,U},&_aggr_id1);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &pcosts_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucosts_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                        int U = tuple0->at(0);
                        int Cost = tuple0->at(1);
                        Tuple negativeTuple({Cost,U},&_aggr_id0);
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
                                    if(tupleU->getPredicateName() != &_aggr_id0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &pcosts_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucosts_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                        int U = tuple0->at(0);
                        int Cost = tuple0->at(1);
                        Tuple negativeTuple({Cost,U},&_body0);
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
                                    if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &paux_val0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_val0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux_val0 && !tupleUNegated)
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
                        int Cost = tuple0->at(0);
                        const std::vector<int>* tuples = &puser_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uuser_.getValuesVec({});
                        else if(tupleU->getPredicateName() == &_user && !tupleUNegated)
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
                                tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int U = tuple1->at(0);
                                int MIN = tuple1->at(1);
                                int MAX = tuple1->at(2);
                                Tuple negativeTuple({Cost,U,MIN,MAX},&_aux1);
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
                                            if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &paux1_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        int Cost = tuple0->at(0);
                        int U = tuple0->at(1);
                        int MIN = tuple0->at(2);
                        int MAX = tuple0->at(3);
                        Tuple negativeTuple({U,MIN,MAX},&_user);
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
                                    if(tupleU->getPredicateName() != &_user || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &paux1_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        int Cost = tuple0->at(0);
                        int U = tuple0->at(1);
                        int MIN = tuple0->at(2);
                        int MAX = tuple0->at(3);
                        Tuple negativeTuple({Cost},&_aux_val0);
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
                                    if(tupleU->getPredicateName() != &_aux_val0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &passign_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uassign_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_assign && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        int U = tuple0->at(1);
                        const std::vector<int>* tuples = &pcomponent_0_.getValuesVec({C});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucomponent_0_.getValuesVec({C});
                        else if(tupleU->getPredicateName() == &_component && !tupleUNegated)
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
                                if(tupleU->at(0) == C)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int P = tuple1->at(1);
                                Tuple negativeTuple({P,C,U},&_aggr_set0);
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
                                            if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::set<int,AggregateSetCmp>* tuples = &paggr_set0_.getValuesSet({});
                const std::set<int,AggregateSetCmp>* tuplesU = &EMPTY_TUPLES_SET;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_.getValuesSet({});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
                    undeRepeated.push_back(tupleU);
                auto itTrue = tuples->begin();
                auto itUndef = tuplesU->begin();
                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                    if(tuplesU!=&EMPTY_TUPLES_SET)
                        tupleU = NULL;
                    const Tuple* tuple0 = NULL;
                    if(i<tuples->size()){
                        tuple0 = factory.getTupleFromInternalID(*itTrue);
                        itTrue++;
                    }else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(*itUndef);
                        tupleUNegated=false;
                        itUndef++;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int P = tuple0->at(0);
                        int C = tuple0->at(1);
                        int U = tuple0->at(2);
                        Tuple negativeTuple({C,P},&_component);
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
                                    if(tupleU->getPredicateName() != &_component || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::set<int,AggregateSetCmp>* tuples = &paggr_set0_.getValuesSet({});
                const std::set<int,AggregateSetCmp>* tuplesU = &EMPTY_TUPLES_SET;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_.getValuesSet({});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
                    undeRepeated.push_back(tupleU);
                auto itTrue = tuples->begin();
                auto itUndef = tuplesU->begin();
                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                    if(tuplesU!=&EMPTY_TUPLES_SET)
                        tupleU = NULL;
                    const Tuple* tuple0 = NULL;
                    if(i<tuples->size()){
                        tuple0 = factory.getTupleFromInternalID(*itTrue);
                        itTrue++;
                    }else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(*itUndef);
                        tupleUNegated=false;
                        itUndef++;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int P = tuple0->at(0);
                        int C = tuple0->at(1);
                        int U = tuple0->at(2);
                        Tuple negativeTuple({C,U},&_assign);
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
                                    if(tupleU->getPredicateName() != &_assign || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            const std::vector<int>* trueHeads = &pbody0_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int Cost = currentHead->at(0);
                int U = currentHead->at(1);
                const std::vector<int>* tuples = &paux1_0_1_.getValuesVec({Cost, U});
                const std::vector<int>* tuplesU = &uaux1_0_1_.getValuesVec({Cost, U});
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
            const std::vector<int>* falseHeads = &fbody0_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                int Cost = currentHead->at(0);
                int U = currentHead->at(1);
                const std::vector<int>* tuples = &paux1_0_1_.getValuesVec({Cost, U});
                const std::vector<int>* tuplesU = &uaux1_0_1_.getValuesVec({Cost, U});
                if(tuples->size()>0){
                    propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const std::vector<int>* undefHeads = &ubody0_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                int Cost = currentHead->at(0);
                int U = currentHead->at(1);
                const std::vector<int>* tuples = &paux1_0_1_.getValuesVec({Cost, U});
                const std::vector<int>* tuplesU = &uaux1_0_1_.getValuesVec({Cost, U});
                if(tuples->size() > 0)
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(tuplesU->size()==0)
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int Cost = currentTuple->at(0);
                int U = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < Cost-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= Cost-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                int Cost = currentTuple->at(0);
                int U = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= Cost){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < Cost-currentJoinTuple->at(0))break;
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
                    int Cost = currentTuple->at(0);
                    int U = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(1)});
                    const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesU->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum >= Cost){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else if(actSum < Cost - posSum){
                        int itProp = tuplesU->at(i);
                        const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int Cost = currentTuple->at(0);
                    int U = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(1)});
                    const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                    int aggrIdIt=tuples->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum < Cost+1-posSum){
                        propagatedLiterals.push_back(1);
                    }else{
                        while(!joinTuplesU->empty()){
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                            if(actSum >= Cost+1-posSum+currentJoinTuple->at(0)) {break;}
                            int itProp = *joinTuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                    int Cost = currentTuple->at(0);
                    int U = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(1)});
                    const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesF->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    if(actSum >= Cost+1){
                        propagatedLiterals.push_back(1);
                    }else{
                        while(!joinTuplesU->empty()){
                            int itProp = *joinTuplesU->begin();
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                            if(actSum < Cost+1-currentJoinTuple->at(0))break;
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
                        int Cost = currentTuple->at(0);
                        int U = currentTuple->at(1);
                        std::vector<int> sharedVar({currentTuple->at(1)});
                        const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                        const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                        int aggrIdIt=tuplesU->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        int& posSum = possibleSum[aggrIdIt];
                        if(actSum >= Cost+1){
                            int itProp = tuplesU->at(i);
                            for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                int it = *j;
                                shared_reason.get()->insert(it);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else if(actSum < Cost+1 - posSum){
                            int itProp = tuplesU->at(i);
                            const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
            }//close decision level == -1
            while(!propagationStack.empty()){
                int startVar = propagationStack.back();
                int uStartVar = startVar<0 ? -startVar : startVar;
                Tuple starter (*factory.getTupleFromInternalID(uStartVar));
                std::string minus = startVar < 0 ? "not " : "";
                propagationStack.pop_back();
                {
                    if(starter.getPredicateName() == &_assign && startVar < 0){
                        int C = starter[0];
                        int U = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::set<int,AggregateSetCmp>* tuples = &paggr_set0_1_2_.getValuesSet({C,U});
                        const std::set<int,AggregateSetCmp>* tuplesU = &EMPTY_TUPLES_SET;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaggr_set0_1_2_.getValuesSet({C,U});
                        else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
                            undeRepeated.push_back(tupleU);
                        auto itTrue = tuples->begin();
                        auto itUndef = tuplesU->begin();
                        for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                            if(tuplesU!=&EMPTY_TUPLES_SET)
                                tupleU = NULL;
                            const Tuple* tuple1 = NULL;
                            if(i<tuples->size()){
                                tuple1 = factory.getTupleFromInternalID(*itTrue);
                                itTrue++;
                            }else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple1 = factory.getTupleFromInternalID(*itUndef);
                                tupleUNegated=false;
                                itUndef++;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(1) == C && tupleU->at(2) == U)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int P = tuple1->at(0);
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    if(starter.getPredicateName() == &_aggr_set0 && startVar > 0){
                        int P = starter[0];
                        int C = starter[1];
                        int U = starter[2];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({C,U},&_assign);
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
                                    if(tupleU->getPredicateName() != &_assign || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    if(starter.getPredicateName() == &_component && startVar < 0){
                        int C = starter[0];
                        int P = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::set<int,AggregateSetCmp>* tuples = &paggr_set0_0_1_.getValuesSet({P,C});
                        const std::set<int,AggregateSetCmp>* tuplesU = &EMPTY_TUPLES_SET;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaggr_set0_0_1_.getValuesSet({P,C});
                        else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
                            undeRepeated.push_back(tupleU);
                        auto itTrue = tuples->begin();
                        auto itUndef = tuplesU->begin();
                        for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                            if(tuplesU!=&EMPTY_TUPLES_SET)
                                tupleU = NULL;
                            const Tuple* tuple1 = NULL;
                            if(i<tuples->size()){
                                tuple1 = factory.getTupleFromInternalID(*itTrue);
                                itTrue++;
                            }else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple1 = factory.getTupleFromInternalID(*itUndef);
                                tupleUNegated=false;
                                itUndef++;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == P && tupleU->at(1) == C)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int U = tuple1->at(2);
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    if(starter.getPredicateName() == &_aggr_set0 && startVar > 0){
                        int P = starter[0];
                        int C = starter[1];
                        int U = starter[2];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({C,P},&_component);
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
                                    if(tupleU->getPredicateName() != &_component || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    if(starter.getPredicateName() == &_aggr_set0 && startVar < 0){
                        int P = starter[0];
                        int C = starter[1];
                        int U = starter[2];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({C,U},&_assign);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_assign || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            const Tuple* tuple2 = factory.find({C,P},&_component);
                            if(tuple2!=NULL){
                                if(tuple2->isFalse())
                                tuple2=NULL;
                                else if(tuple2->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple2;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_component || tupleUNegated || !(*tupleU == *tuple2))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    if(starter.getPredicateName() == &_component && startVar > 0){
                        int C = starter[0];
                        int P = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &passign_0_.getValuesVec({C});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uassign_0_.getValuesVec({C});
                        else if(tupleU->getPredicateName() == &_assign && !tupleUNegated)
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
                                if(tupleU->at(0) == C)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int U = tuple1->at(1);
                                Tuple negativeTuple({P,C,U},&_aggr_set0);
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
                                            if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    if(starter.getPredicateName() == &_assign && startVar > 0){
                        int C = starter[0];
                        int U = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &pcomponent_0_.getValuesVec({C});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucomponent_0_.getValuesVec({C});
                        else if(tupleU->getPredicateName() == &_component && !tupleUNegated)
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
                                if(tupleU->at(0) == C)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int P = tuple1->at(1);
                                Tuple negativeTuple({P,C,U},&_aggr_set0);
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
                                            if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_aux1){
                    int Cost = starter.at(0);
                    int U = starter.at(1);
                    int MIN = starter.at(2);
                    int MAX = starter.at(3);
                    Tuple* head = factory.find({Cost,U}, &_body0);
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
                        const std::vector<int>* tuples = &paux1_0_1_.getValuesVec({Cost, U});
                        const std::vector<int>* tuplesU = &uaux1_0_1_.getValuesVec({Cost, U});
                        if(head != NULL && head->isTrue()){
                            if(tuples->size() == 0 && tuplesU->size() == 0){
                                int itHead = head->getId();
                                const std::vector<int>* tuplesF = &faux1_0_1_.getValuesVec({Cost, U});
                                for(unsigned i=0;i<tuplesF->size();i++){
                                    int it = tuplesF->at(i);
                                    shared_reason.get()->insert(-it);
                                }
                                reasonForLiteral[-itHead]=shared_reason;
                                handleConflict(-itHead, propagatedLiterals);
                                return;
                            }else if(tuples->size() == 0 && tuplesU->size() == 1){
                                int itProp = tuplesU->at(0);
                                const std::vector<int>* tuplesF = &faux1_0_1_.getValuesVec({Cost, U});
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
                                const std::vector<int>* tuplesF = &faux1_0_1_.getValuesVec({Cost, U});
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
                }else if(starter.getPredicateName() == &_body0){
                    int Cost = starter.at(0);
                    int U = starter.at(1);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    const std::vector<int>* tuples = &paux1_0_1_.getValuesVec({Cost,U});
                    const std::vector<int>* tuplesU = &uaux1_0_1_.getValuesVec({Cost,U});
                    if(startVar > 0){
                        if(tuples->size()==0){
                            if(tuplesU->size() == 0){
                                const std::vector<int>* tuplesF = &faux1_0_1_.getValuesVec({Cost,U});
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
                                const std::vector<int>* tuplesF = &faux1_0_1_.getValuesVec({Cost,U});
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
                if(starter.getPredicateName() == &_aux_val0 && startVar < 0){
                    int Cost = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &paux1_0_.getValuesVec({Cost});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux1_0_.getValuesVec({Cost});
                    else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                            if(tupleU->at(0) == Cost)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int U = tuple1->at(1);
                            int MIN = tuple1->at(2);
                            int MAX = tuple1->at(3);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_aux1 && startVar > 0){
                    int Cost = starter[0];
                    int U = starter[1];
                    int MIN = starter[2];
                    int MAX = starter[3];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    Tuple negativeTuple({Cost},&_aux_val0);
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
                                if(tupleU->getPredicateName() != &_aux_val0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_user && startVar < 0){
                    int U = starter[0];
                    int MIN = starter[1];
                    int MAX = starter[2];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &paux1_1_2_3_.getValuesVec({U,MIN,MAX});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux1_1_2_3_.getValuesVec({U,MIN,MAX});
                    else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                            if(tupleU->at(1) == U && tupleU->at(2) == MIN && tupleU->at(3) == MAX)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int Cost = tuple1->at(0);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_aux1 && startVar > 0){
                    int Cost = starter[0];
                    int U = starter[1];
                    int MIN = starter[2];
                    int MAX = starter[3];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    Tuple negativeTuple({U,MIN,MAX},&_user);
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
                                if(tupleU->getPredicateName() != &_user || !tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_aux1 && startVar < 0){
                    int Cost = starter[0];
                    int U = starter[1];
                    int MIN = starter[2];
                    int MAX = starter[3];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const Tuple* tuple1 = factory.find({Cost},&_aux_val0);
                    if(tuple1!=NULL){
                        if(tuple1->isFalse())
                        tuple1=NULL;
                        else if(tuple1->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple1;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_aux_val0 || tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
                        }
                    }
                    if(tuple1!=NULL){
                        const Tuple* tuple2 = factory.find({U,MIN,MAX},&_user);
                        if(tuple2!=NULL){
                            if(tuple2->isFalse())
                            tuple2=NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_user || tupleUNegated || !(*tupleU == *tuple2))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_user && startVar > 0){
                    int U = starter[0];
                    int MIN = starter[1];
                    int MAX = starter[2];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &paux_val0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux_val0_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_aux_val0 && !tupleUNegated)
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
                            tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int Cost = tuple1->at(0);
                            Tuple negativeTuple({Cost,U,MIN,MAX},&_aux1);
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
                                        if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                if(starter.getPredicateName() == &_aux_val0 && startVar > 0){
                    int Cost = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &puser_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uuser_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_user && !tupleUNegated)
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
                            tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int U = tuple1->at(0);
                            int MIN = tuple1->at(1);
                            int MAX = tuple1->at(2);
                            Tuple negativeTuple({Cost,U,MIN,MAX},&_aux1);
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
                                        if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                int Cost = starter[0];
                int U = starter[1];
                std::vector<int> sharedVar({starter[1]});
                const std::set<int,AggregateSetCmp>* tuples = &paggr_set0_2_.getValuesSet(sharedVar);
                const std::set<int,AggregateSetCmp>* tuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(startVar < 0){
                    int& actSum = actualSum[uStartVar];
                    if(actSum>=Cost){
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
                            if(actSum >= Cost-currentTuple->at(0)){
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
                    if(actSum+posSum < Cost){
                        const std::set<int,AggregateSetCmp>* tuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                            if(actSum < Cost-posSum+currentTuple->at(0)){
                                int itProp = *tuplesU->begin();
                                if(shared_reason.get()->empty()){
                                    const std::set<int,AggregateSetCmp>* tuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                    int Cost = currentTuple->at(0);
                    int U = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(1)});
                    const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                    int aggrIdIt=tuples->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum < Cost-posSum){
                        int itProp = tuples->at(i);
                        const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                            if(actSum >= Cost-posSum+currentJoinTuple->at(0)) {break;}
                            int itProp = *joinTuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                    int Cost = currentTuple->at(0);
                    int U = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(1)});
                    const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesF->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    if(actSum >= Cost){
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
                            if(actSum < Cost-currentJoinTuple->at(0))break;
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
                        int Cost = currentTuple->at(0);
                        int U = currentTuple->at(1);
                        std::vector<int> sharedVar({currentTuple->at(1)});
                        const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                        const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                        int aggrIdIt=tuplesU->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        int& posSum = possibleSum[aggrIdIt];
                        if(actSum >= Cost){
                            int itProp = tuplesU->at(i);
                            for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                int it = *j;
                                shared_reason.get()->insert(it);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else if(actSum < Cost - posSum){
                            int itProp = tuplesU->at(i);
                            const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                if(starter.getPredicateName() == &_aggr_id1){
                    int Cost = starter[0];
                    int U = starter[1];
                    std::vector<int> sharedVar({starter[1]});
                    const std::set<int,AggregateSetCmp>* tuples = &paggr_set0_2_.getValuesSet(sharedVar);
                    const std::set<int,AggregateSetCmp>* tuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    if(startVar < 0){
                        int& actSum = actualSum[uStartVar];
                        if(actSum>=Cost+1){
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
                                if(actSum >= Cost+1-currentTuple->at(0)){
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
                        if(actSum+posSum < Cost+1){
                            const std::set<int,AggregateSetCmp>* tuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                                if(actSum < Cost+1-posSum+currentTuple->at(0)){
                                    int itProp = *tuplesU->begin();
                                    if(shared_reason.get()->empty()){
                                        const std::set<int,AggregateSetCmp>* tuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                    const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
                    const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
                    const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
                    for(unsigned i = 0; i<tuples->size(); i++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                        int Cost = currentTuple->at(0);
                        int U = currentTuple->at(1);
                        std::vector<int> sharedVar({currentTuple->at(1)});
                        const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                        const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                        int aggrIdIt=tuples->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        int& posSum = possibleSum[aggrIdIt];
                        if(actSum < Cost+1-posSum){
                            int itProp = tuples->at(i);
                            const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                                if(actSum >= Cost+1-posSum+currentJoinTuple->at(0)) {break;}
                                int itProp = *joinTuplesU->begin();
                                if(shared_reason.get()->empty()){
                                    const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                        int Cost = currentTuple->at(0);
                        int U = currentTuple->at(1);
                        std::vector<int> sharedVar({currentTuple->at(1)});
                        const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                        const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                        int aggrIdIt=tuplesF->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        if(actSum >= Cost+1){
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
                                if(actSum < Cost+1-currentJoinTuple->at(0))break;
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
                            int Cost = currentTuple->at(0);
                            int U = currentTuple->at(1);
                            std::vector<int> sharedVar({currentTuple->at(1)});
                            const std::set<int,AggregateSetCmp>* joinTuples = &paggr_set0_2_.getValuesSet(sharedVar);
                            const std::set<int,AggregateSetCmp>* joinTuplesU = &uaggr_set0_2_.getValuesSet(sharedVar);
                            int aggrIdIt=tuplesU->at(i);
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            int& actSum = actualSum[aggrIdIt];
                            int& posSum = possibleSum[aggrIdIt];
                            if(actSum >= Cost+1){
                                int itProp = tuplesU->at(i);
                                for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                    int it = *j;
                                    shared_reason.get()->insert(it);
                                }
                                auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else if(actSum < Cost+1 - posSum){
                                int itProp = tuplesU->at(i);
                                const std::set<int,AggregateSetCmp>* joinTuplesF = &faggr_set0_2_.getValuesSet(sharedVar);
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
                        if(starter.getPredicateName() == &_body0 && startVar < 0){
                            int Cost = starter[0];
                            int U = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({U,Cost},&_costs);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_costs || tupleUNegated || !(*tupleU == *tuple1))
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
                                        shared_reason.get()->insert(it*-1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                    if(!itReason.second && itReason.first->second.get()->empty())
                                        itReason.first->second=shared_reason;
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        if(starter.getPredicateName() == &_costs && startVar > 0){
                            int U = starter[0];
                            int Cost = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({Cost,U},&_body0);
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
                                        if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        if(starter.getPredicateName() == &_aggr_id0 && startVar < 0){
                            int Cost = starter[0];
                            int U = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({U,Cost},&_costs);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_costs || tupleUNegated || !(*tupleU == *tuple1))
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
                                        shared_reason.get()->insert(it*-1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                    if(!itReason.second && itReason.first->second.get()->empty())
                                        itReason.first->second=shared_reason;
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        if(starter.getPredicateName() == &_costs && startVar > 0){
                            int U = starter[0];
                            int Cost = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({Cost,U},&_aggr_id0);
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
                                        if(tupleU->getPredicateName() != &_aggr_id0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        if(starter.getPredicateName() == &_aggr_id1 && startVar > 0){
                            int Cost = starter[0];
                            int U = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({U,Cost},&_costs);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_costs || tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        if(starter.getPredicateName() == &_costs && startVar > 0){
                            int U = starter[0];
                            int Cost = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Cost,U},&_aggr_id1);
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                    {
                        if(starter.getPredicateName() == &_costs && startVar < 0){
                            int U = starter[0];
                            int Cost = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Cost,U},&_body0);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_body0 || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                const Tuple* tuple2 = factory.find({Cost,U},&_aggr_id0);
                                if(tuple2!=NULL){
                                    if(tuple2->isFalse())
                                    tuple2=NULL;
                                    else if(tuple2->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple2;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != &_aggr_id0 || tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    Tuple negativeTuple({Cost,U},&_aggr_id1);
                                    const Tuple* tuple3 = factory.find(negativeTuple);
                                    if(tuple3 == NULL)
                                        tuple3 = &negativeTuple;
                                    else{
                                        if(tuple3->isTrue())
                                            tuple3 = NULL;
                                        else if(tuple3->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple3;
                                                tupleUNegated=true;
                                            }else{
                                                if(tupleU->getPredicateName() != &_aggr_id1 || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
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
                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                int it = tuple3->getId();
                                                shared_reason.get()->insert(it*-1);
                                            }
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                                            if(tuple3!=NULL){
                                                int it = tuple3->getId();
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
                        if(starter.getPredicateName() == &_aggr_id1 && startVar < 0){
                            int Cost = starter[0];
                            int U = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Cost,U},&_body0);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_body0 || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                const Tuple* tuple2 = factory.find({Cost,U},&_aggr_id0);
                                if(tuple2!=NULL){
                                    if(tuple2->isFalse())
                                    tuple2=NULL;
                                    else if(tuple2->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple2;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != &_aggr_id0 || tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    Tuple negativeTuple({U,Cost},&_costs);
                                    const Tuple* tuple3 = factory.find(negativeTuple);
                                    if(tuple3 == NULL)
                                        tuple3 = &negativeTuple;
                                    else{
                                        if(tuple3->isTrue())
                                            tuple3 = NULL;
                                        else if(tuple3->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple3;
                                                tupleUNegated=true;
                                            }else{
                                                if(tupleU->getPredicateName() != &_costs || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
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
                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                int it = tuple3->getId();
                                                shared_reason.get()->insert(it*-1);
                                            }
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                                            if(tuple3!=NULL){
                                                int it = tuple3->getId();
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
                        if(starter.getPredicateName() == &_aggr_id0 && startVar > 0){
                            int Cost = starter[0];
                            int U = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Cost,U},&_body0);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_body0 || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                Tuple negativeTuple({Cost,U},&_aggr_id1);
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
                                            if(tupleU->getPredicateName() != &_aggr_id1 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    Tuple negativeTuple({U,Cost},&_costs);
                                    const Tuple* tuple3 = factory.find(negativeTuple);
                                    if(tuple3 == NULL)
                                        tuple3 = &negativeTuple;
                                    else{
                                        if(tuple3->isTrue())
                                            tuple3 = NULL;
                                        else if(tuple3->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple3;
                                                tupleUNegated=true;
                                            }else{
                                                if(tupleU->getPredicateName() != &_costs || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
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
                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                int it = tuple3->getId();
                                                shared_reason.get()->insert(it*-1);
                                            }
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                                            if(tuple3!=NULL){
                                                int it = tuple3->getId();
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
                        if(starter.getPredicateName() == &_body0 && startVar > 0){
                            int Cost = starter[0];
                            int U = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Cost,U},&_aggr_id0);
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
                                Tuple negativeTuple({Cost,U},&_aggr_id1);
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
                                            if(tupleU->getPredicateName() != &_aggr_id1 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    Tuple negativeTuple({U,Cost},&_costs);
                                    const Tuple* tuple3 = factory.find(negativeTuple);
                                    if(tuple3 == NULL)
                                        tuple3 = &negativeTuple;
                                    else{
                                        if(tuple3->isTrue())
                                            tuple3 = NULL;
                                        else if(tuple3->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple3;
                                                tupleUNegated=true;
                                            }else{
                                                if(tupleU->getPredicateName() != &_costs || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
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
                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                int it = tuple3->getId();
                                                shared_reason.get()->insert(it*-1);
                                            }
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                                            if(tuple3!=NULL){
                                                int it = tuple3->getId();
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
                    {
                        if(starter.getPredicateName() == &_costs && startVar > 0){
                            int U = starter[0];
                            int Cost = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &puser_0_.getValuesVec({U});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uuser_0_.getValuesVec({U});
                            else if(tupleU->getPredicateName() == &_user && !tupleUNegated)
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
                                    if(tupleU->at(0) == U)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int MIN = tuple1->at(1);
                                    int MAX = tuple1->at(2);
                                    if(Cost < MIN){
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
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == &_user && startVar > 0){
                            int U = starter[0];
                            int MIN = starter[1];
                            int MAX = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &pcosts_0_.getValuesVec({U});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ucosts_0_.getValuesVec({U});
                            else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                                    if(tupleU->at(0) == U)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Cost = tuple1->at(1);
                                    if(Cost < MIN){
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
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == &_costs && startVar > 0){
                            int U = starter[0];
                            int Cost = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &puser_0_.getValuesVec({U});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uuser_0_.getValuesVec({U});
                            else if(tupleU->getPredicateName() == &_user && !tupleUNegated)
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
                                    if(tupleU->at(0) == U)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int MIN = tuple1->at(1);
                                    int MAX = tuple1->at(2);
                                    if(Cost > MAX){
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
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == &_user && startVar > 0){
                            int U = starter[0];
                            int MIN = starter[1];
                            int MAX = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &pcosts_0_.getValuesVec({U});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ucosts_0_.getValuesVec({U});
                            else if(tupleU->getPredicateName() == &_costs && !tupleUNegated)
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
                                    if(tupleU->at(0) == U)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Cost = tuple1->at(1);
                                    if(Cost > MAX){
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
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }
                if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
            }
            }
