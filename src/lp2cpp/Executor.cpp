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

#include <chrono>

#include "datastructures/AuxiliaryMapSmart.h"

#include "datastructures/VectorAsSet.h"

#include "../tsl/hopscotch_map.h"

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
const std::string _agg_id_0 = "agg_id_0";
const std::string _agg_id_1 = "agg_id_1";
const std::string _agg_set_0 = "agg_set_0";
const std::string _assign = "assign";
const std::string _aux_0 = "aux_0";
const std::string _aux_val0 = "aux_val0";
const std::string _body_0 = "body_0";
const std::string _component = "component";
const std::string _costs = "costs";
const std::string _user = "user";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
std::vector<int> visitedExplainLiteral;
std::unordered_set<int> eagerFacts;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
std::vector<int> falseLits;
bool unRoll=false;
unsigned conflictCount=0;
Executor::~Executor() {
}


const std::vector<int> EMPTY_TUPLES_VEC;
const IndexedSet EMPTY_TUPLES_SET;
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
AuxMap<64> paux_0_0_1_({0,1});
AuxMap<64> uaux_0_0_1_({0,1});
AuxMap<64> faux_0_0_1_({0,1});
AuxMap<0> paux_0_({});
AuxMap<0> uaux_0_({});
AuxMap<0> faux_0_({});
AuxMap<0> pbody_0_({});
AuxMap<0> ubody_0_({});
AuxMap<0> fbody_0_({});
AuxMap<0> puser_({});
AuxMap<0> uuser_({});
AuxMap<0> fuser_({});
AuxMap<96> paux_0_0_2_3_({0,2,3});
AuxMap<96> uaux_0_0_2_3_({0,2,3});
AuxMap<96> faux_0_0_2_3_({0,2,3});
AuxMap<32> paux_0_1_({1});
AuxMap<32> uaux_0_1_({1});
AuxMap<32> faux_0_1_({1});
AuxMap<0> pagg_set_0_({});
AuxMap<0> uagg_set_0_({});
AuxMap<0> fagg_set_0_({});
AuxMap<0> passign_({});
AuxMap<0> uassign_({});
AuxMap<0> fassign_({});
AuxMap<64> pagg_set_0_1_2_({1,2});
AuxMap<64> uagg_set_0_1_2_({1,2});
AuxMap<64> fagg_set_0_1_2_({1,2});
AuxMap<0> pcomponent_({});
AuxMap<0> ucomponent_({});
AuxMap<0> fcomponent_({});
AuxMap<64> pagg_set_0_0_1_({0,1});
AuxMap<64> uagg_set_0_0_1_({0,1});
AuxMap<64> fagg_set_0_0_1_({0,1});
AuxMap<32> pcomponent_0_({0});
AuxMap<32> ucomponent_0_({0});
AuxMap<32> fcomponent_0_({0});
AuxMap<32> passign_0_({0});
AuxMap<32> uassign_0_({0});
AuxMap<32> fassign_0_({0});
AuxMap<0> pagg_id_0_({});
AuxMap<0> uagg_id_0_({});
AuxMap<0> fagg_id_0_({});
AuxMap<32> pagg_id_0_0_({0});
AuxMap<32> uagg_id_0_0_({0});
AuxMap<32> fagg_id_0_0_({0});
AuxMap<32> pagg_set_0_2_({2});
AuxMap<32> uagg_set_0_2_({2});
AuxMap<32> fagg_set_0_2_({2});
AuxMap<0> pagg_id_1_({});
AuxMap<0> uagg_id_1_({});
AuxMap<0> fagg_id_1_({});
AuxMap<32> pagg_id_1_0_({0});
AuxMap<32> uagg_id_1_0_({0});
AuxMap<32> fagg_id_1_0_({0});
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
    if(currentDecisionLevel <= 0){
        propagatedLiterals.push_back(1);
        return;
    }

    explainLevel++;
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    explainExternalLiteral(literal,conflictReason,true);
    explainExternalLiteral(-literal,conflictReason,true);
    propagatedLiterals.push_back(1);
    reasonForLiteral[literal].get()->clear();
}
int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,bool propagatorCall){
    int literalsCount = factory.size();
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        Tuple* waspTuple = factory.getTupleFromWASPID(uVar);
        if(waspTuple==NULL) std::cout << "WARNING: Unable to find tuple from wasp id in explainExternalLiteral"<<std::endl;
        int internalVar = waspTuple->getId();
        var = var>0 ? internalVar : -internalVar;
        explainLevel++;
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
            int& visitCount = reasonLiteral>=0 ? visitedExplainLiteral[reasonLiteral] : visitedExplainLiteral[literalsCount-reasonLiteral];
            if(visitCount != explainLevel){
                visitCount=explainLevel;
                Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);
                if(literal==NULL) std::cout << "WARNING: Unable to find tuple in reason "<<reasonLiteral<<std::endl;
                if(literal->getWaspID()==0){
                    stack.push_back(reasonLiteral);
                }else{
                    int signedLit = reasonLiteral>0 ? literal->getWaspID() : -literal->getWaspID();
                    reas.insert(signedLit);
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
    if(insertResult.first->getPredicateName() == &_component){
        fcomponent_.insert2Vec(*insertResult.first);
        fcomponent_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        fassign_.insert2Vec(*insertResult.first);
        fassign_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_set_0){
        fagg_set_0_.insert2Set(*insertResult.first);
        fagg_set_0_0_1_.insert2Set(*insertResult.first);
        fagg_set_0_1_2_.insert2Set(*insertResult.first);
        fagg_set_0_2_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        fuser_.insert2Vec(*insertResult.first);
        fuser_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_1){
        fagg_id_1_.insert2Vec(*insertResult.first);
        fagg_id_1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body_0){
        fbody_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_costs){
        fcosts_.insert2Vec(*insertResult.first);
        fcosts_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_0){
        faux_0_.insert2Vec(*insertResult.first);
        faux_0_0_1_.insert2Vec(*insertResult.first);
        faux_0_0_2_3_.insert2Vec(*insertResult.first);
        faux_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_0){
        fagg_id_0_.insert2Vec(*insertResult.first);
        fagg_id_0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        faux_val0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_component){
        pcomponent_.insert2Vec(*insertResult.first);
        pcomponent_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        passign_.insert2Vec(*insertResult.first);
        passign_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_set_0){
        pagg_set_0_.insert2Set(*insertResult.first);
        pagg_set_0_0_1_.insert2Set(*insertResult.first);
        pagg_set_0_1_2_.insert2Set(*insertResult.first);
        pagg_set_0_2_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        puser_.insert2Vec(*insertResult.first);
        puser_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_1){
        pagg_id_1_.insert2Vec(*insertResult.first);
        pagg_id_1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body_0){
        pbody_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_costs){
        pcosts_.insert2Vec(*insertResult.first);
        pcosts_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_0){
        paux_0_.insert2Vec(*insertResult.first);
        paux_0_0_1_.insert2Vec(*insertResult.first);
        paux_0_0_2_3_.insert2Vec(*insertResult.first);
        paux_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_0){
        pagg_id_0_.insert2Vec(*insertResult.first);
        pagg_id_0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        paux_val0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_component){
        ucomponent_.insert2Vec(*insertResult.first);
        ucomponent_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        uassign_.insert2Vec(*insertResult.first);
        uassign_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_set_0){
        uagg_set_0_.insert2Set(*insertResult.first);
        uagg_set_0_0_1_.insert2Set(*insertResult.first);
        uagg_set_0_1_2_.insert2Set(*insertResult.first);
        uagg_set_0_2_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        uuser_.insert2Vec(*insertResult.first);
        uuser_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_1){
        uagg_id_1_.insert2Vec(*insertResult.first);
        uagg_id_1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body_0){
        ubody_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_costs){
        ucosts_.insert2Vec(*insertResult.first);
        ucosts_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_0){
        uaux_0_.insert2Vec(*insertResult.first);
        uaux_0_0_1_.insert2Vec(*insertResult.first);
        uaux_0_0_2_3_.insert2Vec(*insertResult.first);
        uaux_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_0){
        uagg_id_0_.insert2Vec(*insertResult.first);
        uagg_id_0_0_.insert2Vec(*insertResult.first);
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
    if(var<0) falseLits.push_back(-tuple->getId());
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
std::unordered_map<const std::string*,std::unordered_set<int>*> predsToUnfoundedSet;
std::vector<int> foundnessFactory;
void checkFoundness(){
    while(!falseLits.empty()){
        int starter = falseLits.back();
        int current = starter >= 0 ? starter : -starter;
        falseLits.pop_back();
    }//close while
}//close function
void Executor::checkUnfoundedSets(std::vector<int>& literalsToPropagate,Executor* executor){
    checkFoundness();
}
void Executor::undefLiteralsReceived(){
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    std::cout<<"Undef received"<<std::endl;
    std::cout<<"Component 8"<<std::endl;
    std::cout<<"Component 7"<<std::endl;
    std::cout<<"Component 6"<<std::endl;
    {
        const std::vector<int>* tuples = &passign_.getValuesVec({});
        const std::vector<int>* tuplesU = &uassign_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int C = tuple0->at(0);
            int U = tuple0->at(1);
            const std::vector<int>* tuples = &pcomponent_0_.getValuesVec({C});
            const std::vector<int>* tuplesU = &ucomponent_0_.getValuesVec({C});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(tuple1->at(0) == C){
                    int P = tuple1->at(1);
                    Tuple* saving1 = factory.addNewInternalTuple({P,C,U},&_agg_set_0);
                    const auto& insertResult = saving1->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving1->getId());
                        insertUndef(insertResult);
                    }
                }
            }
        }
    }
    std::cout<<"Component 5"<<std::endl;
    {
        std::map<std::vector<int>,std::vector<int>> possibleSumValues;
        std::map<std::vector<int>,std::unordered_set<int>> possibleSumValuesSet;
        const IndexedSet* tuples = &pagg_set_0_.getValuesSet({});
        const IndexedSet* tuplesU = &uagg_set_0_.getValuesSet({});
        auto itTrue = tuples->begin();
        auto itUndef = tuplesU->begin();
        while(itTrue!=tuples->end() || itUndef != tuplesU->end()){
            Tuple* tuple = NULL;
            if(itTrue!=tuples->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
            else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;}
            int P = tuple->at(0);
            int C = tuple->at(1);
            int U = tuple->at(2);
            std::vector<int> sharedVars({U});
            if(possibleSumValues[sharedVars].empty()){ // init with 0
                possibleSumValues[sharedVars].push_back(0);
                possibleSumValuesSet[sharedVars].insert(0);
                Tuple* auxVal = factory.addNewInternalTuple({0},&_aux_val0);
                const auto& insertResult = auxVal->setStatus(True);
                if(insertResult.second){
                    factory.removeFromCollisionsList(auxVal->getId());
                    insertTrue(insertResult);
                }
            }//closing init with 0
            unsigned actualSumCount=possibleSumValues[sharedVars].size();
            for(unsigned k = 0; k < actualSumCount; k++){
                int currentSum = possibleSumValues[sharedVars][k]+P;
                if(possibleSumValuesSet[sharedVars].count(currentSum)==0){
                    possibleSumValues[sharedVars].push_back(currentSum);
                    possibleSumValuesSet[sharedVars].insert(currentSum);
                    Tuple* auxVal = factory.addNewInternalTuple({currentSum},&_aux_val0);
                    const auto& insertResult = auxVal->setStatus(True);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(auxVal->getId());
                        insertTrue(insertResult);
                    }
                }
            }
        }
    }
    std::cout<<"Component 4"<<std::endl;
    std::cout<<"Component 3"<<std::endl;
    {
        const std::vector<int>* tuples = &puser_.getValuesVec({});
        const std::vector<int>* tuplesU = &uuser_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int U = tuple0->at(0);
            int MIN = tuple0->at(1);
            int MAX = tuple0->at(2);
            const std::vector<int>* tuples = &paux_val0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaux_val0_.getValuesVec({});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int Cost = tuple1->at(0);
                Tuple* saving2 = factory.addNewInternalTuple({U,Cost,MIN,MAX},&_aux_0);
                const auto& insertResult = saving2->setStatus(Undef);
                if(insertResult.second){
                    factory.removeFromCollisionsList(saving2->getId());
                    insertUndef(insertResult);
                    Tuple* saving0 = factory.addNewInternalTuple({U,Cost},&_body_0);
                    const auto& insertResult = saving0->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving0->getId());
                        insertUndef(insertResult);
                    }
                }
            }
        }
    }
    std::cout<<"Component 2"<<std::endl;
    {
        const std::vector<int>* tuples = &pbody_0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ubody_0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int U = tuple->at(0);
            int Cost = tuple->at(1);
            Tuple* saving1 = factory.addNewInternalTuple({U,Cost},&_costs);
            const auto& insertResult = saving1->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(saving1->getId());
                insertUndef(insertResult);
            }
        }
    }
    std::cout<<"Component 1"<<std::endl;
    {
        const std::vector<int>* tuples = &pbody_0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ubody_0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int U = tuple->at(0);
            int Cost = tuple->at(1);
            Tuple* aggr_id = factory.addNewInternalTuple({U,Cost},&_agg_id_1);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    std::cout<<"Component 0"<<std::endl;
    {
        const std::vector<int>* tuples = &pbody_0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ubody_0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int U = tuple->at(0);
            int Cost = tuple->at(1);
            Tuple* aggr_id = factory.addNewInternalTuple({U,Cost},&_agg_id_0);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    std::vector<int> ordered_ids;
    std::vector<int> tuplesIdOrdered;
    std::map<int, Tuple*> idToTuples;
    int currentIdIndex=0;
    {
        const IndexedSet tuples = uagg_set_0_.getValuesSet({});
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
    {
        const std::vector<int>* tuples = &pagg_id_0_.getValuesVec({});
        const std::vector<int>* tuplesU = &uagg_id_0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* aggr_id = NULL;
            if(i<tuples->size()) aggr_id=factory.getTupleFromInternalID(tuples->at(i));
            else aggr_id=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int U = aggr_id->at(0);
            int Cost = aggr_id->at(1);
            const IndexedSet* aggrSet = &pagg_set_0_2_.getValuesSet({U});
            const IndexedSet* aggrSetU = &uagg_set_0_2_.getValuesSet({U});
            auto itTrue = aggrSet->begin();
            auto itUndef = aggrSetU->begin();
            int& sum = possibleSum[aggr_id->getId()];
            while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){
                Tuple* tuple = NULL;
                bool undefTuple = false;
                if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
                else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}
                int P = tuple->at(0);
                int C = tuple->at(1);
                if(tuple->at(2) == U){
                    sum+=P;
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pagg_id_1_.getValuesVec({});
        const std::vector<int>* tuplesU = &uagg_id_1_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* aggr_id = NULL;
            if(i<tuples->size()) aggr_id=factory.getTupleFromInternalID(tuples->at(i));
            else aggr_id=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int U = aggr_id->at(0);
            int Cost = aggr_id->at(1);
            const IndexedSet* aggrSet = &pagg_set_0_2_.getValuesSet({U});
            const IndexedSet* aggrSetU = &uagg_set_0_2_.getValuesSet({U});
            auto itTrue = aggrSet->begin();
            auto itUndef = aggrSetU->begin();
            int& sum = possibleSum[aggr_id->getId()];
            while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){
                Tuple* tuple = NULL;
                bool undefTuple = false;
                if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
                else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}
                int P = tuple->at(0);
                int C = tuple->at(1);
                if(tuple->at(2) == U){
                    sum+=P;
                }
            }
        }
    }
    visitedExplainLiteral.resize(2*factory.size());
    explainLevel=1;
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
}
void Executor::init() {
    stringToUniqueStringPointer["agg_id_0"] = &_agg_id_0;
    stringToUniqueStringPointer["agg_id_1"] = &_agg_id_1;
    stringToUniqueStringPointer["agg_set_0"] = &_agg_set_0;
    stringToUniqueStringPointer["assign"] = &_assign;
    stringToUniqueStringPointer["aux_0"] = &_aux_0;
    stringToUniqueStringPointer["aux_val0"] = &_aux_val0;
    stringToUniqueStringPointer["body_0"] = &_body_0;
    stringToUniqueStringPointer["component"] = &_component;
    stringToUniqueStringPointer["costs"] = &_costs;
    stringToUniqueStringPointer["user"] = &_user;
    factory.setIndexForAggregateSet(0,&_agg_set_0);
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
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        {
                            const std::vector<int>* aggrIds = &pagg_id_0_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uagg_id_0_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &fagg_id_0_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        {
                            const std::vector<int>* aggrIds = &pagg_id_1_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uagg_id_1_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &fagg_id_1_0_.getValuesVec({tupleU->at(2)});
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
                    falseLits.push_back(-realTupleU->getId());
                    insertFalse(insertResult);
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        {
                            const std::vector<int>* aggrIds = &pagg_id_0_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uagg_id_0_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &fagg_id_0_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        {
                            const std::vector<int>* aggrIds = &pagg_id_1_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uagg_id_1_0_.getValuesVec({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &fagg_id_1_0_.getValuesVec({tupleU->at(2)});
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
inline void clearFalse(){
}
inline void clearTrue(){
}
inline void clearUndef(){
}
std::string Executor::printInternalLiterals(){
    std::string trueConstraint = "";
    for(int internalId : pcosts_.getValuesVec({})){
        Tuple* tuple = factory.getTupleFromInternalID(internalId);
        std::string tupleToString = tuple->size() > 0 ? "costs(" : "costs";
        for(unsigned k=0; k<tuple->size();k++){
            if(k>0) tupleToString+=",";
            tupleToString+=ConstantsManager::getInstance().unmapConstant(tuple->at(k));
        }
        tupleToString+= tuple->size() > 0 ? ")" : "";
        std::cout << tupleToString <<" ";
    }
    std::cout << std::endl;
    TupleFactory lazyFactory;
    clearUndef();
    clearTrue();
    clearFalse();
    return trueConstraint;
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
            int uVar = var>0 ? var : -var;
            Tuple* tuple = factory.getTupleFromInternalID(uVar);
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral[var].get()->clear();
            const auto& insertResult = tuple->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(tuple->getId());
                insertUndef(insertResult);
            }
            if(tuple->getPredicateName() == &_agg_set_0){
                {
                    const std::vector<int>* aggrIds = &pagg_id_0_0_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uagg_id_0_0_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &fagg_id_0_0_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
            }
            if(tuple->getPredicateName() == &_agg_set_0){
                {
                    const std::vector<int>* aggrIds = &pagg_id_1_0_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uagg_id_1_0_.getValuesVec({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &fagg_id_1_0_.getValuesVec({tuple->at(2)});
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
    falseLits.clear();
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts,std::vector<int>& propagatedLiterals,bool fromPropagator) {
    int decisionLevel = facts[0];
    currentDecisionLevel=solver->getCurrentDecisionLevel();
    clearPropagations();
    std::vector<int> propagationStack;
    for(unsigned i=1;i<facts.size();i++) {
        int factVar = facts[i]>0 ? facts[i] : -facts[i];
        int minus = facts[i]<0 ? -1 : 1;
        if(!fromPropagator){
            onLiteralTrue(facts[i]);
            propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());
            remainingPropagatingLiterals.erase(facts[i]);
        }else{
            propUndefined(factory.getTupleFromInternalID(factVar),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
    }
    if(decisionLevel == -1) {
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const IndexedSet* tuples = &pagg_set_0_.getValuesSet({});
                const IndexedSet* tuplesU = &EMPTY_TUPLES_SET;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uagg_set_0_.getValuesSet({});
                else if(tupleU->getPredicateName() == &_agg_set_0 && !tupleUNegated)
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
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                const IndexedSet* tuples = &pagg_set_0_.getValuesSet({});
                const IndexedSet* tuplesU = &EMPTY_TUPLES_SET;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uagg_set_0_.getValuesSet({});
                else if(tupleU->getPredicateName() == &_agg_set_0 && !tupleUNegated)
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
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                                Tuple negativeTuple({P,C,U},&_agg_set_0);
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
                                            if(tupleU->getPredicateName() != &_agg_set_0 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
            const std::vector<int>* tuples = &pagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
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
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        if(currentDecisionLevel > 0){
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
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
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        if(currentDecisionLevel>0){
                            auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= Cost){
                    if(currentDecisionLevel>0){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < Cost - posSum){
                    int itProp = tuplesU->at(i);
                    if(currentDecisionLevel>0){
                        const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<int>* tuples = &pagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_1_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
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
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        if(currentDecisionLevel > 0){
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
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
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        if(currentDecisionLevel>0){
                            auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= Cost+1){
                    if(currentDecisionLevel>0){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < Cost+1 - posSum){
                    int itProp = tuplesU->at(i);
                    if(currentDecisionLevel>0){
                        const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
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
                        Tuple negativeTuple({U,Cost},&_body_0);
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
                                    if(tupleU->getPredicateName() != &_body_0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                        Tuple negativeTuple({U,Cost},&_agg_id_0);
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
                                    if(tupleU->getPredicateName() != &_agg_id_0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                        const Tuple* tuple1 = factory.find({U,Cost},&_agg_id_1);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_agg_id_1 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                const std::vector<int>* tuples = &pbody_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_body_0 && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({U,Cost},&_agg_id_0);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_agg_id_0 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({U,Cost},&_agg_id_1);
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
                                        if(tupleU->getPredicateName() != &_agg_id_1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                                if(Cost > MAX){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                                Tuple negativeTuple({U,Cost,MIN,MAX},&_aux_0);
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
                                            if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                const std::vector<int>* tuples = &paux_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
                const std::vector<int>* tuples = &paux_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
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
            const std::vector<int>* trueHeads = &pbody_0_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                if(eagerFacts.count(currentHead->getId())!=0) continue;
                int U = currentHead->at(0);
                int Cost = currentHead->at(1);
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({U, Cost});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({U, Cost});
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
            const std::vector<int>* falseHeads = &fbody_0_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                int U = currentHead->at(0);
                int Cost = currentHead->at(1);
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({U, Cost});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({U, Cost});
                if(tuples->size()>0){
                    propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const std::vector<int>* undefHeads = &ubody_0_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                int U = currentHead->at(0);
                int Cost = currentHead->at(1);
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({U, Cost});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({U, Cost});
                if(tuples->size() > 0)
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(tuplesU->size()==0)
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
    }//close decision level == -1
    std::vector<int> propagated;
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        propagated.push_back(startVar);
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aux_0){
            int U = starter.at(0);
            int Cost = starter.at(1);
            int MIN = starter.at(2);
            int MAX = starter.at(3);
            Tuple* head = factory.find({U,Cost}, &_body_0);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar > 0){
                if(head == NULL || (!head->isTrue() && !head->isUndef())){
                    if(currentDecisionLevel>0){
                        int it = head->getId();
                        shared_reason.get()->insert(startVar);
                        reasonForLiteral[it]=shared_reason;
                        handleConflict(it, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else if(head !=NULL && head->isUndef()){
                    if(currentDecisionLevel>0){
                        int it = head->getId();
                        shared_reason.get()->insert(startVar);
                        auto itReason = reasonForLiteral.emplace(it,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({U, Cost});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({U, Cost});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        if(currentDecisionLevel>0){
                            int itHead = head->getId();
                            const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({U, Cost});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-itHead]=shared_reason;
                            handleConflict(-itHead, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        if(currentDecisionLevel>0){
                            int itProp = tuplesU->at(0);
                            const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({U, Cost});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            int it = head->getId();
                            shared_reason.get()->insert(it);
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }else if( head != NULL && head->isUndef() ){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        if(currentDecisionLevel>0){
                            int itHead = head->getId();
                            const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({U, Cost});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            auto itReason = reasonForLiteral.emplace(-itHead,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }else if(starter.getPredicateName() == &_body_0){
            int U = starter.at(0);
            int Cost = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({U,Cost});
            const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({U,Cost});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        if(currentDecisionLevel>0){
                            const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({U,Cost});
                            for(unsigned i=0; i<tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }else if(tuplesU->size()==1){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));
                        if(currentDecisionLevel>0){
                            int itProp = currentTuple->getId();
                            const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({U,Cost});
                            for(unsigned i=0; i<tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            shared_reason.get()->insert(startVar);
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()>0){
                    if(currentDecisionLevel>0){
                        int it = tuples->at(0);
                        shared_reason.get()->insert(startVar);
                        reasonForLiteral[-it]=shared_reason;
                        handleConflict(-it, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    shared_reason.get()->insert(startVar);
                    while(!tuplesU->empty()){
                        int it = tuplesU->back();
                        if(currentDecisionLevel>0){
                            auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(factory.getTupleFromInternalID(it),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
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
                const std::vector<int>* tuples = &paux_0_0_2_3_.getValuesVec({U,MIN,MAX});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_0_2_3_.getValuesVec({U,MIN,MAX});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        if(tupleU->at(0) == U && tupleU->at(2) == MIN && tupleU->at(3) == MAX)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Cost = tuple1->at(1);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
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
                            }
                            if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                            }else propagatedLiterals.push_back(1);
                            return;
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_aux_0 && startVar > 0){
                int U = starter[0];
                int Cost = starter[1];
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            if(starter.getPredicateName() == &_aux_val0 && startVar < 0){
                int Cost = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux_0_1_.getValuesVec({Cost});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_1_.getValuesVec({Cost});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        if(tupleU->at(1) == Cost)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int U = tuple1->at(0);
                        int MIN = tuple1->at(2);
                        int MAX = tuple1->at(3);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
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
                            }
                            if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                            }else propagatedLiterals.push_back(1);
                            return;
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_aux_0 && startVar > 0){
                int U = starter[0];
                int Cost = starter[1];
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            if(starter.getPredicateName() == &_aux_0 && startVar < 0){
                int U = starter[0];
                int Cost = starter[1];
                int MIN = starter[2];
                int MAX = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({U,MIN,MAX},&_user);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_user || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({Cost},&_aux_val0);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_aux_val0 || tupleUNegated || !(*tupleU == *tuple2))
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
                            if(currentDecisionLevel>0){
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
                            }
                            if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
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
                            }else propagatedLiterals.push_back(1);
                            return;
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
                        Tuple negativeTuple({U,Cost,MIN,MAX},&_aux_0);
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
                                    if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
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
                        Tuple negativeTuple({U,Cost,MIN,MAX},&_aux_0);
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
                                    if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
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
            if(starter.getPredicateName() == &_assign && startVar < 0){
                int C = starter[0];
                int U = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const IndexedSet* tuples = &pagg_set_0_1_2_.getValuesSet({C,U});
                const IndexedSet* tuplesU = &EMPTY_TUPLES_SET;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uagg_set_0_1_2_.getValuesSet({C,U});
                else if(tupleU->getPredicateName() == &_agg_set_0 && !tupleUNegated)
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
                            if(currentDecisionLevel>0){
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
                            }
                            if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                            }else propagatedLiterals.push_back(1);
                            return;
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_agg_set_0 && startVar > 0){
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
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
                const IndexedSet* tuples = &pagg_set_0_0_1_.getValuesSet({P,C});
                const IndexedSet* tuplesU = &EMPTY_TUPLES_SET;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uagg_set_0_0_1_.getValuesSet({P,C});
                else if(tupleU->getPredicateName() == &_agg_set_0 && !tupleUNegated)
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
                            if(currentDecisionLevel>0){
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
                            }
                            if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                reasonForLiteral[-startVar]=shared_reason;
                                handleConflict(-startVar, propagatedLiterals);
                            }else propagatedLiterals.push_back(1);
                            return;
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_agg_set_0 && startVar > 0){
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            if(starter.getPredicateName() == &_agg_set_0 && startVar < 0){
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
                            if(currentDecisionLevel>0){
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
                            }
                            if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                            if(currentDecisionLevel>0){
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
                            }else propagatedLiterals.push_back(1);
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
                        Tuple negativeTuple({P,C,U},&_agg_set_0);
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
                                    if(tupleU->getPredicateName() != &_agg_set_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
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
                        Tuple negativeTuple({P,C,U},&_agg_set_0);
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
                                    if(tupleU->getPredicateName() != &_agg_set_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
                                return;
                            }
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        if(starter.getPredicateName() == &_agg_id_0){
            int U = starter[0];
            int Cost = starter[1];
            std::vector<int> sharedVar({starter[0]});
            const IndexedSet* tuples = &pagg_set_0_2_.getValuesSet(sharedVar);
            const IndexedSet* tuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=Cost){
                    if(currentDecisionLevel > 0){
                        for(auto i =tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    if(!tuplesU->empty() && currentDecisionLevel>0){
                        for(auto i = tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    while(!tuplesU->empty()){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                        if(actSum >= Cost-currentTuple->at(0)){
                            if(currentDecisionLevel > 0){
                                int itProp =currentTuple->getId();
                                auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                            }
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else break;
                    }
                }
            }else{
                int& actSum = actualSum[uStartVar];
                int& posSum = possibleSum[uStartVar];
                if(actSum+posSum < Cost){
                    if(currentDecisionLevel > 0){
                        const IndexedSet* tuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                        if(actSum < Cost-posSum+currentTuple->at(0)){
                            int itProp = *tuplesU->begin();
                            if(shared_reason.get()->empty() && currentDecisionLevel>0){
                                const IndexedSet* tuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                                for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(-it);
                                }
                                shared_reason.get()->insert(startVar);
                            }
                            if(currentDecisionLevel > 0){
                                auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else break;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_agg_set_0){
            const std::vector<int>* tuples = &pagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < Cost-posSum){
                    if(currentDecisionLevel>0){
                        int itProp = tuples->at(i);
                        const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itProp]=shared_reason;
                        handleConflict(-itProp, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= Cost-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        if(currentDecisionLevel > 0){
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= Cost){
                    if(currentDecisionLevel > 0){
                        int itProp = tuplesF->at(i);
                        for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[itProp]=shared_reason;
                        handleConflict(itProp, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < Cost-currentJoinTuple->at(0))break;
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        if(currentDecisionLevel>0){
                            auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= Cost){
                    if(currentDecisionLevel>0){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < Cost - posSum){
                    int itProp = tuplesU->at(i);
                    if(currentDecisionLevel>0){
                        const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        if(starter.getPredicateName() == &_agg_id_1){
            int U = starter[0];
            int Cost = starter[1];
            std::vector<int> sharedVar({starter[0]});
            const IndexedSet* tuples = &pagg_set_0_2_.getValuesSet(sharedVar);
            const IndexedSet* tuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=Cost+1){
                    if(currentDecisionLevel > 0){
                        for(auto i =tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    if(!tuplesU->empty() && currentDecisionLevel>0){
                        for(auto i = tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    while(!tuplesU->empty()){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                        if(actSum >= Cost+1-currentTuple->at(0)){
                            if(currentDecisionLevel > 0){
                                int itProp =currentTuple->getId();
                                auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                            }
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else break;
                    }
                }
            }else{
                int& actSum = actualSum[uStartVar];
                int& posSum = possibleSum[uStartVar];
                if(actSum+posSum < Cost+1){
                    if(currentDecisionLevel > 0){
                        const IndexedSet* tuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                        if(actSum < Cost+1-posSum+currentTuple->at(0)){
                            int itProp = *tuplesU->begin();
                            if(shared_reason.get()->empty() && currentDecisionLevel>0){
                                const IndexedSet* tuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                                for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(-it);
                                }
                                shared_reason.get()->insert(startVar);
                            }
                            if(currentDecisionLevel > 0){
                                auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else break;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_agg_set_0){
            const std::vector<int>* tuples = &pagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_1_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < Cost+1-posSum){
                    if(currentDecisionLevel>0){
                        int itProp = tuples->at(i);
                        const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itProp]=shared_reason;
                        handleConflict(-itProp, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= Cost+1-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        if(currentDecisionLevel > 0){
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= Cost+1){
                    if(currentDecisionLevel > 0){
                        int itProp = tuplesF->at(i);
                        for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[itProp]=shared_reason;
                        handleConflict(itProp, propagatedLiterals);
                    }else propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < Cost+1-currentJoinTuple->at(0))break;
                        if(shared_reason.get()->empty() && currentDecisionLevel>0){
                            for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        if(currentDecisionLevel>0){
                            auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int U = currentTuple->at(0);
                int Cost = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const IndexedSet* joinTuples = &pagg_set_0_2_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_2_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= Cost+1){
                    if(currentDecisionLevel>0){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < Cost+1 - posSum){
                    int itProp = tuplesU->at(i);
                    if(currentDecisionLevel>0){
                        const IndexedSet* joinTuplesF = &fagg_set_0_2_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_body_0 && startVar < 0){
                int U = starter[0];
                int Cost = starter[1];
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
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
                Tuple negativeTuple({U,Cost},&_body_0);
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
                            if(tupleU->getPredicateName() != &_body_0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            if(starter.getPredicateName() == &_agg_id_0 && startVar < 0){
                int U = starter[0];
                int Cost = starter[1];
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
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
                Tuple negativeTuple({U,Cost},&_agg_id_0);
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
                            if(tupleU->getPredicateName() != &_agg_id_0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
                        return;
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            if(starter.getPredicateName() == &_agg_id_1 && startVar > 0){
                int U = starter[0];
                int Cost = starter[1];
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
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
                const Tuple* tuple1 = factory.find({U,Cost},&_agg_id_1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_agg_id_1 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(currentDecisionLevel>0){
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
                        }
                        if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        if(currentDecisionLevel>0){
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                shared_reason.get()->insert(it*1);
                            }
                            reasonForLiteral[-startVar]=shared_reason;
                            handleConflict(-startVar, propagatedLiterals);
                        }else propagatedLiterals.push_back(1);
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
                const Tuple* tuple1 = factory.find({U,Cost},&_body_0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_body_0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({U,Cost},&_agg_id_0);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_agg_id_0 || tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple negativeTuple({U,Cost},&_agg_id_1);
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
                                    if(tupleU->getPredicateName() != &_agg_id_1 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
                                return;
                            }
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_agg_id_1 && startVar < 0){
                int U = starter[0];
                int Cost = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({U,Cost},&_body_0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_body_0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({U,Cost},&_agg_id_0);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_agg_id_0 || tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
                                return;
                            }
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_agg_id_0 && startVar > 0){
                int U = starter[0];
                int Cost = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({U,Cost},&_body_0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_body_0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({U,Cost},&_agg_id_1);
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
                                if(tupleU->getPredicateName() != &_agg_id_1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
                                return;
                            }
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_body_0 && startVar > 0){
                int U = starter[0];
                int Cost = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({U,Cost},&_agg_id_0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_agg_id_0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({U,Cost},&_agg_id_1);
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
                                if(tupleU->getPredicateName() != &_agg_id_1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
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
                                }else propagatedLiterals.push_back(1);
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[-startVar]=shared_reason;
                                    handleConflict(-startVar, propagatedLiterals);
                                }else propagatedLiterals.push_back(1);
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[-startVar]=shared_reason;
                                    handleConflict(-startVar, propagatedLiterals);
                                }else propagatedLiterals.push_back(1);
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[-startVar]=shared_reason;
                                    handleConflict(-startVar, propagatedLiterals);
                                }else propagatedLiterals.push_back(1);
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
                                if(currentDecisionLevel>0){
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
                                }
                                if(tupleU->getPredicateName() != &_aux_val0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_body_0 && tupleU->getPredicateName() != &_agg_id_1 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_costs && tupleU->getPredicateName() != &_agg_set_0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                if(currentDecisionLevel>0){
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    reasonForLiteral[-startVar]=shared_reason;
                                    handleConflict(-startVar, propagatedLiterals);
                                }else propagatedLiterals.push_back(1);
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
