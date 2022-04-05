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
    totalReasonSize=0;
    reasonCount=0;
}
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
std::vector<std::string> Executor::predicateIds;
const int _aux_0 = 0;
const int _aux_1 = 1;
const int _e = 2;
const int _first = 3;
const int _gtnumber = 4;
const int _reachable_color = 5;
const int _sup_0 = 6;
const int _sup_1 = 7;
const int _sup_2 = 8;
const int _vertex_color = 9;
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
std::unordered_map<std::string, int > stringToUniqueStringPointer;
TupleFactory factory;
void printTuple(const Tuple* t){
    if(t->isFalse()) std::cout << "not ";
    std::cout << Executor::predicateIds[t->getPredicateName()] << "(";
    for(int i=0;i<t->size();i++){
        if(i>0) std::cout << ", ";
        std::cout << ConstantsManager::getInstance().unmapConstant(t->at(i));
    }
    std::cout << ")"<<std::endl;
}
int parseTuple(const std::string & literalString,std::vector<int>& terms) {
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
AuxMap<0> psup_0_({});
AuxMap<0> usup_0_({});
AuxMap<0> fsup_0_({});
AuxMap<0> preachable_color_({});
AuxMap<0> ureachable_color_({});
AuxMap<0> freachable_color_({});
AuxMap<0> pfirst_({});
AuxMap<0> ufirst_({});
AuxMap<0> ffirst_({});
AuxMap<32> psup_1_0_({0});
AuxMap<32> usup_1_0_({0});
AuxMap<32> fsup_1_0_({0});
AuxMap<0> psup_1_({});
AuxMap<0> usup_1_({});
AuxMap<0> fsup_1_({});
AuxMap<32> paux_0_0_({0});
AuxMap<32> uaux_0_0_({0});
AuxMap<32> faux_0_0_({0});
AuxMap<0> paux_0_({});
AuxMap<0> uaux_0_({});
AuxMap<0> faux_0_({});
AuxMap<32> paux_0_1_({1});
AuxMap<32> uaux_0_1_({1});
AuxMap<32> faux_0_1_({1});
AuxMap<0> pe_({});
AuxMap<0> ue_({});
AuxMap<0> fe_({});
AuxMap<0> pvertex_color_({});
AuxMap<0> uvertex_color_({});
AuxMap<0> fvertex_color_({});
AuxMap<32> preachable_color_0_({0});
AuxMap<32> ureachable_color_0_({0});
AuxMap<32> freachable_color_0_({0});
AuxMap<32> pe_0_({0});
AuxMap<32> ue_0_({0});
AuxMap<32> fe_0_({0});
AuxMap<0> psup_2_({});
AuxMap<0> usup_2_({});
AuxMap<0> fsup_2_({});
AuxMap<64> paux_1_0_1_({0,1});
AuxMap<64> uaux_1_0_1_({0,1});
AuxMap<64> faux_1_0_1_({0,1});
AuxMap<0> paux_1_({});
AuxMap<0> uaux_1_({});
AuxMap<0> faux_1_({});
AuxMap<64> paux_1_0_2_({0,2});
AuxMap<64> uaux_1_0_2_({0,2});
AuxMap<64> faux_1_0_2_({0,2});
AuxMap<64> paux_1_1_2_({1,2});
AuxMap<64> uaux_1_1_2_({1,2});
AuxMap<64> faux_1_1_2_({1,2});
AuxMap<0> pgtnumber_({});
AuxMap<0> ugtnumber_({});
AuxMap<0> fgtnumber_({});
AuxMap<64> paux_1_1_3_({1,3});
AuxMap<64> uaux_1_1_3_({1,3});
AuxMap<64> faux_1_1_3_({1,3});
AuxMap<32> preachable_color_1_({1});
AuxMap<32> ureachable_color_1_({1});
AuxMap<32> freachable_color_1_({1});
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
int Executor::explainExternalLiteral(int var,std::vector<int>& reas,bool propagatorCall){
    unsigned literalsCount = factory.size();
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        Tuple* waspTuple = factory.getTupleFromWASPID(uVar);
        if(waspTuple==NULL) std::cout << "WARNING: Unable to find tuple from wasp id in explainExternalLiteral"<<std::endl;
        int internalVar = waspTuple->getId();
        var = var>0 ? internalVar : -internalVar;
        explainLevel++;
        reas.reserve(factory.size());
    }
    buildingReasonStack.push_back(var);
    auto end=reasonForLiteral.end();
    while(!buildingReasonStack.empty()){
        int lit = buildingReasonStack.back();
        buildingReasonStack.pop_back();
        auto itReason = reasonForLiteral.find(lit);
        VectorAsSet<int>* currentReas = itReason != end ? itReason->second.get() : NULL;
        unsigned currentReasonSize= currentReas != NULL ? currentReas->size() : 0;
        for(unsigned i = 0; i<currentReasonSize; i++){
            int& reasonLiteral=currentReas->at(i);
            int& visitCount = reasonLiteral>=0 ? visitedExplainLiteral[reasonLiteral] : visitedExplainLiteral[literalsCount-reasonLiteral];
            if(visitCount != explainLevel){
                visitCount=explainLevel;
                Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);
                if(literal==NULL) std::cout << "WARNING: Unable to find tuple in reason "<<reasonLiteral<<std::endl;
                if(literal->isInternalLiteral()){
                    buildingReasonStack.push_back(reasonLiteral);
                }else{
                    int signedLit = reasonLiteral>0 ? literal->getWaspID() : -literal->getWaspID();
                    reas.push_back(signedLit);
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
    if(insertResult.first->getPredicateName() == _aux_1){
        faux_1_.insert2Vec(*insertResult.first);
        faux_1_0_1_.insert2Vec(*insertResult.first);
        faux_1_0_2_.insert2Vec(*insertResult.first);
        faux_1_1_2_.insert2Vec(*insertResult.first);
        faux_1_1_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_2){
        fsup_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _gtnumber){
        fgtnumber_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _vertex_color){
        fvertex_color_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _e){
        fe_.insert2Vec(*insertResult.first);
        fe_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_0){
        faux_0_.insert2Vec(*insertResult.first);
        faux_0_0_.insert2Vec(*insertResult.first);
        faux_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_1){
        fsup_1_.insert2Vec(*insertResult.first);
        fsup_1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _first){
        ffirst_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reachable_color){
        freachable_color_.insert2Vec(*insertResult.first);
        freachable_color_0_.insert2Vec(*insertResult.first);
        freachable_color_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_0){
        fsup_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == _aux_1){
        paux_1_.insert2Vec(*insertResult.first);
        paux_1_0_1_.insert2Vec(*insertResult.first);
        paux_1_0_2_.insert2Vec(*insertResult.first);
        paux_1_1_2_.insert2Vec(*insertResult.first);
        paux_1_1_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_2){
        psup_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _gtnumber){
        pgtnumber_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _vertex_color){
        pvertex_color_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _e){
        pe_.insert2Vec(*insertResult.first);
        pe_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_0){
        paux_0_.insert2Vec(*insertResult.first);
        paux_0_0_.insert2Vec(*insertResult.first);
        paux_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_1){
        psup_1_.insert2Vec(*insertResult.first);
        psup_1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _first){
        pfirst_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reachable_color){
        preachable_color_.insert2Vec(*insertResult.first);
        preachable_color_0_.insert2Vec(*insertResult.first);
        preachable_color_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_0){
        psup_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == _aux_1){
        uaux_1_.insert2Vec(*insertResult.first);
        uaux_1_0_1_.insert2Vec(*insertResult.first);
        uaux_1_0_2_.insert2Vec(*insertResult.first);
        uaux_1_1_2_.insert2Vec(*insertResult.first);
        uaux_1_1_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_2){
        usup_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _gtnumber){
        ugtnumber_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _vertex_color){
        uvertex_color_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _e){
        ue_.insert2Vec(*insertResult.first);
        ue_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_0){
        uaux_0_.insert2Vec(*insertResult.first);
        uaux_0_0_.insert2Vec(*insertResult.first);
        uaux_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_1){
        usup_1_.insert2Vec(*insertResult.first);
        usup_1_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _first){
        ufirst_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reachable_color){
        ureachable_color_.insert2Vec(*insertResult.first);
        ureachable_color_0_.insert2Vec(*insertResult.first);
        ureachable_color_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_0){
        usup_0_.insert2Vec(*insertResult.first);
    }
}
inline void Executor::onLiteralTrue(const aspc::Literal* l) {
}
inline void Executor::onLiteralUndef(const aspc::Literal* l) {
}
inline void Executor::onLiteralTrue(int var, const std::string& literalString) {
    std::vector<int> terms;
    int predicate = parseTuple(literalString,terms);
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
    if(currentDecisionLevel > 0){
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
std::vector<std::vector<int>> supportedAux0;
std::vector<std::vector<int>> supportedLiterals0;
std::unordered_map<int,int> sourcePointers0;
std::vector<int> unfoundedSetForComponent0;
void propFoundnessForComponent0(int foundedLiteral){
    std::vector<int> foundedStack({foundedLiteral});
    while(!foundedStack.empty()){
        Tuple* starter = factory.getTupleFromInternalID(foundedStack.back());
        foundedStack.pop_back();
        if(starter->getPredicateName() == _sup_1){
            if(1 == starter->at(0)){
                int W=starter->at(1);
                Tuple* head = factory.find({1,W},_reachable_color);
                if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                    supportedLiterals0[starter->getId()].push_back(head->getId());
                    sourcePointers0[head->getId()] = starter->getId();
                    foundedStack.push_back(head->getId());
                    foundnessFactory[head->getId()]=1;
                }
            }
        }
        if(starter->getPredicateName() == _aux_0){
            int W=starter->at(0);
            int V=starter->at(1);
            Tuple* head = factory.find({1,W},_sup_1);
            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                supportedLiterals0[starter->getId()].push_back(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                foundnessFactory[head->getId()]=1;
            }
        }
        if(starter->getPredicateName() == _reachable_color){
            if(1 == starter->at(0)){
                int V=starter->at(1);
                Tuple* tuple1 = factory.find({V,1},_vertex_color);
                if(tuple1!=NULL && !tuple1->isFalse()){
                    const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                    const std::vector<int>* tuplesU = &ue_0_.getValuesVec({V});
                    for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                        Tuple* tuple2 = NULL;
                        if(i<tuples->size()) tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                        else tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        int W=tuple2->at(1);
                        Tuple* head = factory.find({W,V},_aux_0);
                        if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                            foundedStack.push_back(head->getId());
                            foundnessFactory[head->getId()]=1;
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _e){
            int V=starter->at(0);
            int W=starter->at(1);
            Tuple* tuple1 = factory.find({1,V},_reachable_color);
            if(tuple1!=NULL && !tuple1->isFalse()){
                if(foundnessFactory[tuple1->getId()]>=0){
                    Tuple* tuple2 = factory.find({V,1},_vertex_color);
                    if(tuple2!=NULL && !tuple2->isFalse()){
                        Tuple* head = factory.find({W,V},_aux_0);
                        if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                            foundedStack.push_back(head->getId());
                            foundnessFactory[head->getId()]=1;
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _vertex_color){
            int V=starter->at(0);
            if(1 == starter->at(1)){
                Tuple* tuple1 = factory.find({1,V},_reachable_color);
                if(tuple1!=NULL && !tuple1->isFalse()){
                    if(foundnessFactory[tuple1->getId()]>=0){
                        const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                        const std::vector<int>* tuplesU = &ue_0_.getValuesVec({V});
                        for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                            Tuple* tuple2 = NULL;
                            if(i<tuples->size()) tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                            else tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                            int W=tuple2->at(1);
                            Tuple* head = factory.find({W,V},_aux_0);
                            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                foundedStack.push_back(head->getId());
                                foundnessFactory[head->getId()]=1;
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _sup_2){
            int C=starter->at(0);
            int W=starter->at(1);
            Tuple* head = factory.find({C,W},_reachable_color);
            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                supportedLiterals0[starter->getId()].push_back(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                foundnessFactory[head->getId()]=1;
            }
        }
        if(starter->getPredicateName() == _aux_1){
            int C=starter->at(0);
            int W=starter->at(1);
            int V=starter->at(2);
            int C1=starter->at(3);
            Tuple* head = factory.find({C,W},_sup_2);
            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                supportedLiterals0[starter->getId()].push_back(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                foundnessFactory[head->getId()]=1;
            }
        }
        if(starter->getPredicateName() == _reachable_color){
            int C=starter->at(0);
            int V=starter->at(1);
            int C1 = C - 1;
            Tuple* tuple2 = factory.find({V,C},_vertex_color);
            if(tuple2!=NULL && !tuple2->isFalse()){
                const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                const std::vector<int>* tuplesU = &ue_0_.getValuesVec({V});
                for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                    Tuple* tuple3 = NULL;
                    if(i<tuples->size()) tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                    else tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int W=tuple3->at(1);
                    Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                    if(tuple4!=NULL && !tuple4->isFalse()){
                        Tuple* head = factory.find({C,W,V,C1},_aux_1);
                        if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                            foundedStack.push_back(head->getId());
                            foundnessFactory[head->getId()]=1;
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _e){
            int V=starter->at(0);
            int W=starter->at(1);
            const std::vector<int>* tuples = &preachable_color_1_.getValuesVec({V});
            const std::vector<int>* tuplesU = &ureachable_color_1_.getValuesVec({V});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int C=tuple1->at(0);
                if(foundnessFactory[tuple1->getId()]>=0){
                    int C1 = C - 1;
                    Tuple* tuple3 = factory.find({V,C},_vertex_color);
                    if(tuple3!=NULL && !tuple3->isFalse()){
                        Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                        if(tuple4!=NULL && !tuple4->isFalse()){
                            Tuple* head = factory.find({C,W,V,C1},_aux_1);
                            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                foundedStack.push_back(head->getId());
                                foundnessFactory[head->getId()]=1;
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _vertex_color){
            int V=starter->at(0);
            int C=starter->at(1);
            int C1 = C - 1;
            Tuple* tuple2 = factory.find({C,V},_reachable_color);
            if(tuple2!=NULL && !tuple2->isFalse()){
                if(foundnessFactory[tuple2->getId()]>=0){
                    const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                    const std::vector<int>* tuplesU = &ue_0_.getValuesVec({V});
                    for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                        Tuple* tuple3 = NULL;
                        if(i<tuples->size()) tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                        else tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        int W=tuple3->at(1);
                        Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                        if(tuple4!=NULL && !tuple4->isFalse()){
                            Tuple* head = factory.find({C,W,V,C1},_aux_1);
                            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                foundedStack.push_back(head->getId());
                                foundnessFactory[head->getId()]=1;
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _gtnumber){
            int W=starter->at(0);
            int C1=starter->at(1);
            int C = C1 + 1;
            const std::vector<int>* tuples = &preachable_color_0_.getValuesVec({C});
            const std::vector<int>* tuplesU = &ureachable_color_0_.getValuesVec({C});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple2 = NULL;
                if(i<tuples->size()) tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int V=tuple2->at(1);
                if(foundnessFactory[tuple2->getId()]>=0){
                    Tuple* tuple3 = factory.find({V,W},_e);
                    if(tuple3!=NULL && !tuple3->isFalse()){
                        Tuple* tuple4 = factory.find({V,C},_vertex_color);
                        if(tuple4!=NULL && !tuple4->isFalse()){
                            Tuple* head = factory.find({C,W,V,C1},_aux_1);
                            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                foundedStack.push_back(head->getId());
                                foundnessFactory[head->getId()]=1;
                            }
                        }
                    }
                }
            }
        }
    }//close while 
}//close function
void unfoundedPropagatorForComponent0(std::vector<int>& literalToPropagate,Executor* executor){
    currentDecisionLevel=executor->getCurrentDecisionLevel();
    int unfoundedCount=0;
    for(int id : unfoundedSetForComponent0){
        Tuple* starter = factory.getTupleFromInternalID(id);
        if(starter->isFalse() || foundnessFactory[id]>=0) continue;
        if(eagerFacts.count(id)!=0){
            foundnessFactory[starter->getId()]=1;
            propFoundnessForComponent0(id);
            continue;
        }
        bool spFound=false;
        if(!spFound && starter->getPredicateName() == _reachable_color && foundnessFactory[starter->getId()]<0){
            int C=starter->at(0);
            int V=starter->at(1);
            Tuple* body = factory.find({C,V},_sup_0);
            if(body!=NULL && !body->isFalse()){
                sourcePointers0[starter->getId()]=body->getId();
                supportedLiterals0[body->getId()].push_back(starter->getId());
                foundnessFactory[starter->getId()]=1;
                propFoundnessForComponent0(starter->getId());
                spFound=true;
            }
        }
        if(!spFound && starter->getPredicateName() == _reachable_color && foundnessFactory[starter->getId()]<0){
            if(1 == starter->at(0)){
                int W=starter->at(1);
                Tuple* body = factory.find({1,W},_sup_1);
                if(body!=NULL && !body->isFalse()){
                    if(foundnessFactory[body->getId()]>=0){
                        sourcePointers0[starter->getId()]=body->getId();
                        supportedLiterals0[body->getId()].push_back(starter->getId());
                        foundnessFactory[starter->getId()]=1;
                        propFoundnessForComponent0(starter->getId());
                        spFound=true;
                    }
                }
            }
        }
        if(!spFound && starter->getPredicateName() == _sup_1 && foundnessFactory[starter->getId()]<0){
            if(1 == starter->at(0)){
                int W=starter->at(1);
                const std::vector<int>* tuples = &paux_0_0_.getValuesVec({W});
                const std::vector<int>* tuplesU = &uaux_0_0_.getValuesVec({W});
                for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){
                    Tuple* body = NULL;
                    if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));
                    else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    if(body!=NULL){
                        if(foundnessFactory[body->getId()]>=0){
                            sourcePointers0[starter->getId()]=body->getId();
                            supportedLiterals0[body->getId()].push_back(starter->getId());
                            foundnessFactory[starter->getId()]=1;
                            propFoundnessForComponent0(starter->getId());
                            spFound=true;
                        }
                    }
                }
            }
        }
        if(!spFound && starter->getPredicateName() == _reachable_color && foundnessFactory[starter->getId()]<0){
            int C=starter->at(0);
            int W=starter->at(1);
            Tuple* body = factory.find({C,W},_sup_2);
            if(body!=NULL && !body->isFalse()){
                if(foundnessFactory[body->getId()]>=0){
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].push_back(starter->getId());
                    foundnessFactory[starter->getId()]=1;
                    propFoundnessForComponent0(starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == _sup_2 && foundnessFactory[starter->getId()]<0){
            int C=starter->at(0);
            int W=starter->at(1);
            const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({C,W});
            const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({C,W});
            for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){
                Tuple* body = NULL;
                if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));
                else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(body!=NULL){
                    if(foundnessFactory[body->getId()]>=0){
                        sourcePointers0[starter->getId()]=body->getId();
                        supportedLiterals0[body->getId()].push_back(starter->getId());
                        foundnessFactory[starter->getId()]=1;
                        propFoundnessForComponent0(starter->getId());
                        spFound=true;
                    }
                }
            }
        }
        if(!spFound) unfoundedSetForComponent0[unfoundedCount++]=id;
        } //close unfounded for
        unfoundedSetForComponent0.resize(unfoundedCount);
        if(!unfoundedSetForComponent0.empty()){
            int conflictDetected=0;
            int currentExplainLevel = executor->getNextExplainLevel();
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            std::vector<int> propLiterals({currentDecisionLevel});
            std::vector<int> reasonStack;
            for(int lit : unfoundedSetForComponent0){
                Tuple* starter = factory.getTupleFromInternalID(lit);
                if(starter == NULL || starter->isFalse() || foundnessFactory[lit]>=0) continue;
                if(starter->getPredicateName()==_reachable_color){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    propLiterals.push_back(-lit);
                    int& visitedLevel = visitedExplainLiteral[lit];
                    if(visitedLevel!=currentExplainLevel){
                        visitedLevel = currentExplainLevel;
                        reasonStack.push_back(lit);
                    }
                    reasonForLiteral[-lit]=shared_reason;
                }
            }
            if(currentDecisionLevel > 0){
                while(!reasonStack.empty()){
                    int lit = reasonStack.back();
                    reasonStack.pop_back();
                    Tuple* starter = factory.getTupleFromInternalID(lit);
                    if(starter->getPredicateName() == _reachable_color){
                        int C=starter->at(0);
                        int V=starter->at(1);
                        Tuple* tuple = factory.find({C,V},_sup_0);
                        if(tuple!=NULL){
                            if(tuple->isFalse())
                                shared_reason.get()->insert(-tuple->getId());
                        }
                    }
                    if(starter->getPredicateName() == _reachable_color){
                        if(1 == starter->at(0)){
                            int W=starter->at(1);
                            Tuple* tuple = factory.find({1,W},_sup_1);
                            if(tuple!=NULL){
                                if(tuple->isFalse())
                                    shared_reason.get()->insert(-tuple->getId());
                                else if(foundnessFactory[tuple->getId()]<0){
                                    int& visitedLevel = visitedExplainLiteral[tuple->getId()];
                                    if(visitedLevel!=currentExplainLevel){
                                        visitedLevel = currentExplainLevel;
                                        reasonStack.push_back(tuple->getId());
                                    }
                                }
                            }
                        }
                    }
                    if(starter->getPredicateName() == _sup_1){
                        if(1 == starter->at(0)){
                            int W=starter->at(1);
                            const std::vector<int>* tuplesF = &faux_0_0_.getValuesVec({W});
                            for(unsigned i=0; i<tuplesF->size();i++){
                                Tuple* tuple =factory.getTupleFromInternalID(tuplesF->at(i));
                                if(tuple!=NULL){
                                    if(tuple->isFalse())
                                        shared_reason.get()->insert(-tuple->getId());
                                }
                            }
                        }
                    }
                    if(starter->getPredicateName() == _reachable_color){
                        int C=starter->at(0);
                        int W=starter->at(1);
                        Tuple* tuple = factory.find({C,W},_sup_2);
                        if(tuple!=NULL){
                            if(tuple->isFalse())
                                shared_reason.get()->insert(-tuple->getId());
                            else if(foundnessFactory[tuple->getId()]<0){
                                int& visitedLevel = visitedExplainLiteral[tuple->getId()];
                                if(visitedLevel!=currentExplainLevel){
                                    visitedLevel = currentExplainLevel;
                                    reasonStack.push_back(tuple->getId());
                                }
                            }
                        }
                    }
                    if(starter->getPredicateName() == _sup_2){
                        int C=starter->at(0);
                        int W=starter->at(1);
                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({C,W});
                        for(unsigned i=0; i<tuplesF->size();i++){
                            Tuple* tuple =factory.getTupleFromInternalID(tuplesF->at(i));
                            if(tuple!=NULL){
                                if(tuple->isFalse())
                                    shared_reason.get()->insert(-tuple->getId());
                            }
                        }
                    }
                }
            }
            for(int lit : unfoundedSetForComponent0){
                Tuple* starter = factory.getTupleFromInternalID(lit);
                if(starter == NULL || starter->isFalse() || foundnessFactory[lit]>=0) continue;
                foundnessFactory[lit]=1;
                auto oldSP = sourcePointers0.find(lit);
                if(oldSP!=sourcePointers0.end()){
                    supportedLiterals0[oldSP->second].push_back(lit);
                }
            }
            if(conflictDetected!=0) {
                executor->handleConflict(conflictDetected,literalToPropagate);
                if(currentDecisionLevel > 0) for(int i=1; i<propLiterals.size(); i++) reasonForLiteral[propLiterals[i]]->clear();
            }else if(propLiterals.size()>1){
                executor->executeProgramOnFacts(propLiterals,literalToPropagate,true);
            }
            unfoundedSetForComponent0.clear();
        }//close if empty unfounded set
    }// close unfoundedPropagatorForComponent
    void checkFoundness(){
        while(!falseLits.empty()){
            int starter = falseLits.back();
            int current = starter >= 0 ? starter : -starter;
            falseLits.pop_back();
            {
                std::vector<int>& supported = supportedLiterals0[current];
                int saving=0;
                for(int i=0;i < supported.size(); i++){
                    int lit = supported[i];
                    Tuple* removingLit = factory.getTupleFromInternalID(lit);
                    if(removingLit->isFalse()){supported[saving++]=supported[i]; continue;}
                    if(foundnessFactory[lit]>=0){
                        foundnessFactory[lit]=-1;
                        unfoundedSetForComponent0.push_back(lit);
                        falseLits.push_back(lit);
                    }//close if
                }//close for
                supported.resize(saving);
                if(current < supportedAux0.size()){
                    std::vector<int>& supAux = supportedAux0[current];
                    for(int lit : supAux){
                        Tuple* removingLit = factory.getTupleFromInternalID(lit);
                        if(!removingLit->isFalse() && foundnessFactory[lit]>=0){
                            foundnessFactory[lit]=-1;
                            unfoundedSetForComponent0.push_back(lit);
                            falseLits.push_back(lit);
                        }//close if
                    }//close for
                }
            }//close local scope
        }//close while
    }//close function
    void Executor::checkUnfoundedSets(std::vector<int>& literalsToPropagate,Executor* executor){
        checkFoundness();
        unfoundedPropagatorForComponent0(literalsToPropagate,executor);
    }
    void Executor::undefLiteralsReceived(){
        factory.setGenerated(true);
        undefinedLoaded=true;
        std::cout<<"Undef received "<<factory.size()<<std::endl;
        std::cout<<"Component 4"<<std::endl;
        std::cout<<"Component 3"<<std::endl;
        std::cout<<"Component 2"<<std::endl;
        std::cout<<"Component 1"<<std::endl;
        std::cout<<"Component 0"<<std::endl;
        //---------------------------------Recursive Component---------------------------------
        {
            std::vector<int> generationStack;
            {
                const std::vector<int>* tuples = &pfirst_.getValuesVec({});
                const std::vector<int>* tuplesU = &ufirst_.getValuesVec({});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple = NULL;
                    if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int C = tuple->at(0);
                    int V = tuple->at(1);
                    Tuple* saving2 = factory.addNewInternalTuple({C,V},_sup_0);
                    const auto& insertResult = saving2->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving2->getId());
                        insertUndef(insertResult);
                        Tuple* saving0 = factory.addNewInternalTuple({C,V},_reachable_color);
                        const auto& insertResult = saving0->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving0->getId());
                            insertUndef(insertResult);
                            generationStack.push_back(saving0->getId());
                        }
                    }
                }
            }
            while(!generationStack.empty()){
                Tuple* starter = factory.getTupleFromInternalID(generationStack.back());
                generationStack.pop_back();
                if(starter->getPredicateName() == _reachable_color){
                    if(starter->at(0) == 1){
                        int V = starter->at(1);
                        Tuple* tuple1 = factory.find({V,1},_vertex_color);
                        if(tuple1!=NULL && !tuple1->isFalse()){
                            const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                            const std::vector<int>* tuplesU = &ue_0_.getValuesVec({V});
                            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                                Tuple* tuple2 = NULL;
                                if(i<tuples->size()) tuple2=factory.getTupleFromInternalID(tuples->at(i));
                                else tuple2=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                if(tuple2->at(0) == V){
                                    int W = tuple2->at(1);
                                    Tuple* saving2 = factory.addNewInternalTuple({W,V},_aux_0);
                                    const auto& insertResult = saving2->setStatus(Undef);
                                    if(insertResult.second){
                                        factory.removeFromCollisionsList(saving2->getId());
                                        insertUndef(insertResult);
                                        if(supportedAux0.size() < factory.size())
                                            supportedAux0.resize(factory.size());
                                        supportedAux0[starter->getId()].push_back(saving2->getId());
                                        Tuple* saving1 = factory.addNewInternalTuple({1,W},_sup_1);
                                        const auto& insertResult = saving1->setStatus(Undef);
                                        if(insertResult.second){
                                            factory.removeFromCollisionsList(saving1->getId());
                                            insertUndef(insertResult);
                                            Tuple* saving0 = factory.addNewInternalTuple({1,W},_reachable_color);
                                            const auto& insertResult = saving0->setStatus(Undef);
                                            if(insertResult.second){
                                                factory.removeFromCollisionsList(saving0->getId());
                                                insertUndef(insertResult);
                                                generationStack.push_back(saving0->getId());
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if(starter->getPredicateName() == _reachable_color){
                    int C = starter->at(0);
                    int V = starter->at(1);
                    int C1 = C - 1;
                    Tuple* tuple2 = factory.find({V,C},_vertex_color);
                    if(tuple2!=NULL && !tuple2->isFalse()){
                        const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                        const std::vector<int>* tuplesU = &ue_0_.getValuesVec({V});
                        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                            Tuple* tuple3 = NULL;
                            if(i<tuples->size()) tuple3=factory.getTupleFromInternalID(tuples->at(i));
                            else tuple3=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                            if(tuple3->at(0) == V){
                                int W = tuple3->at(1);
                                Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                                if(tuple4!=NULL && !tuple4->isFalse()){
                                    Tuple* saving2 = factory.addNewInternalTuple({C,W,V,C1},_aux_1);
                                    const auto& insertResult = saving2->setStatus(Undef);
                                    if(insertResult.second){
                                        factory.removeFromCollisionsList(saving2->getId());
                                        insertUndef(insertResult);
                                        if(supportedAux0.size() < factory.size())
                                            supportedAux0.resize(factory.size());
                                        supportedAux0[starter->getId()].push_back(saving2->getId());
                                        Tuple* saving1 = factory.addNewInternalTuple({C,W},_sup_2);
                                        const auto& insertResult = saving1->setStatus(Undef);
                                        if(insertResult.second){
                                            factory.removeFromCollisionsList(saving1->getId());
                                            insertUndef(insertResult);
                                            Tuple* saving0 = factory.addNewInternalTuple({C,W},_reachable_color);
                                            const auto& insertResult = saving0->setStatus(Undef);
                                            if(insertResult.second){
                                                factory.removeFromCollisionsList(saving0->getId());
                                                insertUndef(insertResult);
                                                generationStack.push_back(saving0->getId());
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }//close local scope
        //---------------------------------Recursive Component---------------------------------
        foundnessFactory.resize(factory.size());
        {
            const std::vector<int>* tuples = &preachable_color_.getValuesVec({});
            const std::vector<int>* tuplesU = &ureachable_color_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent0.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &psup_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &usup_1_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent0.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &paux_0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaux_0_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent0.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &preachable_color_.getValuesVec({});
            const std::vector<int>* tuplesU = &ureachable_color_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent0.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &psup_2_.getValuesVec({});
            const std::vector<int>* tuplesU = &usup_2_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent0.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &paux_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaux_1_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent0.push_back(lit);}
            }
        }
        supportedLiterals0.resize(factory.size());
        std::cout<<"Generated"<<factory.size()<<std::endl;
        buildingReasonStack.reserve(2*factory.size());
        conflictReason.reserve(factory.size());
        visitedExplainLiteral.resize(2*factory.size());
        explainLevel=1;
    }
    inline void Executor::addedVarName(int var, const std::string & atom) {
        std::vector<int> terms;
        int predicate = parseTuple(atom,terms);
        Tuple* t = factory.addNewTuple(terms,predicate,var);
    }
    void Executor::clearPropagations() {
        propagatedLiteralsAndReasons.clear();
    }
    void Executor::clear() {
        failedConstraints.clear();
    }
    void Executor::init() {
        stringToUniqueStringPointer["aux_0"] = _aux_0;
        stringToUniqueStringPointer["aux_1"] = _aux_1;
        stringToUniqueStringPointer["e"] = _e;
        stringToUniqueStringPointer["first"] = _first;
        stringToUniqueStringPointer["gtnumber"] = _gtnumber;
        stringToUniqueStringPointer["reachable_color"] = _reachable_color;
        stringToUniqueStringPointer["sup_0"] = _sup_0;
        stringToUniqueStringPointer["sup_1"] = _sup_1;
        stringToUniqueStringPointer["sup_2"] = _sup_2;
        stringToUniqueStringPointer["vertex_color"] = _vertex_color;
        Executor::predicateIds.push_back("aux_0");
        factory.addPredicate();
        Executor::predicateIds.push_back("aux_1");
        factory.addPredicate();
        Executor::predicateIds.push_back("e");
        factory.addPredicate();
        Executor::predicateIds.push_back("first");
        factory.addPredicate();
        Executor::predicateIds.push_back("gtnumber");
        factory.addPredicate();
        Executor::predicateIds.push_back("reachable_color");
        factory.addPredicate();
        Executor::predicateIds.push_back("sup_0");
        factory.addPredicate();
        Executor::predicateIds.push_back("sup_1");
        factory.addPredicate();
        Executor::predicateIds.push_back("sup_2");
        factory.addPredicate();
        Executor::predicateIds.push_back("vertex_color");
        factory.addPredicate();
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
        for(int internalId : preachable_color_.getValuesVec({})){
            Tuple* tuple = factory.getTupleFromInternalID(internalId);
            std::string tupleToString = tuple->size() > 0 ? "reachable_color(" : "reachable_color";
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
            std::vector<int>& level=levelToIntLiterals[currentDecisionLevel];
            unsigned size = level.size();
            for(int i=0;i<size;i++){
                int var = level[i];
                int uVar = var>0 ? var : -var;
                Tuple* tuple = factory.getTupleFromInternalID(uVar);
                reasonForLiteral[var].get()->clear();
                const auto& insertResult = tuple->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(tuple->getId());
                    insertUndef(insertResult);
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
        if(!factory.isGenerated()) {
            undefLiteralsReceived();
                {
                    {
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &psup_0_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &usup_0_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _sup_0 && !tupleUNegated)
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
                                int V = tuple0->at(1);
                                Tuple negativeTuple({C,V},_reachable_color);
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
                                            if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    const std::vector<int>* trueHeads = &psup_0_.getValuesVec({});
                    for(unsigned i = 0;i < trueHeads->size(); i++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                        if(eagerFacts.count(currentHead->getId())!=0) continue;
                        int C = currentHead->at(0);
                        int V = currentHead->at(1);
                        Tuple* currentBody = factory.find({C,V}, _first);
                        if(!currentBody->isUndef() && !currentBody->isTrue()){
                            propagatedLiterals.push_back(1);
                            return;
                        }else if(currentBody->isUndef()){
                            propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    const std::vector<int>* falseHeads = &fsup_0_.getValuesVec({});
                    for(unsigned i = 0;i < falseHeads->size(); i++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                        int C = currentHead->at(0);
                        int V = currentHead->at(1);
                        Tuple* currentBody = factory.find({C,V}, _first);
                        if(currentBody->isTrue()){
                            propagatedLiterals.push_back(1);
                            return;
                        }else if(currentBody->isUndef()){
                            propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    const std::vector<int>* undefHeads = &usup_0_.getValuesVec({});
                    for(unsigned i = 0; i < undefHeads->size();){
                        const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                        int C = currentHead->at(0);
                        int V = currentHead->at(1);
                        const Tuple* currentBody = factory.find({C, V}, _first);
                        if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                            propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else if(currentBody!=NULL && currentBody->isTrue())
                            propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else i++;
                    }
                }
                {
                    {
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &psup_1_0_.getValuesVec({1});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &usup_1_0_.getValuesVec({1});
                        else if(tupleU->getPredicateName() == _sup_1 && !tupleUNegated)
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
                                if(tupleU->at(0) == 1)
                                    tuple0 = tupleU;
                            }
                            if(tuple0!=NULL){
                                if(tuple0->at(0)==1){
                                    int W = tuple0->at(1);
                                    Tuple negativeTuple({1,W},_reachable_color);
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
                                                if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                            else internalProps.push_back({tupleU,tupleUNegated});
                                        }else{
                                            propagatedLiterals.push_back(1);
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
                        const std::vector<int>* tuples = &psup_2_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &usup_2_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _sup_2 && !tupleUNegated)
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
                                int W = tuple0->at(1);
                                Tuple negativeTuple({C,W},_reachable_color);
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
                                            if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &pvertex_color_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uvertex_color_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _vertex_color && !tupleUNegated)
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
                                int V = tuple0->at(0);
                                int C = tuple0->at(1);
                                Tuple negativeTuple({C,V},_reachable_color);
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
                                            if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &preachable_color_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ureachable_color_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _reachable_color && !tupleUNegated)
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
                                int X0 = tuple0->at(0);
                                int X1 = tuple0->at(1);
                                Tuple negativeTuple({X0,X1},_sup_0);
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
                                            if(tupleU->getPredicateName() != _sup_0 || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    Tuple negativeTuple({X0,X1},_sup_1);
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
                                                if(tupleU->getPredicateName() != _sup_1 || !tupleUNegated || !(*tupleU == *tuple2))
                                                tuple2=NULL;
                                            }
                                        }
                                    }
                                    if(tuple2!=NULL){
                                        Tuple negativeTuple({X0,X1},_sup_2);
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
                                                    if(tupleU->getPredicateName() != _sup_2 || !tupleUNegated || !(*tupleU == *tuple3))
                                                    tuple3=NULL;
                                                }
                                            }
                                        }
                                        if(tuple3!=NULL){
                                            if(tupleU != NULL){
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &preachable_color_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ureachable_color_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _reachable_color && !tupleUNegated)
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
                                int V = tuple0->at(1);
                                int C1 = C - 1;
                                const Tuple* tuple2 = factory.find({V,C},_vertex_color);
                                if(tuple2!=NULL){
                                    if(tuple2->isFalse())
                                    tuple2=NULL;
                                    else if(tuple2->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple2;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &ue_0_.getValuesVec({V});
                                    else if(tupleU->getPredicateName() == _e && !tupleUNegated)
                                        undeRepeated.push_back(tupleU);
                                    for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                        if(tuplesU!=&EMPTY_TUPLES_VEC)
                                            tupleU = NULL;
                                        const Tuple* tuple3 = NULL;
                                        if(i<tuples->size())
                                            tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                        else if(i<tuples->size()+tuplesU->size()){
                                            tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                            tupleUNegated=false;
                                        }else if(!undeRepeated.empty()){
                                            if(tupleU->at(0) == V)
                                                tuple3 = tupleU;
                                        }
                                        if(tuple3!=NULL){
                                            int W = tuple3->at(1);
                                            const Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                                            if(tuple4!=NULL){
                                                if(tuple4->isFalse())
                                                tuple4=NULL;
                                                else if(tuple4->isUndef()){
                                                    if(tupleU == NULL){
                                                        tupleU = tuple4;
                                                        tupleUNegated=false;
                                                    }else{
                                                        if(tupleU->getPredicateName() != _gtnumber || tupleUNegated || !(*tupleU == *tuple4))
                                                        tuple4=NULL;
                                                    }
                                                }
                                            }
                                            if(tuple4!=NULL){
                                                Tuple negativeTuple({C,W,V,C1},_aux_1);
                                                const Tuple* tuple5 = factory.find(negativeTuple);
                                                if(tuple5 == NULL)
                                                    tuple5 = &negativeTuple;
                                                else{
                                                    if(tuple5->isTrue())
                                                        tuple5 = NULL;
                                                    else if(tuple5->isUndef()){
                                                        if(tupleU == NULL){
                                                            tupleU = tuple5;
                                                            tupleUNegated=true;
                                                        }else{
                                                            if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple5))
                                                            tuple5=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple5!=NULL){
                                                    if(tupleU != NULL){
                                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &paux_1_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                int W = tuple0->at(1);
                                int V = tuple0->at(2);
                                int C1 = tuple0->at(3);
                                Tuple negativeTuple({W,C1},_gtnumber);
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
                                            if(tupleU->getPredicateName() != _gtnumber || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &paux_1_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                int W = tuple0->at(1);
                                int V = tuple0->at(2);
                                int C1 = tuple0->at(3);
                                Tuple negativeTuple({V,C},_vertex_color);
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
                                            if(tupleU->getPredicateName() != _vertex_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &paux_1_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                int W = tuple0->at(1);
                                int V = tuple0->at(2);
                                int C1 = tuple0->at(3);
                                Tuple negativeTuple({V,W},_e);
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
                                            if(tupleU->getPredicateName() != _e || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &paux_1_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_.getValuesVec({});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                int W = tuple0->at(1);
                                int V = tuple0->at(2);
                                int C1 = tuple0->at(3);
                                Tuple negativeTuple({C,V},_reachable_color);
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
                                            if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* tuples = &preachable_color_0_.getValuesVec({1});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ureachable_color_0_.getValuesVec({1});
                        else if(tupleU->getPredicateName() == _reachable_color && !tupleUNegated)
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
                                if(tupleU->at(0) == 1)
                                    tuple0 = tupleU;
                            }
                            if(tuple0!=NULL){
                                if(tuple0->at(0)==1){
                                    int V = tuple0->at(1);
                                    const Tuple* tuple1 = factory.find({V,1},_vertex_color);
                                    if(tuple1!=NULL){
                                        if(tuple1->isFalse())
                                        tuple1=NULL;
                                        else if(tuple1->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple1;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                        std::vector<const Tuple*> undeRepeated;
                                        if(tupleU == NULL)
                                            tuplesU = &ue_0_.getValuesVec({V});
                                        else if(tupleU->getPredicateName() == _e && !tupleUNegated)
                                            undeRepeated.push_back(tupleU);
                                        for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                            if(tuplesU!=&EMPTY_TUPLES_VEC)
                                                tupleU = NULL;
                                            const Tuple* tuple2 = NULL;
                                            if(i<tuples->size())
                                                tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                                            else if(i<tuples->size()+tuplesU->size()){
                                                tupleU = tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                tupleUNegated=false;
                                            }else if(!undeRepeated.empty()){
                                                if(tupleU->at(0) == V)
                                                    tuple2 = tupleU;
                                            }
                                            if(tuple2!=NULL){
                                                int W = tuple2->at(1);
                                                Tuple negativeTuple({W,V},_aux_0);
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
                                                            if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
                                                            tuple3=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple3!=NULL){
                                                    if(tupleU != NULL){
                                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        else if(tupleU->getPredicateName() == _aux_0 && !tupleUNegated)
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
                                int W = tuple0->at(0);
                                int V = tuple0->at(1);
                                Tuple negativeTuple({V,1},_vertex_color);
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
                                            if(tupleU->getPredicateName() != _vertex_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        else if(tupleU->getPredicateName() == _aux_0 && !tupleUNegated)
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
                                int W = tuple0->at(0);
                                int V = tuple0->at(1);
                                Tuple negativeTuple({V,W},_e);
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
                                            if(tupleU->getPredicateName() != _e || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                        else if(tupleU->getPredicateName() == _aux_0 && !tupleUNegated)
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
                                int W = tuple0->at(0);
                                int V = tuple0->at(1);
                                Tuple negativeTuple({1,V},_reachable_color);
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
                                            if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
                                            tuple1=NULL;
                                        }
                                    }
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    const std::vector<int>* trueHeads = &psup_1_.getValuesVec({});
                    for(unsigned i = 0;i < trueHeads->size(); i++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                        if(eagerFacts.count(currentHead->getId())!=0) continue;
                        if(currentHead->at(0) == 1){
                            int W = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_0_0_.getValuesVec({W});
                            const std::vector<int>* tuplesU = &uaux_0_0_.getValuesVec({W});
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
                    }
                    const std::vector<int>* falseHeads = &fsup_1_.getValuesVec({});
                    for(unsigned i = 0;i < falseHeads->size(); i++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                        if(currentHead->at(0) == 1){
                            int W = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_0_0_.getValuesVec({W});
                            const std::vector<int>* tuplesU = &uaux_0_0_.getValuesVec({W});
                            if(tuples->size()>0){
                                propagatedLiterals.push_back(1);
                                return;
                            }else{
                                while(!tuplesU->empty()){
                                    propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                }
                            }
                        }
                    }
                    const std::vector<int>* undefHeads = &usup_1_.getValuesVec({});
                    for(unsigned i = 0; i < undefHeads->size();){
                        const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                        if(currentHead->at(0) == 1){
                            int W = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_0_0_.getValuesVec({W});
                            const std::vector<int>* tuplesU = &uaux_0_0_.getValuesVec({W});
                            if(tuples->size() > 0)
                                propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else if(tuplesU->size()==0)
                                propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else i++;
                        }
                    }
                }
                {
                    const std::vector<int>* trueHeads = &psup_2_.getValuesVec({});
                    for(unsigned i = 0;i < trueHeads->size(); i++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                        if(eagerFacts.count(currentHead->getId())!=0) continue;
                        int C = currentHead->at(0);
                        int W = currentHead->at(1);
                        const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({C, W});
                        const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({C, W});
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
                    const std::vector<int>* falseHeads = &fsup_2_.getValuesVec({});
                    for(unsigned i = 0;i < falseHeads->size(); i++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                        int C = currentHead->at(0);
                        int W = currentHead->at(1);
                        const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({C, W});
                        const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({C, W});
                        if(tuples->size()>0){
                            propagatedLiterals.push_back(1);
                            return;
                        }else{
                            while(!tuplesU->empty()){
                                propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }
                    const std::vector<int>* undefHeads = &usup_2_.getValuesVec({});
                    for(unsigned i = 0; i < undefHeads->size();){
                        const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                        int C = currentHead->at(0);
                        int W = currentHead->at(1);
                        const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({C, W});
                        const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({C, W});
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
                {
                    if(starter.getPredicateName() == _reachable_color && startVar < 0){
                        int C = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({C,V},_sup_0);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _sup_0 || tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _sup_0 && startVar > 0){
                        int C = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({C,V},_reachable_color);
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
                                    if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                if(starter.getPredicateName() == _first){
                    int C = starter.at(0);
                    int V = starter.at(1);
                    Tuple* head = factory.find({C,V}, _sup_0);
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
                        if(head != NULL && head->isTrue()){
                            if(currentDecisionLevel>0){
                                int it = head->getId();
                                shared_reason.get()->insert(startVar);
                                reasonForLiteral[-it]=shared_reason;
                                handleConflict(-it, propagatedLiterals);
                            }else propagatedLiterals.push_back(1);
                            return;
                        }else{
                            if(head != NULL && head->isUndef()){
                                if(currentDecisionLevel>0){
                                    int it = head->getId();
                                    shared_reason.get()->insert(startVar);
                                    auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                                    if(!itReason.second && itReason.first->second.get()->empty())
                                        itReason.first->second=shared_reason;
                                }
                                propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }
                        }
                    }
                }else if(starter.getPredicateName() == _sup_0){
                    int C = starter.at(0);
                    int V = starter.at(1);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    Tuple* currentBody = factory.find({C,V}, _first);
                    if(startVar > 0){
                        if(currentBody->isFalse()){
                            if(currentDecisionLevel>0){
                                int it = currentBody->getId();
                                shared_reason.get()->insert(startVar);
                                reasonForLiteral[it]=shared_reason;
                                handleConflict(it, propagatedLiterals);
                            } else propagatedLiterals.push_back(1);
                            return;
                        }else if(currentBody->isUndef()){
                            if(currentDecisionLevel>0){
                                int it = currentBody->getId();
                                shared_reason.get()->insert(startVar);
                                auto itReason = reasonForLiteral.emplace(it,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                            }
                            propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }else{
                        if(currentBody->isTrue()){
                            if(currentDecisionLevel>0){
                                int it = currentBody->getId();
                                shared_reason.get()->insert(startVar);
                                reasonForLiteral[-it]=shared_reason;
                                handleConflict(-it, propagatedLiterals);
                            }else propagatedLiterals.push_back(1);
                            return;
                        }else if(currentBody->isUndef()){
                            if(currentDecisionLevel>0){
                                int it = currentBody->getId();
                                shared_reason.get()->insert(startVar);
                                auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                            }
                            propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }
                {
                    if(starter.getPredicateName() == _reachable_color && startVar < 0){
                        if(1 == starter[0]){
                            int W = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({1,W},_sup_1);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _sup_1 || tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _sup_1 && startVar > 0){
                        if(1 == starter[0]){
                            int W = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({1,W},_reachable_color);
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
                                        if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                }
                if(starter.getPredicateName() == _aux_0){
                    int W = starter.at(0);
                    int V = starter.at(1);
                    Tuple* head = factory.find({1,W}, _sup_1);
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
                        const std::vector<int>* tuples = &paux_0_0_.getValuesVec({W});
                        const std::vector<int>* tuplesU = &uaux_0_0_.getValuesVec({W});
                        if(head != NULL && head->isTrue()){
                            if(tuples->size() == 0 && tuplesU->size() == 0){
                                if(currentDecisionLevel>0){
                                    int itHead = head->getId();
                                    const std::vector<int>* tuplesF = &faux_0_0_.getValuesVec({W});
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
                                    const std::vector<int>* tuplesF = &faux_0_0_.getValuesVec({W});
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
                                    const std::vector<int>* tuplesF = &faux_0_0_.getValuesVec({W});
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
                }else if(starter.getPredicateName() == _sup_1){
                    if(starter.at(0) == 1){
                        int W = starter.at(1);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        const std::vector<int>* tuples = &paux_0_0_.getValuesVec({W});
                        const std::vector<int>* tuplesU = &uaux_0_0_.getValuesVec({W});
                        if(startVar > 0){
                            if(tuples->size()==0){
                                if(tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        const std::vector<int>* tuplesF = &faux_0_0_.getValuesVec({W});
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
                                        const std::vector<int>* tuplesF = &faux_0_0_.getValuesVec({W});
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
                }
                {
                    if(starter.getPredicateName() == _reachable_color && startVar < 0){
                        if(1 == starter[0]){
                            int V = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_0_1_.getValuesVec({V});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_0_1_.getValuesVec({V});
                            else if(tupleU->getPredicateName() == _aux_0 && !tupleUNegated)
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
                                    if(tupleU->at(1) == V)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int W = tuple1->at(0);
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    }
                    if(starter.getPredicateName() == _aux_0 && startVar > 0){
                        int W = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({1,V},_reachable_color);
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
                                    if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _e && startVar < 0){
                        int V = starter[0];
                        int W = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({W,V},_aux_0);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _aux_0 || tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_0 && startVar > 0){
                        int W = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({V,W},_e);
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
                                    if(tupleU->getPredicateName() != _e || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _vertex_color && startVar < 0){
                        int V = starter[0];
                        if(1 == starter[1]){
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_0_1_.getValuesVec({V});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_0_1_.getValuesVec({V});
                            else if(tupleU->getPredicateName() == _aux_0 && !tupleUNegated)
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
                                    if(tupleU->at(1) == V)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int W = tuple1->at(0);
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    }
                    if(starter.getPredicateName() == _aux_0 && startVar > 0){
                        int W = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({V,1},_vertex_color);
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
                                    if(tupleU->getPredicateName() != _vertex_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_0 && startVar < 0){
                        int W = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({1,V},_reachable_color);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            const Tuple* tuple2 = factory.find({V,W},_e);
                            if(tuple2!=NULL){
                                if(tuple2->isFalse())
                                tuple2=NULL;
                                else if(tuple2->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple2;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _e || tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                const Tuple* tuple3 = factory.find({V,1},_vertex_color);
                                if(tuple3!=NULL){
                                    if(tuple3->isFalse())
                                    tuple3=NULL;
                                    else if(tuple3->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple3;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple3))
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
                                                shared_reason.get()->insert(it*1);
                                            }
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                        }
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _vertex_color && startVar > 0){
                        int V = starter[0];
                        if(1 == starter[1]){
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({1,V},_reachable_color);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ue_0_.getValuesVec({V});
                                else if(tupleU->getPredicateName() == _e && !tupleUNegated)
                                    undeRepeated.push_back(tupleU);
                                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                    if(tuplesU!=&EMPTY_TUPLES_VEC)
                                        tupleU = NULL;
                                    const Tuple* tuple2 = NULL;
                                    if(i<tuples->size())
                                        tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(0) == V)
                                            tuple2 = tupleU;
                                    }
                                    if(tuple2!=NULL){
                                        int W = tuple2->at(1);
                                        Tuple negativeTuple({W,V},_aux_0);
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
                                                    if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    if(starter.getPredicateName() == _e && startVar > 0){
                        int V = starter[0];
                        int W = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({1,V},_reachable_color);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            const Tuple* tuple2 = factory.find({V,1},_vertex_color);
                            if(tuple2!=NULL){
                                if(tuple2->isFalse())
                                tuple2=NULL;
                                else if(tuple2->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple2;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({W,V},_aux_0);
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
                                            if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _reachable_color && startVar > 0){
                        if(1 == starter[0]){
                            int V = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({V,1},_vertex_color);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ue_0_.getValuesVec({V});
                                else if(tupleU->getPredicateName() == _e && !tupleUNegated)
                                    undeRepeated.push_back(tupleU);
                                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                    if(tuplesU!=&EMPTY_TUPLES_VEC)
                                        tupleU = NULL;
                                    const Tuple* tuple2 = NULL;
                                    if(i<tuples->size())
                                        tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(0) == V)
                                            tuple2 = tupleU;
                                    }
                                    if(tuple2!=NULL){
                                        int W = tuple2->at(1);
                                        Tuple negativeTuple({W,V},_aux_0);
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
                                                    if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }
                {
                    if(starter.getPredicateName() == _reachable_color && startVar < 0){
                        int C = starter[0];
                        int W = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({C,W},_sup_2);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _sup_2 || tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _sup_2 && startVar > 0){
                        int C = starter[0];
                        int W = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({C,W},_reachable_color);
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
                                    if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                if(starter.getPredicateName() == _aux_1){
                    int C = starter.at(0);
                    int W = starter.at(1);
                    int V = starter.at(2);
                    int C1 = starter.at(3);
                    Tuple* head = factory.find({C,W}, _sup_2);
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
                        const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({C, W});
                        const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({C, W});
                        if(head != NULL && head->isTrue()){
                            if(tuples->size() == 0 && tuplesU->size() == 0){
                                if(currentDecisionLevel>0){
                                    int itHead = head->getId();
                                    const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({C, W});
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
                                    const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({C, W});
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
                                    const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({C, W});
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
                }else if(starter.getPredicateName() == _sup_2){
                    int C = starter.at(0);
                    int W = starter.at(1);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({C,W});
                    const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({C,W});
                    if(startVar > 0){
                        if(tuples->size()==0){
                            if(tuplesU->size() == 0){
                                if(currentDecisionLevel>0){
                                    const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({C,W});
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
                                    const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({C,W});
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
                    if(starter.getPredicateName() == _reachable_color && startVar < 0){
                        int C = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &paux_1_0_2_.getValuesVec({C,V});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_0_2_.getValuesVec({C,V});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                if(tupleU->at(0) == C && tupleU->at(2) == V)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int W = tuple1->at(1);
                                int C1 = tuple1->at(3);
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
                                    if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_1 && startVar > 0){
                        int C = starter[0];
                        int W = starter[1];
                        int V = starter[2];
                        int C1 = starter[3];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({C,V},_reachable_color);
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
                                    if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _e && startVar < 0){
                        int V = starter[0];
                        int W = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &paux_1_1_2_.getValuesVec({W,V});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_1_2_.getValuesVec({W,V});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                if(tupleU->at(1) == W && tupleU->at(2) == V)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int C = tuple1->at(0);
                                int C1 = tuple1->at(3);
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
                                    if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_1 && startVar > 0){
                        int C = starter[0];
                        int W = starter[1];
                        int V = starter[2];
                        int C1 = starter[3];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({V,W},_e);
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
                                    if(tupleU->getPredicateName() != _e || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _vertex_color && startVar < 0){
                        int V = starter[0];
                        int C = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &paux_1_0_2_.getValuesVec({C,V});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_0_2_.getValuesVec({C,V});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                if(tupleU->at(0) == C && tupleU->at(2) == V)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int W = tuple1->at(1);
                                int C1 = tuple1->at(3);
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
                                    if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_1 && startVar > 0){
                        int C = starter[0];
                        int W = starter[1];
                        int V = starter[2];
                        int C1 = starter[3];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({V,C},_vertex_color);
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
                                    if(tupleU->getPredicateName() != _vertex_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _gtnumber && startVar < 0){
                        int W = starter[0];
                        int C1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &paux_1_1_3_.getValuesVec({W,C1});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_1_1_3_.getValuesVec({W,C1});
                        else if(tupleU->getPredicateName() == _aux_1 && !tupleUNegated)
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
                                if(tupleU->at(1) == W && tupleU->at(3) == C1)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int C = tuple1->at(0);
                                int V = tuple1->at(2);
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
                                    if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_1 && startVar > 0){
                        int C = starter[0];
                        int W = starter[1];
                        int V = starter[2];
                        int C1 = starter[3];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({W,C1},_gtnumber);
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
                                    if(tupleU->getPredicateName() != _gtnumber || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _aux_1 && startVar < 0){
                        int C = starter[0];
                        int W = starter[1];
                        int V = starter[2];
                        int C1 = starter[3];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        if(C1 == C - 1){
                            const Tuple* tuple2 = factory.find({C,V},_reachable_color);
                            if(tuple2!=NULL){
                                if(tuple2->isFalse())
                                tuple2=NULL;
                                else if(tuple2->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple2;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                const Tuple* tuple3 = factory.find({V,W},_e);
                                if(tuple3!=NULL){
                                    if(tuple3->isFalse())
                                    tuple3=NULL;
                                    else if(tuple3->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple3;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != _e || tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    const Tuple* tuple4 = factory.find({V,C},_vertex_color);
                                    if(tuple4!=NULL){
                                        if(tuple4->isFalse())
                                        tuple4=NULL;
                                        else if(tuple4->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple4;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple4))
                                                tuple4=NULL;
                                            }
                                        }
                                    }
                                    if(tuple4!=NULL){
                                        const Tuple* tuple5 = factory.find({W,C1},_gtnumber);
                                        if(tuple5!=NULL){
                                            if(tuple5->isFalse())
                                            tuple5=NULL;
                                            else if(tuple5->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple5;
                                                    tupleUNegated=false;
                                                }else{
                                                    if(tupleU->getPredicateName() != _gtnumber || tupleUNegated || !(*tupleU == *tuple5))
                                                    tuple5=NULL;
                                                }
                                            }
                                        }
                                        if(tuple5!=NULL){
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
                                                    if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                        int it = tuple5->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                    if(!itReason.second && itReason.first->second.get()->empty())
                                                        itReason.first->second=shared_reason;
                                                }
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                                if(currentDecisionLevel>0){
                                                    if(tuple2!=NULL){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple3!=NULL){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple4!=NULL){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple5!=NULL){
                                                        int it = tuple5->getId();
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
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                    if(starter.getPredicateName() == _gtnumber && startVar > 0){
                        int W = starter[0];
                        int C1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        int C = C1 + 1;
                        const std::vector<int>* tuples = &preachable_color_0_.getValuesVec({C});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ureachable_color_0_.getValuesVec({C});
                        else if(tupleU->getPredicateName() == _reachable_color && !tupleUNegated)
                            undeRepeated.push_back(tupleU);
                        for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                            if(tuplesU!=&EMPTY_TUPLES_VEC)
                                tupleU = NULL;
                            const Tuple* tuple2 = NULL;
                            if(i<tuples->size())
                                tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == C)
                                    tuple2 = tupleU;
                            }
                            if(tuple2!=NULL){
                                int V = tuple2->at(1);
                                const Tuple* tuple3 = factory.find({V,W},_e);
                                if(tuple3!=NULL){
                                    if(tuple3->isFalse())
                                    tuple3=NULL;
                                    else if(tuple3->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple3;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != _e || tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    const Tuple* tuple4 = factory.find({V,C},_vertex_color);
                                    if(tuple4!=NULL){
                                        if(tuple4->isFalse())
                                        tuple4=NULL;
                                        else if(tuple4->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple4;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple4))
                                                tuple4=NULL;
                                            }
                                        }
                                    }
                                    if(tuple4!=NULL){
                                        Tuple negativeTuple({C,W,V,C1},_aux_1);
                                        const Tuple* tuple5 = factory.find(negativeTuple);
                                        if(tuple5 == NULL)
                                            tuple5 = &negativeTuple;
                                        else{
                                            if(tuple5->isTrue())
                                                tuple5 = NULL;
                                            else if(tuple5->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple5;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple5))
                                                    tuple5=NULL;
                                                }
                                            }
                                        }
                                        if(tuple5!=NULL){
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
                                                    if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                        int it = tuple5->getId();
                                                        shared_reason.get()->insert(it*-1);
                                                    }
                                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                    if(!itReason.second && itReason.first->second.get()->empty())
                                                        itReason.first->second=shared_reason;
                                                }
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                                if(currentDecisionLevel>0){
                                                    if(tuple2!=NULL){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple3!=NULL){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple4!=NULL){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple5!=NULL){
                                                        int it = tuple5->getId();
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
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                    if(starter.getPredicateName() == _vertex_color && startVar > 0){
                        int V = starter[0];
                        int C = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        int C1 = C - 1;
                        const Tuple* tuple2 = factory.find({C,V},_reachable_color);
                        if(tuple2!=NULL){
                            if(tuple2->isFalse())
                            tuple2=NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ue_0_.getValuesVec({V});
                            else if(tupleU->getPredicateName() == _e && !tupleUNegated)
                                undeRepeated.push_back(tupleU);
                            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                if(tuplesU!=&EMPTY_TUPLES_VEC)
                                    tupleU = NULL;
                                const Tuple* tuple3 = NULL;
                                if(i<tuples->size())
                                    tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                else if(i<tuples->size()+tuplesU->size()){
                                    tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                    tupleUNegated=false;
                                }else if(!undeRepeated.empty()){
                                    if(tupleU->at(0) == V)
                                        tuple3 = tupleU;
                                }
                                if(tuple3!=NULL){
                                    int W = tuple3->at(1);
                                    const Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                                    if(tuple4!=NULL){
                                        if(tuple4->isFalse())
                                        tuple4=NULL;
                                        else if(tuple4->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple4;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _gtnumber || tupleUNegated || !(*tupleU == *tuple4))
                                                tuple4=NULL;
                                            }
                                        }
                                    }
                                    if(tuple4!=NULL){
                                        Tuple negativeTuple({C,W,V,C1},_aux_1);
                                        const Tuple* tuple5 = factory.find(negativeTuple);
                                        if(tuple5 == NULL)
                                            tuple5 = &negativeTuple;
                                        else{
                                            if(tuple5->isTrue())
                                                tuple5 = NULL;
                                            else if(tuple5->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple5;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple5))
                                                    tuple5=NULL;
                                                }
                                            }
                                        }
                                        if(tuple5!=NULL){
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
                                                    if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                        int it = tuple5->getId();
                                                        shared_reason.get()->insert(it*-1);
                                                    }
                                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                    if(!itReason.second && itReason.first->second.get()->empty())
                                                        itReason.first->second=shared_reason;
                                                }
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                                if(currentDecisionLevel>0){
                                                    if(tuple2!=NULL){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple3!=NULL){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple4!=NULL){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple5!=NULL){
                                                        int it = tuple5->getId();
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
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                    if(starter.getPredicateName() == _e && startVar > 0){
                        int V = starter[0];
                        int W = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const std::vector<int>* tuples = &preachable_color_1_.getValuesVec({V});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ureachable_color_1_.getValuesVec({V});
                        else if(tupleU->getPredicateName() == _reachable_color && !tupleUNegated)
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
                                if(tupleU->at(1) == V)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int C = tuple1->at(0);
                                int C1 = C - 1;
                                const Tuple* tuple3 = factory.find({V,C},_vertex_color);
                                if(tuple3!=NULL){
                                    if(tuple3->isFalse())
                                    tuple3=NULL;
                                    else if(tuple3->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple3;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    const Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                                    if(tuple4!=NULL){
                                        if(tuple4->isFalse())
                                        tuple4=NULL;
                                        else if(tuple4->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple4;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _gtnumber || tupleUNegated || !(*tupleU == *tuple4))
                                                tuple4=NULL;
                                            }
                                        }
                                    }
                                    if(tuple4!=NULL){
                                        Tuple negativeTuple({C,W,V,C1},_aux_1);
                                        const Tuple* tuple5 = factory.find(negativeTuple);
                                        if(tuple5 == NULL)
                                            tuple5 = &negativeTuple;
                                        else{
                                            if(tuple5->isTrue())
                                                tuple5 = NULL;
                                            else if(tuple5->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple5;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple5))
                                                    tuple5=NULL;
                                                }
                                            }
                                        }
                                        if(tuple5!=NULL){
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
                                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                        int it = tuple5->getId();
                                                        shared_reason.get()->insert(it*-1);
                                                    }
                                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                    if(!itReason.second && itReason.first->second.get()->empty())
                                                        itReason.first->second=shared_reason;
                                                }
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                                if(currentDecisionLevel>0){
                                                    if(tuple1!=NULL){
                                                        int it = tuple1->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple3!=NULL){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple4!=NULL){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple5!=NULL){
                                                        int it = tuple5->getId();
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
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                    if(starter.getPredicateName() == _reachable_color && startVar > 0){
                        int C = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        int C1 = C - 1;
                        const Tuple* tuple2 = factory.find({V,C},_vertex_color);
                        if(tuple2!=NULL){
                            if(tuple2->isFalse())
                            tuple2=NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            const std::vector<int>* tuples = &pe_0_.getValuesVec({V});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ue_0_.getValuesVec({V});
                            else if(tupleU->getPredicateName() == _e && !tupleUNegated)
                                undeRepeated.push_back(tupleU);
                            for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                if(tuplesU!=&EMPTY_TUPLES_VEC)
                                    tupleU = NULL;
                                const Tuple* tuple3 = NULL;
                                if(i<tuples->size())
                                    tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                else if(i<tuples->size()+tuplesU->size()){
                                    tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                    tupleUNegated=false;
                                }else if(!undeRepeated.empty()){
                                    if(tupleU->at(0) == V)
                                        tuple3 = tupleU;
                                }
                                if(tuple3!=NULL){
                                    int W = tuple3->at(1);
                                    const Tuple* tuple4 = factory.find({W,C1},_gtnumber);
                                    if(tuple4!=NULL){
                                        if(tuple4->isFalse())
                                        tuple4=NULL;
                                        else if(tuple4->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple4;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _gtnumber || tupleUNegated || !(*tupleU == *tuple4))
                                                tuple4=NULL;
                                            }
                                        }
                                    }
                                    if(tuple4!=NULL){
                                        Tuple negativeTuple({C,W,V,C1},_aux_1);
                                        const Tuple* tuple5 = factory.find(negativeTuple);
                                        if(tuple5 == NULL)
                                            tuple5 = &negativeTuple;
                                        else{
                                            if(tuple5->isTrue())
                                                tuple5 = NULL;
                                            else if(tuple5->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple5;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple5))
                                                    tuple5=NULL;
                                                }
                                            }
                                        }
                                        if(tuple5!=NULL){
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
                                                    if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                        int it = tuple5->getId();
                                                        shared_reason.get()->insert(it*-1);
                                                    }
                                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                    if(!itReason.second && itReason.first->second.get()->empty())
                                                        itReason.first->second=shared_reason;
                                                }
                                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                                if(currentDecisionLevel>0){
                                                    if(tuple2!=NULL){
                                                        int it = tuple2->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple3!=NULL){
                                                        int it = tuple3->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple4!=NULL){
                                                        int it = tuple4->getId();
                                                        shared_reason.get()->insert(it*1);
                                                    }
                                                    if(tuple5!=NULL){
                                                        int it = tuple5->getId();
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
                            }
                        }
                        for(auto pair : internalProps)
                            propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
                {
                    if(starter.getPredicateName() == _reachable_color && startVar < 0){
                        int C = starter[0];
                        int V = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({V,C},_vertex_color);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _vertex_color || tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _vertex_color && startVar > 0){
                        int V = starter[0];
                        int C = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({C,V},_reachable_color);
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
                                    if(tupleU->getPredicateName() != _reachable_color || !tupleUNegated || !(*tupleU == *tuple1))
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
                                if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _sup_2 && startVar < 0){
                        int X0 = starter[0];
                        int X1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({X0,X1},_reachable_color);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0,X1},_sup_0);
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
                                        if(tupleU->getPredicateName() != _sup_0 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({X0,X1},_sup_1);
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
                                            if(tupleU->getPredicateName() != _sup_1 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _sup_1 && startVar < 0){
                        int X0 = starter[0];
                        int X1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({X0,X1},_reachable_color);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0,X1},_sup_0);
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
                                        if(tupleU->getPredicateName() != _sup_0 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({X0,X1},_sup_2);
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
                                            if(tupleU->getPredicateName() != _sup_2 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _sup_0 && startVar < 0){
                        int X0 = starter[0];
                        int X1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({X0,X1},_reachable_color);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != _reachable_color || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0,X1},_sup_1);
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
                                        if(tupleU->getPredicateName() != _sup_1 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({X0,X1},_sup_2);
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
                                            if(tupleU->getPredicateName() != _sup_2 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
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
                    if(starter.getPredicateName() == _reachable_color && startVar > 0){
                        int X0 = starter[0];
                        int X1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        Tuple negativeTuple({X0,X1},_sup_0);
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
                                    if(tupleU->getPredicateName() != _sup_0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0,X1},_sup_1);
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
                                        if(tupleU->getPredicateName() != _sup_1 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({X0,X1},_sup_2);
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
                                            if(tupleU->getPredicateName() != _sup_2 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                                shared_reason.get()->insert(it*-1);
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
                                        if(tupleU->getPredicateName() != _reachable_color && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_2 && tupleU->getPredicateName() != _aux_1)
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                        else internalProps.push_back({tupleU,tupleUNegated});
                                    }else{
                                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                        if(currentDecisionLevel>0){
                                            if(tuple1!=NULL){
                                                int it = tuple1->getId();
                                                shared_reason.get()->insert(it*-1);
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
            }
            if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
        }
        }
