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
const int _bound = 2;
const int _end = 3;
const int _max_cost = 4;
const int _min_cost = 5;
const int _reachable = 6;
const int _reached = 7;
const int _selected_path = 8;
const int _start = 9;
const int _sup_0 = 10;
const int _sup_1 = 11;
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
    if(t->isUndef()) std::cout << "undef ";
    std::cout << Executor::predicateIds[t->getPredicateName()] << "(";
    for(int i=0;i<t->size();i++){
        if(i>0) std::cout << ",";
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
AuxMap<0> preachable_({});
AuxMap<0> ureachable_({});
AuxMap<0> freachable_({});
AuxMap<64> paux_0_0_1_({0,1});
AuxMap<64> uaux_0_0_1_({0,1});
AuxMap<64> faux_0_0_1_({0,1});
AuxMap<0> paux_0_({});
AuxMap<0> uaux_0_({});
AuxMap<0> faux_0_({});
AuxMap<0> pselected_path_({});
AuxMap<0> uselected_path_({});
AuxMap<0> fselected_path_({});
AuxMap<0> pstart_({});
AuxMap<0> ustart_({});
AuxMap<0> fstart_({});
AuxMap<32> paux_0_2_({2});
AuxMap<32> uaux_0_2_({2});
AuxMap<32> faux_0_2_({2});
AuxMap<32> pselected_path_0_({0});
AuxMap<32> uselected_path_0_({0});
AuxMap<32> fselected_path_0_({0});
AuxMap<0> psup_1_({});
AuxMap<0> usup_1_({});
AuxMap<0> fsup_1_({});
AuxMap<64> paux_1_0_1_({0,1});
AuxMap<64> uaux_1_0_1_({0,1});
AuxMap<64> faux_1_0_1_({0,1});
AuxMap<0> paux_1_({});
AuxMap<0> uaux_1_({});
AuxMap<0> faux_1_({});
AuxMap<64> paux_1_2_3_({2,3});
AuxMap<64> uaux_1_2_3_({2,3});
AuxMap<64> faux_1_2_3_({2,3});
AuxMap<96> paux_1_0_2_4_({0,2,4});
AuxMap<96> uaux_1_0_2_4_({0,2,4});
AuxMap<96> faux_1_0_2_4_({0,2,4});
AuxMap<0> pmax_cost_({});
AuxMap<0> umax_cost_({});
AuxMap<0> fmax_cost_({});
AuxMap<32> paux_1_5_({5});
AuxMap<32> uaux_1_5_({5});
AuxMap<32> faux_1_5_({5});
AuxMap<0> pmin_cost_({});
AuxMap<0> umin_cost_({});
AuxMap<0> fmin_cost_({});
AuxMap<32> paux_1_6_({6});
AuxMap<32> uaux_1_6_({6});
AuxMap<32> faux_1_6_({6});
AuxMap<32> preachable_0_({0});
AuxMap<32> ureachable_0_({0});
AuxMap<32> freachable_0_({0});
AuxMap<0> preached_({});
AuxMap<0> ureached_({});
AuxMap<0> freached_({});
AuxMap<0> pend_({});
AuxMap<0> uend_({});
AuxMap<0> fend_({});
AuxMap<0> pbound_({});
AuxMap<0> ubound_({});
AuxMap<0> fbound_({});
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
    updateReasonSize(conflictReason.size());
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
        reas.reserve(getMeanReasonSize());
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
    if(insertResult.first->getPredicateName() == _bound){
        fbound_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _min_cost){
        fmin_cost_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_1){
        faux_1_.insert2Vec(*insertResult.first);
        faux_1_0_1_.insert2Vec(*insertResult.first);
        faux_1_0_2_4_.insert2Vec(*insertResult.first);
        faux_1_2_3_.insert2Vec(*insertResult.first);
        faux_1_5_.insert2Vec(*insertResult.first);
        faux_1_6_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_1){
        fsup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _max_cost){
        fmax_cost_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _start){
        fstart_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _end){
        fend_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _selected_path){
        fselected_path_.insert2Vec(*insertResult.first);
        fselected_path_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_0){
        faux_0_.insert2Vec(*insertResult.first);
        faux_0_0_1_.insert2Vec(*insertResult.first);
        faux_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reached){
        freached_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reachable){
        freachable_.insert2Vec(*insertResult.first);
        freachable_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_0){
        fsup_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == _bound){
        pbound_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _min_cost){
        pmin_cost_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_1){
        paux_1_.insert2Vec(*insertResult.first);
        paux_1_0_1_.insert2Vec(*insertResult.first);
        paux_1_0_2_4_.insert2Vec(*insertResult.first);
        paux_1_2_3_.insert2Vec(*insertResult.first);
        paux_1_5_.insert2Vec(*insertResult.first);
        paux_1_6_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_1){
        psup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _max_cost){
        pmax_cost_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _start){
        pstart_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _end){
        pend_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _selected_path){
        pselected_path_.insert2Vec(*insertResult.first);
        pselected_path_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_0){
        paux_0_.insert2Vec(*insertResult.first);
        paux_0_0_1_.insert2Vec(*insertResult.first);
        paux_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reached){
        preached_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reachable){
        preachable_.insert2Vec(*insertResult.first);
        preachable_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_0){
        psup_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == _bound){
        ubound_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _min_cost){
        umin_cost_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_1){
        uaux_1_.insert2Vec(*insertResult.first);
        uaux_1_0_1_.insert2Vec(*insertResult.first);
        uaux_1_0_2_4_.insert2Vec(*insertResult.first);
        uaux_1_2_3_.insert2Vec(*insertResult.first);
        uaux_1_5_.insert2Vec(*insertResult.first);
        uaux_1_6_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _sup_1){
        usup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _max_cost){
        umax_cost_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _start){
        ustart_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _end){
        uend_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _selected_path){
        uselected_path_.insert2Vec(*insertResult.first);
        uselected_path_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _aux_0){
        uaux_0_.insert2Vec(*insertResult.first);
        uaux_0_0_1_.insert2Vec(*insertResult.first);
        uaux_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reached){
        ureached_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == _reachable){
        ureachable_.insert2Vec(*insertResult.first);
        ureachable_0_.insert2Vec(*insertResult.first);
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
std::vector<std::vector<int>> supportedAux1;
std::vector<std::vector<int>> supportedLiterals1;
std::unordered_map<int,int> sourcePointers1;
std::vector<int> unfoundedSetForComponent1;
void propFoundnessForComponent1(int foundedLiteral){
    std::vector<int> foundedStack({foundedLiteral});
    while(!foundedStack.empty()){
        Tuple* starter = factory.getTupleFromInternalID(foundedStack.back());
        foundedStack.pop_back();
        if(starter->getPredicateName() == _sup_1){
            int Y=starter->at(0);
            int C=starter->at(1);
            Tuple* head = factory.find({Y,C},_reachable);
            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                supportedLiterals1[starter->getId()].push_back(head->getId());
                sourcePointers1[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                foundnessFactory[head->getId()]=1;
            }
        }
        if(starter->getPredicateName() == _aux_1){
            int Y=starter->at(0);
            int C=starter->at(1);
            int X=starter->at(2);
            int C1=starter->at(3);
            int C2=starter->at(4);
            int V=starter->at(5);
            int V1=starter->at(6);
            Tuple* head = factory.find({Y,C},_sup_1);
            if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                supportedLiterals1[starter->getId()].push_back(head->getId());
                sourcePointers1[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                foundnessFactory[head->getId()]=1;
            }
        }
        if(starter->getPredicateName() == _reachable){
            int X=starter->at(0);
            int C1=starter->at(1);
            const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
            const std::vector<int>* tuplesU = &uselected_path_0_.getValuesVec({X});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int Y=tuple1->at(1);
                int C2=tuple1->at(2);
                int C = C1 + C2;
                const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                const std::vector<int>* tuplesU = &umax_cost_.getValuesVec({});
                for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                    Tuple* tuple3 = NULL;
                    if(i<tuples->size()) tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                    else tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int V=tuple3->at(0);
                    if(C <= V){
                        const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                        const std::vector<int>* tuplesU = &umin_cost_.getValuesVec({});
                        for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                            Tuple* tuple5 = NULL;
                            if(i<tuples->size()) tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                            else tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                            int V1=tuple5->at(0);
                            if(C >= V1){
                                Tuple* head = factory.find({Y,C,X,C1,C2,V,V1},_aux_1);
                                if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                    foundedStack.push_back(head->getId());
                                    foundnessFactory[head->getId()]=1;
                                }
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _selected_path){
            int X=starter->at(0);
            int Y=starter->at(1);
            int C2=starter->at(2);
            const std::vector<int>* tuples = &preachable_0_.getValuesVec({X});
            const std::vector<int>* tuplesU = &ureachable_0_.getValuesVec({X});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int C1=tuple1->at(1);
                if(foundnessFactory[tuple1->getId()]>=0){
                    int C = C1 + C2;
                    const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                    const std::vector<int>* tuplesU = &umax_cost_.getValuesVec({});
                    for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                        Tuple* tuple3 = NULL;
                        if(i<tuples->size()) tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                        else tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        int V=tuple3->at(0);
                        if(C <= V){
                            const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                            const std::vector<int>* tuplesU = &umin_cost_.getValuesVec({});
                            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                                Tuple* tuple5 = NULL;
                                if(i<tuples->size()) tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                else tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                int V1=tuple5->at(0);
                                if(C >= V1){
                                    Tuple* head = factory.find({Y,C,X,C1,C2,V,V1},_aux_1);
                                    if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                        foundedStack.push_back(head->getId());
                                        foundnessFactory[head->getId()]=1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _max_cost){
            int V=starter->at(0);
            const std::vector<int>* tuples = &preachable_.getValuesVec({});
            const std::vector<int>* tuplesU = &ureachable_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X=tuple1->at(0);
                int C1=tuple1->at(1);
                if(foundnessFactory[tuple1->getId()]>=0){
                    const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                    const std::vector<int>* tuplesU = &uselected_path_0_.getValuesVec({X});
                    for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                        Tuple* tuple2 = NULL;
                        if(i<tuples->size()) tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                        else tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        int Y=tuple2->at(1);
                        int C2=tuple2->at(2);
                        int C = C1 + C2;
                        if(C <= V){
                            const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                            const std::vector<int>* tuplesU = &umin_cost_.getValuesVec({});
                            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                                Tuple* tuple5 = NULL;
                                if(i<tuples->size()) tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                else tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                int V1=tuple5->at(0);
                                if(C >= V1){
                                    Tuple* head = factory.find({Y,C,X,C1,C2,V,V1},_aux_1);
                                    if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                        foundedStack.push_back(head->getId());
                                        foundnessFactory[head->getId()]=1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == _min_cost){
            int V1=starter->at(0);
            const std::vector<int>* tuples = &preachable_.getValuesVec({});
            const std::vector<int>* tuplesU = &ureachable_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X=tuple1->at(0);
                int C1=tuple1->at(1);
                if(foundnessFactory[tuple1->getId()]>=0){
                    const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                    const std::vector<int>* tuplesU = &uselected_path_0_.getValuesVec({X});
                    for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                        Tuple* tuple2 = NULL;
                        if(i<tuples->size()) tuple2 = factory.getTupleFromInternalID(tuples->at(i));
                        else tuple2 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        int Y=tuple2->at(1);
                        int C2=tuple2->at(2);
                        int C = C1 + C2;
                        if(C >= V1){
                            const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                            const std::vector<int>* tuplesU = &umax_cost_.getValuesVec({});
                            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                                Tuple* tuple5 = NULL;
                                if(i<tuples->size()) tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                else tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                int V=tuple5->at(0);
                                if(C <= V){
                                    Tuple* head = factory.find({Y,C,X,C1,C2,V,V1},_aux_1);
                                    if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){
                                        foundedStack.push_back(head->getId());
                                        foundnessFactory[head->getId()]=1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }//close while 
}//close function
void unfoundedPropagatorForComponent1(std::vector<int>& literalToPropagate,Executor* executor){
    currentDecisionLevel=executor->getCurrentDecisionLevel();
    int unfoundedCount=0;
    for(int id : unfoundedSetForComponent1){
        Tuple* starter = factory.getTupleFromInternalID(id);
        if(starter->isFalse() || foundnessFactory[id]>=0) continue;
        if(eagerFacts.count(id)!=0){
            foundnessFactory[starter->getId()]=1;
            propFoundnessForComponent1(id);
            continue;
        }
        bool spFound=false;
        if(!spFound && starter->getPredicateName() == _reachable && foundnessFactory[starter->getId()]<0){
            int Y=starter->at(0);
            int C=starter->at(1);
            Tuple* body = factory.find({Y,C},_sup_0);
            if(body!=NULL && !body->isFalse()){
                sourcePointers1[starter->getId()]=body->getId();
                supportedLiterals1[body->getId()].push_back(starter->getId());
                foundnessFactory[starter->getId()]=1;
                propFoundnessForComponent1(starter->getId());
                spFound=true;
            }
        }
        if(!spFound && starter->getPredicateName() == _reachable && foundnessFactory[starter->getId()]<0){
            int Y=starter->at(0);
            int C=starter->at(1);
            Tuple* body = factory.find({Y,C},_sup_1);
            if(body!=NULL && !body->isFalse()){
                if(foundnessFactory[body->getId()]>=0){
                    sourcePointers1[starter->getId()]=body->getId();
                    supportedLiterals1[body->getId()].push_back(starter->getId());
                    foundnessFactory[starter->getId()]=1;
                    propFoundnessForComponent1(starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == _sup_1 && foundnessFactory[starter->getId()]<0){
            int Y=starter->at(0);
            int C=starter->at(1);
            const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({Y,C});
            const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({Y,C});
            for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){
                Tuple* body = NULL;
                if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));
                else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(body!=NULL){
                    if(foundnessFactory[body->getId()]>=0){
                        sourcePointers1[starter->getId()]=body->getId();
                        supportedLiterals1[body->getId()].push_back(starter->getId());
                        foundnessFactory[starter->getId()]=1;
                        propFoundnessForComponent1(starter->getId());
                        spFound=true;
                    }
                }
            }
        }
        if(!spFound) unfoundedSetForComponent1[unfoundedCount++]=id;
        } //close unfounded for
        unfoundedSetForComponent1.resize(unfoundedCount);
        if(!unfoundedSetForComponent1.empty()){
            int conflictDetected=0;
            int currentExplainLevel = executor->getNextExplainLevel();
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            std::vector<int> propLiterals({currentDecisionLevel});
            std::vector<int> reasonStack;
            for(int lit : unfoundedSetForComponent1){
                Tuple* starter = factory.getTupleFromInternalID(lit);
                if(starter == NULL || starter->isFalse() || foundnessFactory[lit]>=0) continue;
                if(starter->getPredicateName()==_reachable){
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
                    if(starter->getPredicateName() == _reachable){
                        int Y=starter->at(0);
                        int C=starter->at(1);
                        Tuple* tuple = factory.find({Y,C},_sup_0);
                        if(tuple!=NULL){
                            if(tuple->isFalse())
                                shared_reason.get()->insert(-tuple->getId());
                        }
                    }
                    if(starter->getPredicateName() == _reachable){
                        int Y=starter->at(0);
                        int C=starter->at(1);
                        Tuple* tuple = factory.find({Y,C},_sup_1);
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
                    if(starter->getPredicateName() == _sup_1){
                        int Y=starter->at(0);
                        int C=starter->at(1);
                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({Y,C});
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
            for(int lit : unfoundedSetForComponent1){
                Tuple* starter = factory.getTupleFromInternalID(lit);
                if(starter == NULL || starter->isFalse() || foundnessFactory[lit]>=0) continue;
                foundnessFactory[lit]=1;
                auto oldSP = sourcePointers1.find(lit);
                if(oldSP!=sourcePointers1.end()){
                    supportedLiterals1[oldSP->second].push_back(lit);
                }
            }
            if(conflictDetected!=0) {
                executor->handleConflict(conflictDetected,literalToPropagate);
                if(currentDecisionLevel > 0) for(int i=1; i<propLiterals.size(); i++) reasonForLiteral[propLiterals[i]].get()->clear();
            }else if(propLiterals.size()>1){
                executor->executeProgramOnFacts(propLiterals,literalToPropagate,true);
            }
            unfoundedSetForComponent1.clear();
        }//close if empty unfounded set
    }// close unfoundedPropagatorForComponent
    void checkFoundness(){
        while(!falseLits.empty()){
            int starter = falseLits.back();
            int current = starter >= 0 ? starter : -starter;
            falseLits.pop_back();
            {
                std::vector<int>& supported = supportedLiterals1[current];
                int saving=0;
                for(int i=0;i < supported.size(); i++){
                    int lit = supported[i];
                    Tuple* removingLit = factory.getTupleFromInternalID(lit);
                    if(removingLit->isFalse()){supported[saving++]=supported[i]; continue;}
                    if(foundnessFactory[lit]>=0){
                        foundnessFactory[lit]=-1;
                        unfoundedSetForComponent1.push_back(lit);
                        falseLits.push_back(lit);
                    }//close if
                }//close for
                supported.resize(saving);
                if(current < supportedAux1.size()){
                    std::vector<int>& supAux = supportedAux1[current];
                    for(int lit : supAux){
                        Tuple* removingLit = factory.getTupleFromInternalID(lit);
                        if(!removingLit->isFalse() && foundnessFactory[lit]>=0){
                            foundnessFactory[lit]=-1;
                            unfoundedSetForComponent1.push_back(lit);
                            falseLits.push_back(lit);
                        }//close if
                    }//close for
                }
            }//close local scope
        }//close while
    }//close function
    void Executor::checkUnfoundedSets(std::vector<int>& literalsToPropagate,Executor* executor){
        checkFoundness();
        unfoundedPropagatorForComponent1(literalsToPropagate,executor);
    }
    void Executor::undefLiteralsReceived(){
        factory.setGenerated(true);
        undefinedLoaded=true;
        std::cout<<"Undef received "<<factory.size()<<std::endl;
        std::cout<<"Component 5"<<std::endl;
        std::cout<<"Component 4"<<std::endl;
        std::cout<<"Component 3"<<std::endl;
        std::cout<<"Component 2"<<std::endl;
        std::cout<<"Component 1"<<std::endl;
        //---------------------------------Recursive Component---------------------------------
        {
            std::vector<int> generationStack;
            {
                const std::vector<int>* tuples = &pselected_path_.getValuesVec({});
                const std::vector<int>* tuplesU = &uselected_path_.getValuesVec({});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple0 = NULL;
                    if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int X = tuple0->at(0);
                    int Y = tuple0->at(1);
                    int C = tuple0->at(2);
                    Tuple* tuple1 = factory.find({X},_start);
                    if(tuple1!=NULL && !tuple1->isFalse()){
                        Tuple* saving3 = factory.addNewInternalTuple({Y,C,X},_aux_0);
                        const auto& insertResult = saving3->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving3->getId());
                            insertUndef(insertResult);
                            Tuple* saving1 = factory.addNewInternalTuple({Y,C},_sup_0);
                            const auto& insertResult = saving1->setStatus(Undef);
                            if(insertResult.second){
                                factory.removeFromCollisionsList(saving1->getId());
                                insertUndef(insertResult);
                                Tuple* saving0 = factory.addNewInternalTuple({Y,C},_reachable);
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
            while(!generationStack.empty()){
                Tuple* starter = factory.getTupleFromInternalID(generationStack.back());
                generationStack.pop_back();
                if(starter->getPredicateName() == _reachable){
                    int X = starter->at(0);
                    int C1 = starter->at(1);
                    const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                    const std::vector<int>* tuplesU = &uselected_path_0_.getValuesVec({X});
                    for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                        Tuple* tuple1 = NULL;
                        if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                        else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        if(tuple1->at(0) == X){
                            int Y = tuple1->at(1);
                            int C2 = tuple1->at(2);
                            int C = C1 + C2;
                            const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                            const std::vector<int>* tuplesU = &umax_cost_.getValuesVec({});
                            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                                Tuple* tuple3 = NULL;
                                if(i<tuples->size()) tuple3=factory.getTupleFromInternalID(tuples->at(i));
                                else tuple3=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                int V = tuple3->at(0);
                                if(C <= V){
                                    const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                                    const std::vector<int>* tuplesU = &umin_cost_.getValuesVec({});
                                    for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                                        Tuple* tuple5 = NULL;
                                        if(i<tuples->size()) tuple5=factory.getTupleFromInternalID(tuples->at(i));
                                        else tuple5=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        int V1 = tuple5->at(0);
                                        if(C >= V1){
                                            Tuple* saving2 = factory.addNewInternalTuple({Y,C,X,C1,C2,V,V1},_aux_1);
                                            const auto& insertResult = saving2->setStatus(Undef);
                                            if(insertResult.second){
                                                factory.removeFromCollisionsList(saving2->getId());
                                                insertUndef(insertResult);
                                                if(supportedAux1.size() < factory.size())
                                                    supportedAux1.resize(factory.size());
                                                supportedAux1[starter->getId()].push_back(saving2->getId());
                                                Tuple* saving1 = factory.addNewInternalTuple({Y,C},_sup_1);
                                                const auto& insertResult = saving1->setStatus(Undef);
                                                if(insertResult.second){
                                                    factory.removeFromCollisionsList(saving1->getId());
                                                    insertUndef(insertResult);
                                                    Tuple* saving0 = factory.addNewInternalTuple({Y,C},_reachable);
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
                }
            }
        }//close local scope
        //---------------------------------Recursive Component---------------------------------
        std::cout<<"Component 0"<<std::endl;
        {
            const std::vector<int>* tuples = &preachable_.getValuesVec({});
            const std::vector<int>* tuplesU = &ureachable_.getValuesVec({});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple = NULL;
                if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
                else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int Y = tuple->at(0);
                int C = tuple->at(1);
                Tuple* saving1 = factory.addNewInternalTuple({Y},_reached);
                const auto& insertResult = saving1->setStatus(Undef);
                if(insertResult.second){
                    factory.removeFromCollisionsList(saving1->getId());
                    insertUndef(insertResult);
                }
            }
        }
        foundnessFactory.resize(factory.size());
        {
            const std::vector<int>* tuples = &preachable_.getValuesVec({});
            const std::vector<int>* tuplesU = &ureachable_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent1.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &psup_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &usup_1_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent1.push_back(lit);}
            }
        }
        {
            const std::vector<int>* tuples = &paux_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaux_1_.getValuesVec({});
            for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
                int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());
                int& founded = foundnessFactory[lit];
                if(founded == 0) {founded=-1;unfoundedSetForComponent1.push_back(lit);}
            }
        }
        supportedLiterals1.resize(factory.size());
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
        stringToUniqueStringPointer["bound"] = _bound;
        stringToUniqueStringPointer["end"] = _end;
        stringToUniqueStringPointer["max_cost"] = _max_cost;
        stringToUniqueStringPointer["min_cost"] = _min_cost;
        stringToUniqueStringPointer["reachable"] = _reachable;
        stringToUniqueStringPointer["reached"] = _reached;
        stringToUniqueStringPointer["selected_path"] = _selected_path;
        stringToUniqueStringPointer["start"] = _start;
        stringToUniqueStringPointer["sup_0"] = _sup_0;
        stringToUniqueStringPointer["sup_1"] = _sup_1;
        Executor::predicateIds.push_back("aux_0");
        factory.addPredicate();
        Executor::predicateIds.push_back("aux_1");
        factory.addPredicate();
        Executor::predicateIds.push_back("bound");
        factory.addPredicate();
        Executor::predicateIds.push_back("end");
        factory.addPredicate();
        Executor::predicateIds.push_back("max_cost");
        factory.addPredicate();
        Executor::predicateIds.push_back("min_cost");
        factory.addPredicate();
        Executor::predicateIds.push_back("reachable");
        factory.addPredicate();
        Executor::predicateIds.push_back("reached");
        factory.addPredicate();
        Executor::predicateIds.push_back("selected_path");
        factory.addPredicate();
        Executor::predicateIds.push_back("start");
        factory.addPredicate();
        Executor::predicateIds.push_back("sup_0");
        factory.addPredicate();
        Executor::predicateIds.push_back("sup_1");
        factory.addPredicate();
    }
    void Executor::printStatus(){
        for(const Tuple* t : factory.getTuples())
            if(!t->isInternalLiteral()) printTuple(t);
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
            std::cout << "Stored reason count             "<<reasonForLiteral.size()<<std::endl;
            std::cout << "Stored level count              "<<levelToIntLiterals.size()<<std::endl;
            int sum = 0,count=0;for(auto pair : levelToIntLiterals) if(pair.second.size()>0){count++;sum+=pair.second.size();}
            if(count >0) std::cout << "Averager per level              "<<sum/count<<std::endl;
            sum = 0;count=0;for(auto pair : reasonForLiteral) if(pair.second.get()->size()>0){count++;sum+=pair.second.get()->size();}
            if(count >0) std::cout << "Averager reason per literal     "<<sum/count<<std::endl;
            std::string trueConstraint = "";
            for(int internalId : preached_.getValuesVec({})){
                Tuple* tuple = factory.getTupleFromInternalID(internalId);
                std::string tupleToString = tuple->size() > 0 ? "reached(" : "reached";
                for(unsigned k=0; k<tuple->size();k++){
                    if(k>0) tupleToString+=",";
                    tupleToString+=ConstantsManager::getInstance().unmapConstant(tuple->at(k));
                }
                tupleToString+= tuple->size() > 0 ? ")" : "";
                std::cout << tupleToString <<" ";
            }
            for(int internalId : preachable_.getValuesVec({})){
                Tuple* tuple = factory.getTupleFromInternalID(internalId);
                std::string tupleToString = tuple->size() > 0 ? "reachable(" : "reachable";
                for(unsigned k=0; k<tuple->size();k++){
                    if(k>0) tupleToString+=",";
                    tupleToString+=ConstantsManager::getInstance().unmapConstant(tuple->at(k));
                }
                tupleToString+= tuple->size() > 0 ? ")" : "";
                std::cout << tupleToString <<" ";
            }
            std::cout << std::endl;
            TupleFactory lazyFactory;
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
            lazyFactory.addPredicate();
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
                int size=levelToIntLiterals[currentDecisionLevel].size();
                while(size-- >0){
                    int var = levelToIntLiterals[currentDecisionLevel][size];
                    int uVar = var>0 ? var : -var;
                    Tuple* tuple = factory.getTupleFromInternalID(uVar);
                    reasonForLiteral[var].get()->clear();
                    const auto& insertResult = tuple->setStatus(Undef);
                    if (insertResult.second) {
                        factory.removeFromCollisionsList(uVar);
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    Tuple negativeTuple({Y,C},_reachable);
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
                                                if(tupleU->getPredicateName() != _reachable || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                            const std::vector<int>* tuples = &psup_1_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &usup_1_.getValuesVec({});
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
                                    tuple0 = tupleU;
                                }
                                if(tuple0!=NULL){
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    Tuple negativeTuple({Y,C},_reachable);
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
                                                if(tupleU->getPredicateName() != _reachable || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                        const std::vector<int>* trueHeads = &preached_.getValuesVec({});
                        for(unsigned i = 0;i < trueHeads->size(); i++){
                            const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                            if(eagerFacts.count(currentHead->getId())!=0) continue;
                            int Y = currentHead->at(0);
                            const std::vector<int>* tuples = &preachable_0_.getValuesVec({Y});
                            const std::vector<int>* tuplesU = &ureachable_0_.getValuesVec({Y});
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
                        const std::vector<int>* falseHeads = &freached_.getValuesVec({});
                        for(unsigned i = 0;i < falseHeads->size(); i++){
                            const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                            int Y = currentHead->at(0);
                            const std::vector<int>* tuples = &preachable_0_.getValuesVec({Y});
                            const std::vector<int>* tuplesU = &ureachable_0_.getValuesVec({Y});
                            if(tuples->size()>0){
                                propagatedLiterals.push_back(1);
                                return;
                            }else{
                                while(!tuplesU->empty()){
                                    propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                }
                            }
                        }
                        const std::vector<int>* undefHeads = &ureached_.getValuesVec({});
                        for(unsigned i = 0; i < undefHeads->size();){
                            const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                            int Y = currentHead->at(0);
                            const std::vector<int>* tuples = &preachable_0_.getValuesVec({Y});
                            const std::vector<int>* tuplesU = &ureachable_0_.getValuesVec({Y});
                            if(tuples->size() > 0)
                                propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else if(tuplesU->size()==0)
                                propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else i++;
                        }
                    }
                    {
                        {
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &pend_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uend_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _end && !tupleUNegated)
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
                                    int Y = tuple0->at(0);
                                    Tuple negativeTuple({Y},_reached);
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
                                                if(tupleU->getPredicateName() != _reached || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                            const std::vector<int>* tuples = &pend_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uend_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _end && !tupleUNegated)
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
                                    int X = tuple0->at(0);
                                    const std::vector<int>* tuples = &preachable_0_.getValuesVec({X});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &ureachable_0_.getValuesVec({X});
                                    else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                            if(tupleU->at(0) == X)
                                                tuple1 = tupleU;
                                        }
                                        if(tuple1!=NULL){
                                            int C = tuple1->at(1);
                                            const std::vector<int>* tuples = &pbound_.getValuesVec({});
                                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                            std::vector<const Tuple*> undeRepeated;
                                            if(tupleU == NULL)
                                                tuplesU = &ubound_.getValuesVec({});
                                            else if(tupleU->getPredicateName() == _bound && !tupleUNegated)
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
                                                    tuple2 = tupleU;
                                                }
                                                if(tuple2!=NULL){
                                                    int B = tuple2->at(0);
                                                    if(C < B){
                                                        if(tupleU != NULL){
                                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                            const std::vector<int>* tuples = &preachable_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ureachable_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                            if(tupleU != NULL){
                                                if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                            const std::vector<int>* tuples = &preachable_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ureachable_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                    int X = tuple0->at(0);
                                    int C1 = tuple0->at(1);
                                    const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &uselected_path_0_.getValuesVec({X});
                                    else if(tupleU->getPredicateName() == _selected_path && !tupleUNegated)
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
                                            if(tupleU->at(0) == X)
                                                tuple1 = tupleU;
                                        }
                                        if(tuple1!=NULL){
                                            int Y = tuple1->at(1);
                                            int C2 = tuple1->at(2);
                                            int C = C1 + C2;
                                            const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                            std::vector<const Tuple*> undeRepeated;
                                            if(tupleU == NULL)
                                                tuplesU = &umax_cost_.getValuesVec({});
                                            else if(tupleU->getPredicateName() == _max_cost && !tupleUNegated)
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
                                                    tuple3 = tupleU;
                                                }
                                                if(tuple3!=NULL){
                                                    int V = tuple3->at(0);
                                                    if(C <= V){
                                                        const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                                                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                                        std::vector<const Tuple*> undeRepeated;
                                                        if(tupleU == NULL)
                                                            tuplesU = &umin_cost_.getValuesVec({});
                                                        else if(tupleU->getPredicateName() == _min_cost && !tupleUNegated)
                                                            undeRepeated.push_back(tupleU);
                                                        for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                                            if(tuplesU!=&EMPTY_TUPLES_VEC)
                                                                tupleU = NULL;
                                                            const Tuple* tuple5 = NULL;
                                                            if(i<tuples->size())
                                                                tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                                            else if(i<tuples->size()+tuplesU->size()){
                                                                tupleU = tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                                tupleUNegated=false;
                                                            }else if(!undeRepeated.empty()){
                                                                tuple5 = tupleU;
                                                            }
                                                            if(tuple5!=NULL){
                                                                int V1 = tuple5->at(0);
                                                                if(C >= V1){
                                                                    Tuple negativeTuple({Y,C,X,C1,C2,V,V1},_aux_1);
                                                                    const Tuple* tuple7 = factory.find(negativeTuple);
                                                                    if(tuple7 == NULL)
                                                                        tuple7 = &negativeTuple;
                                                                    else{
                                                                        if(tuple7->isTrue())
                                                                            tuple7 = NULL;
                                                                        else if(tuple7->isUndef()){
                                                                            if(tupleU == NULL){
                                                                                tupleU = tuple7;
                                                                                tupleUNegated=true;
                                                                            }else{
                                                                                if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple7))
                                                                                tuple7=NULL;
                                                                            }
                                                                        }
                                                                    }
                                                                    if(tuple7!=NULL){
                                                                        if(tupleU != NULL){
                                                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    int X = tuple0->at(2);
                                    int C1 = tuple0->at(3);
                                    int C2 = tuple0->at(4);
                                    int V = tuple0->at(5);
                                    int V1 = tuple0->at(6);
                                    Tuple negativeTuple({V1},_min_cost);
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
                                                if(tupleU->getPredicateName() != _min_cost || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    int X = tuple0->at(2);
                                    int C1 = tuple0->at(3);
                                    int C2 = tuple0->at(4);
                                    int V = tuple0->at(5);
                                    int V1 = tuple0->at(6);
                                    Tuple negativeTuple({V},_max_cost);
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
                                                if(tupleU->getPredicateName() != _max_cost || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    int X = tuple0->at(2);
                                    int C1 = tuple0->at(3);
                                    int C2 = tuple0->at(4);
                                    int V = tuple0->at(5);
                                    int V1 = tuple0->at(6);
                                    Tuple negativeTuple({X,Y,C2},_selected_path);
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
                                                if(tupleU->getPredicateName() != _selected_path || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    int X = tuple0->at(2);
                                    int C1 = tuple0->at(3);
                                    int C2 = tuple0->at(4);
                                    int V = tuple0->at(5);
                                    int V1 = tuple0->at(6);
                                    Tuple negativeTuple({X,C1},_reachable);
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
                                                if(tupleU->getPredicateName() != _reachable || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                            const std::vector<int>* tuples = &pselected_path_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uselected_path_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _selected_path && !tupleUNegated)
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
                                    int X = tuple0->at(0);
                                    int Y = tuple0->at(1);
                                    int C = tuple0->at(2);
                                    const Tuple* tuple1 = factory.find({X},_start);
                                    if(tuple1!=NULL){
                                        if(tuple1->isFalse())
                                        tuple1=NULL;
                                        else if(tuple1->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple1;
                                                tupleUNegated=false;
                                            }else{
                                                if(tupleU->getPredicateName() != _start || tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        Tuple negativeTuple({Y,C,X},_aux_0);
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
                                                    if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple2))
                                                    tuple2=NULL;
                                                }
                                            }
                                        }
                                        if(tuple2!=NULL){
                                            if(tupleU != NULL){
                                                if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    int X = tuple0->at(2);
                                    Tuple negativeTuple({X},_start);
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
                                                if(tupleU->getPredicateName() != _start || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                    int Y = tuple0->at(0);
                                    int C = tuple0->at(1);
                                    int X = tuple0->at(2);
                                    Tuple negativeTuple({X,Y,C},_selected_path);
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
                                                if(tupleU->getPredicateName() != _selected_path || !tupleUNegated || !(*tupleU == *tuple1))
                                                tuple1=NULL;
                                            }
                                        }
                                    }
                                    if(tuple1!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                            int Y = currentHead->at(0);
                            int C = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({Y, C});
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
                        const std::vector<int>* falseHeads = &fsup_0_.getValuesVec({});
                        for(unsigned i = 0;i < falseHeads->size(); i++){
                            const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                            int Y = currentHead->at(0);
                            int C = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({Y, C});
                            if(tuples->size()>0){
                                propagatedLiterals.push_back(1);
                                return;
                            }else{
                                while(!tuplesU->empty()){
                                    propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                }
                            }
                        }
                        const std::vector<int>* undefHeads = &usup_0_.getValuesVec({});
                        for(unsigned i = 0; i < undefHeads->size();){
                            const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                            int Y = currentHead->at(0);
                            int C = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({Y, C});
                            if(tuples->size() > 0)
                                propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else if(tuplesU->size()==0)
                                propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else i++;
                        }
                    }
                    {
                        const std::vector<int>* trueHeads = &psup_1_.getValuesVec({});
                        for(unsigned i = 0;i < trueHeads->size(); i++){
                            const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                            if(eagerFacts.count(currentHead->getId())!=0) continue;
                            int Y = currentHead->at(0);
                            int C = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({Y, C});
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
                        const std::vector<int>* falseHeads = &fsup_1_.getValuesVec({});
                        for(unsigned i = 0;i < falseHeads->size(); i++){
                            const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                            int Y = currentHead->at(0);
                            int C = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({Y, C});
                            if(tuples->size()>0){
                                propagatedLiterals.push_back(1);
                                return;
                            }else{
                                while(!tuplesU->empty()){
                                    propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                }
                            }
                        }
                        const std::vector<int>* undefHeads = &usup_1_.getValuesVec({});
                        for(unsigned i = 0; i < undefHeads->size();){
                            const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                            int Y = currentHead->at(0);
                            int C = currentHead->at(1);
                            const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({Y, C});
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
                        if(starter.getPredicateName() == _reachable && startVar < 0){
                            int Y = starter[0];
                            int C = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Y,C},_sup_0);
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _sup_0 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({Y,C},_reachable);
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
                                        if(tupleU->getPredicateName() != _reachable || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    if(starter.getPredicateName() == _aux_0){
                        int Y = starter.at(0);
                        int C = starter.at(1);
                        int X = starter.at(2);
                        Tuple* head = factory.find({Y,C}, _sup_0);
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
                            const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({Y, C});
                            if(head != NULL && head->isTrue()){
                                if(tuples->size() == 0 && tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        int itHead = head->getId();
                                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({Y, C});
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
                                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({Y, C});
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
                                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({Y, C});
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
                    }else if(starter.getPredicateName() == _sup_0){
                        int Y = starter.at(0);
                        int C = starter.at(1);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({Y,C});
                        const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({Y,C});
                        if(startVar > 0){
                            if(tuples->size()==0){
                                if(tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({Y,C});
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
                                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({Y,C});
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
                        if(starter.getPredicateName() == _selected_path && startVar < 0){
                            int X = starter[0];
                            int Y = starter[1];
                            int C = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Y,C,X},_aux_0);
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _aux_0 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({X,Y,C},_selected_path);
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
                                        if(tupleU->getPredicateName() != _selected_path || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == _start && startVar < 0){
                            int X = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_0_2_.getValuesVec({X});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_0_2_.getValuesVec({X});
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
                                    if(tupleU->at(2) == X)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Y = tuple1->at(0);
                                    int C = tuple1->at(1);
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _aux_0 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({X},_start);
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
                                        if(tupleU->getPredicateName() != _start || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
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
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({X,Y,C},_selected_path);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _selected_path || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                const Tuple* tuple2 = factory.find({X},_start);
                                if(tuple2!=NULL){
                                    if(tuple2->isFalse())
                                    tuple2=NULL;
                                    else if(tuple2->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple2;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != _start || tupleUNegated || !(*tupleU == *tuple2))
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _start && startVar > 0){
                            int X = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uselected_path_0_.getValuesVec({X});
                            else if(tupleU->getPredicateName() == _selected_path && !tupleUNegated)
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
                                    if(tupleU->at(0) == X)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Y = tuple1->at(1);
                                    int C = tuple1->at(2);
                                    Tuple negativeTuple({Y,C,X},_aux_0);
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
                                                if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                            }else propagatedLiterals.push_back(1);
                                            return;
                                        }
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _selected_path && startVar > 0){
                            int X = starter[0];
                            int Y = starter[1];
                            int C = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({X},_start);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _start || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                Tuple negativeTuple({Y,C,X},_aux_0);
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
                                            if(tupleU->getPredicateName() != _aux_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == _reachable && startVar < 0){
                            int Y = starter[0];
                            int C = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Y,C},_sup_1);
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _sup_1 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({Y,C},_reachable);
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
                                        if(tupleU->getPredicateName() != _reachable || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    if(starter.getPredicateName() == _aux_1){
                        int Y = starter.at(0);
                        int C = starter.at(1);
                        int X = starter.at(2);
                        int C1 = starter.at(3);
                        int C2 = starter.at(4);
                        int V = starter.at(5);
                        int V1 = starter.at(6);
                        Tuple* head = factory.find({Y,C}, _sup_1);
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
                            const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({Y, C});
                            const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({Y, C});
                            if(head != NULL && head->isTrue()){
                                if(tuples->size() == 0 && tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        int itHead = head->getId();
                                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({Y, C});
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
                                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({Y, C});
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
                                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({Y, C});
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
                        int Y = starter.at(0);
                        int C = starter.at(1);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        const std::vector<int>* tuples = &paux_1_0_1_.getValuesVec({Y,C});
                        const std::vector<int>* tuplesU = &uaux_1_0_1_.getValuesVec({Y,C});
                        if(startVar > 0){
                            if(tuples->size()==0){
                                if(tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({Y,C});
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
                                        const std::vector<int>* tuplesF = &faux_1_0_1_.getValuesVec({Y,C});
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
                        if(starter.getPredicateName() == _reachable && startVar < 0){
                            int X = starter[0];
                            int C1 = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_1_2_3_.getValuesVec({X,C1});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_1_2_3_.getValuesVec({X,C1});
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
                                    if(tupleU->at(2) == X && tupleU->at(3) == C1)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Y = tuple1->at(0);
                                    int C = tuple1->at(1);
                                    int C2 = tuple1->at(4);
                                    int V = tuple1->at(5);
                                    int V1 = tuple1->at(6);
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _aux_1 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            int C1 = starter[3];
                            int C2 = starter[4];
                            int V = starter[5];
                            int V1 = starter[6];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({X,C1},_reachable);
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
                                        if(tupleU->getPredicateName() != _reachable || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == _selected_path && startVar < 0){
                            int X = starter[0];
                            int Y = starter[1];
                            int C2 = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_1_0_2_4_.getValuesVec({Y,X,C2});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_1_0_2_4_.getValuesVec({Y,X,C2});
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
                                    if(tupleU->at(0) == Y && tupleU->at(2) == X && tupleU->at(4) == C2)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int C = tuple1->at(1);
                                    int C1 = tuple1->at(3);
                                    int V = tuple1->at(5);
                                    int V1 = tuple1->at(6);
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _aux_1 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            int C1 = starter[3];
                            int C2 = starter[4];
                            int V = starter[5];
                            int V1 = starter[6];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({X,Y,C2},_selected_path);
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
                                        if(tupleU->getPredicateName() != _selected_path || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == _max_cost && startVar < 0){
                            int V = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_1_5_.getValuesVec({V});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_1_5_.getValuesVec({V});
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
                                    if(tupleU->at(5) == V)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Y = tuple1->at(0);
                                    int C = tuple1->at(1);
                                    int X = tuple1->at(2);
                                    int C1 = tuple1->at(3);
                                    int C2 = tuple1->at(4);
                                    int V1 = tuple1->at(6);
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _aux_1 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            int C1 = starter[3];
                            int C2 = starter[4];
                            int V = starter[5];
                            int V1 = starter[6];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({V},_max_cost);
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
                                        if(tupleU->getPredicateName() != _max_cost || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == _min_cost && startVar < 0){
                            int V1 = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &paux_1_6_.getValuesVec({V1});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uaux_1_6_.getValuesVec({V1});
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
                                    if(tupleU->at(6) == V1)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Y = tuple1->at(0);
                                    int C = tuple1->at(1);
                                    int X = tuple1->at(2);
                                    int C1 = tuple1->at(3);
                                    int C2 = tuple1->at(4);
                                    int V = tuple1->at(5);
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
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _aux_1 && startVar > 0){
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            int C1 = starter[3];
                            int C2 = starter[4];
                            int V = starter[5];
                            int V1 = starter[6];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({V1},_min_cost);
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
                                        if(tupleU->getPredicateName() != _min_cost || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
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
                            int Y = starter[0];
                            int C = starter[1];
                            int X = starter[2];
                            int C1 = starter[3];
                            int C2 = starter[4];
                            int V = starter[5];
                            int V1 = starter[6];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            if(C == C1 + C2){
                                if(C <= V){
                                    if(C >= V1){
                                        const Tuple* tuple4 = factory.find({X,C1},_reachable);
                                        if(tuple4!=NULL){
                                            if(tuple4->isFalse())
                                            tuple4=NULL;
                                            else if(tuple4->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple4;
                                                    tupleUNegated=false;
                                                }else{
                                                    if(tupleU->getPredicateName() != _reachable || tupleUNegated || !(*tupleU == *tuple4))
                                                    tuple4=NULL;
                                                }
                                            }
                                        }
                                        if(tuple4!=NULL){
                                            const Tuple* tuple5 = factory.find({X,Y,C2},_selected_path);
                                            if(tuple5!=NULL){
                                                if(tuple5->isFalse())
                                                tuple5=NULL;
                                                else if(tuple5->isUndef()){
                                                    if(tupleU == NULL){
                                                        tupleU = tuple5;
                                                        tupleUNegated=false;
                                                    }else{
                                                        if(tupleU->getPredicateName() != _selected_path || tupleUNegated || !(*tupleU == *tuple5))
                                                        tuple5=NULL;
                                                    }
                                                }
                                            }
                                            if(tuple5!=NULL){
                                                const Tuple* tuple6 = factory.find({V},_max_cost);
                                                if(tuple6!=NULL){
                                                    if(tuple6->isFalse())
                                                    tuple6=NULL;
                                                    else if(tuple6->isUndef()){
                                                        if(tupleU == NULL){
                                                            tupleU = tuple6;
                                                            tupleUNegated=false;
                                                        }else{
                                                            if(tupleU->getPredicateName() != _max_cost || tupleUNegated || !(*tupleU == *tuple6))
                                                            tuple6=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple6!=NULL){
                                                    const Tuple* tuple7 = factory.find({V1},_min_cost);
                                                    if(tuple7!=NULL){
                                                        if(tuple7->isFalse())
                                                        tuple7=NULL;
                                                        else if(tuple7->isUndef()){
                                                            if(tupleU == NULL){
                                                                tupleU = tuple7;
                                                                tupleUNegated=false;
                                                            }else{
                                                                if(tupleU->getPredicateName() != _min_cost || tupleUNegated || !(*tupleU == *tuple7))
                                                                tuple7=NULL;
                                                            }
                                                        }
                                                    }
                                                    if(tuple7!=NULL){
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
                                                                if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                                    int it = tuple4->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                                    int it = tuple5->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                if(factory.find(*tuple6) != NULL && tuple6!=tupleU){
                                                                    int it = tuple6->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                if(factory.find(*tuple7) != NULL && tuple7!=tupleU){
                                                                    int it = tuple7->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                                if(!itReason.second && itReason.first->second.get()->empty())
                                                                    itReason.first->second=shared_reason;
                                                            }
                                                            if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
                                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                            else internalProps.push_back({tupleU,tupleUNegated});
                                                        }else{
                                                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                                                            if(currentDecisionLevel>0){
                                                                if(tuple4!=NULL){
                                                                    int it = tuple4->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                if(tuple5!=NULL){
                                                                    int it = tuple5->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                if(tuple6!=NULL){
                                                                    int it = tuple6->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                if(tuple7!=NULL){
                                                                    int it = tuple7->getId();
                                                                    shared_reason.get()->insert(it*1);
                                                                }
                                                                reasonForLiteral[-startVar]=shared_reason;
                                                                handleConflict(-startVar, propagatedLiterals);
                                                                for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                                            }else propagatedLiterals.push_back(1);
                                                            return;
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
                        if(starter.getPredicateName() == _min_cost && startVar > 0){
                            int V1 = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &preachable_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ureachable_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                    int X = tuple1->at(0);
                                    int C1 = tuple1->at(1);
                                    const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &uselected_path_0_.getValuesVec({X});
                                    else if(tupleU->getPredicateName() == _selected_path && !tupleUNegated)
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
                                            if(tupleU->at(0) == X)
                                                tuple2 = tupleU;
                                        }
                                        if(tuple2!=NULL){
                                            int Y = tuple2->at(1);
                                            int C2 = tuple2->at(2);
                                            int C = C1 + C2;
                                            if(C >= V1){
                                                const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                                std::vector<const Tuple*> undeRepeated;
                                                if(tupleU == NULL)
                                                    tuplesU = &umax_cost_.getValuesVec({});
                                                else if(tupleU->getPredicateName() == _max_cost && !tupleUNegated)
                                                    undeRepeated.push_back(tupleU);
                                                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                                    if(tuplesU!=&EMPTY_TUPLES_VEC)
                                                        tupleU = NULL;
                                                    const Tuple* tuple5 = NULL;
                                                    if(i<tuples->size())
                                                        tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                                    else if(i<tuples->size()+tuplesU->size()){
                                                        tupleU = tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                        tupleUNegated=false;
                                                    }else if(!undeRepeated.empty()){
                                                        tuple5 = tupleU;
                                                    }
                                                    if(tuple5!=NULL){
                                                        int V = tuple5->at(0);
                                                        if(C <= V){
                                                            Tuple negativeTuple({Y,C,X,C1,C2,V,V1},_aux_1);
                                                            const Tuple* tuple7 = factory.find(negativeTuple);
                                                            if(tuple7 == NULL)
                                                                tuple7 = &negativeTuple;
                                                            else{
                                                                if(tuple7->isTrue())
                                                                    tuple7 = NULL;
                                                                else if(tuple7->isUndef()){
                                                                    if(tupleU == NULL){
                                                                        tupleU = tuple7;
                                                                        tupleUNegated=true;
                                                                    }else{
                                                                        if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple7))
                                                                        tuple7=NULL;
                                                                    }
                                                                }
                                                            }
                                                            if(tuple7!=NULL){
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
                                                                        if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(factory.find(*tuple7) != NULL && tuple7!=tupleU){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                                        if(!itReason.second && itReason.first->second.get()->empty())
                                                                            itReason.first->second=shared_reason;
                                                                    }
                                                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                                        if(tuple5!=NULL){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(tuple7!=NULL){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        reasonForLiteral[-startVar]=shared_reason;
                                                                        handleConflict(-startVar, propagatedLiterals);
                                                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                                                    }else propagatedLiterals.push_back(1);
                                                                    return;
                                                                }
                                                            }
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
                        if(starter.getPredicateName() == _max_cost && startVar > 0){
                            int V = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &preachable_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ureachable_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                    int X = tuple1->at(0);
                                    int C1 = tuple1->at(1);
                                    const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &uselected_path_0_.getValuesVec({X});
                                    else if(tupleU->getPredicateName() == _selected_path && !tupleUNegated)
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
                                            if(tupleU->at(0) == X)
                                                tuple2 = tupleU;
                                        }
                                        if(tuple2!=NULL){
                                            int Y = tuple2->at(1);
                                            int C2 = tuple2->at(2);
                                            int C = C1 + C2;
                                            if(C <= V){
                                                const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                                std::vector<const Tuple*> undeRepeated;
                                                if(tupleU == NULL)
                                                    tuplesU = &umin_cost_.getValuesVec({});
                                                else if(tupleU->getPredicateName() == _min_cost && !tupleUNegated)
                                                    undeRepeated.push_back(tupleU);
                                                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                                    if(tuplesU!=&EMPTY_TUPLES_VEC)
                                                        tupleU = NULL;
                                                    const Tuple* tuple5 = NULL;
                                                    if(i<tuples->size())
                                                        tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                                    else if(i<tuples->size()+tuplesU->size()){
                                                        tupleU = tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                        tupleUNegated=false;
                                                    }else if(!undeRepeated.empty()){
                                                        tuple5 = tupleU;
                                                    }
                                                    if(tuple5!=NULL){
                                                        int V1 = tuple5->at(0);
                                                        if(C >= V1){
                                                            Tuple negativeTuple({Y,C,X,C1,C2,V,V1},_aux_1);
                                                            const Tuple* tuple7 = factory.find(negativeTuple);
                                                            if(tuple7 == NULL)
                                                                tuple7 = &negativeTuple;
                                                            else{
                                                                if(tuple7->isTrue())
                                                                    tuple7 = NULL;
                                                                else if(tuple7->isUndef()){
                                                                    if(tupleU == NULL){
                                                                        tupleU = tuple7;
                                                                        tupleUNegated=true;
                                                                    }else{
                                                                        if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple7))
                                                                        tuple7=NULL;
                                                                    }
                                                                }
                                                            }
                                                            if(tuple7!=NULL){
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
                                                                        if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(factory.find(*tuple7) != NULL && tuple7!=tupleU){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                                        if(!itReason.second && itReason.first->second.get()->empty())
                                                                            itReason.first->second=shared_reason;
                                                                    }
                                                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                                        if(tuple5!=NULL){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(tuple7!=NULL){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        reasonForLiteral[-startVar]=shared_reason;
                                                                        handleConflict(-startVar, propagatedLiterals);
                                                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                                                    }else propagatedLiterals.push_back(1);
                                                                    return;
                                                                }
                                                            }
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
                        if(starter.getPredicateName() == _selected_path && startVar > 0){
                            int X = starter[0];
                            int Y = starter[1];
                            int C2 = starter[2];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &preachable_0_.getValuesVec({X});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ureachable_0_.getValuesVec({X});
                            else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                    if(tupleU->at(0) == X)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int C1 = tuple1->at(1);
                                    int C = C1 + C2;
                                    const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &umax_cost_.getValuesVec({});
                                    else if(tupleU->getPredicateName() == _max_cost && !tupleUNegated)
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
                                            tuple3 = tupleU;
                                        }
                                        if(tuple3!=NULL){
                                            int V = tuple3->at(0);
                                            if(C <= V){
                                                const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                                std::vector<const Tuple*> undeRepeated;
                                                if(tupleU == NULL)
                                                    tuplesU = &umin_cost_.getValuesVec({});
                                                else if(tupleU->getPredicateName() == _min_cost && !tupleUNegated)
                                                    undeRepeated.push_back(tupleU);
                                                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                                    if(tuplesU!=&EMPTY_TUPLES_VEC)
                                                        tupleU = NULL;
                                                    const Tuple* tuple5 = NULL;
                                                    if(i<tuples->size())
                                                        tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                                    else if(i<tuples->size()+tuplesU->size()){
                                                        tupleU = tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                        tupleUNegated=false;
                                                    }else if(!undeRepeated.empty()){
                                                        tuple5 = tupleU;
                                                    }
                                                    if(tuple5!=NULL){
                                                        int V1 = tuple5->at(0);
                                                        if(C >= V1){
                                                            Tuple negativeTuple({Y,C,X,C1,C2,V,V1},_aux_1);
                                                            const Tuple* tuple7 = factory.find(negativeTuple);
                                                            if(tuple7 == NULL)
                                                                tuple7 = &negativeTuple;
                                                            else{
                                                                if(tuple7->isTrue())
                                                                    tuple7 = NULL;
                                                                else if(tuple7->isUndef()){
                                                                    if(tupleU == NULL){
                                                                        tupleU = tuple7;
                                                                        tupleUNegated=true;
                                                                    }else{
                                                                        if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple7))
                                                                        tuple7=NULL;
                                                                    }
                                                                }
                                                            }
                                                            if(tuple7!=NULL){
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
                                                                        if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(factory.find(*tuple7) != NULL && tuple7!=tupleU){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                                        if(!itReason.second && itReason.first->second.get()->empty())
                                                                            itReason.first->second=shared_reason;
                                                                    }
                                                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                                        if(tuple5!=NULL){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(tuple7!=NULL){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        reasonForLiteral[-startVar]=shared_reason;
                                                                        handleConflict(-startVar, propagatedLiterals);
                                                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                                                    }else propagatedLiterals.push_back(1);
                                                                    return;
                                                                }
                                                            }
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
                        if(starter.getPredicateName() == _reachable && startVar > 0){
                            int X = starter[0];
                            int C1 = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &pselected_path_0_.getValuesVec({X});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uselected_path_0_.getValuesVec({X});
                            else if(tupleU->getPredicateName() == _selected_path && !tupleUNegated)
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
                                    if(tupleU->at(0) == X)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Y = tuple1->at(1);
                                    int C2 = tuple1->at(2);
                                    int C = C1 + C2;
                                    const std::vector<int>* tuples = &pmax_cost_.getValuesVec({});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &umax_cost_.getValuesVec({});
                                    else if(tupleU->getPredicateName() == _max_cost && !tupleUNegated)
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
                                            tuple3 = tupleU;
                                        }
                                        if(tuple3!=NULL){
                                            int V = tuple3->at(0);
                                            if(C <= V){
                                                const std::vector<int>* tuples = &pmin_cost_.getValuesVec({});
                                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                                std::vector<const Tuple*> undeRepeated;
                                                if(tupleU == NULL)
                                                    tuplesU = &umin_cost_.getValuesVec({});
                                                else if(tupleU->getPredicateName() == _min_cost && !tupleUNegated)
                                                    undeRepeated.push_back(tupleU);
                                                for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){
                                                    if(tuplesU!=&EMPTY_TUPLES_VEC)
                                                        tupleU = NULL;
                                                    const Tuple* tuple5 = NULL;
                                                    if(i<tuples->size())
                                                        tuple5 = factory.getTupleFromInternalID(tuples->at(i));
                                                    else if(i<tuples->size()+tuplesU->size()){
                                                        tupleU = tuple5 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                        tupleUNegated=false;
                                                    }else if(!undeRepeated.empty()){
                                                        tuple5 = tupleU;
                                                    }
                                                    if(tuple5!=NULL){
                                                        int V1 = tuple5->at(0);
                                                        if(C >= V1){
                                                            Tuple negativeTuple({Y,C,X,C1,C2,V,V1},_aux_1);
                                                            const Tuple* tuple7 = factory.find(negativeTuple);
                                                            if(tuple7 == NULL)
                                                                tuple7 = &negativeTuple;
                                                            else{
                                                                if(tuple7->isTrue())
                                                                    tuple7 = NULL;
                                                                else if(tuple7->isUndef()){
                                                                    if(tupleU == NULL){
                                                                        tupleU = tuple7;
                                                                        tupleUNegated=true;
                                                                    }else{
                                                                        if(tupleU->getPredicateName() != _aux_1 || !tupleUNegated || !(*tupleU == *tuple7))
                                                                        tuple7=NULL;
                                                                    }
                                                                }
                                                            }
                                                            if(tuple7!=NULL){
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
                                                                        if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(factory.find(*tuple7) != NULL && tuple7!=tupleU){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                                        if(!itReason.second && itReason.first->second.get()->empty())
                                                                            itReason.first->second=shared_reason;
                                                                    }
                                                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                                        if(tuple5!=NULL){
                                                                            int it = tuple5->getId();
                                                                            shared_reason.get()->insert(it*1);
                                                                        }
                                                                        if(tuple7!=NULL){
                                                                            int it = tuple7->getId();
                                                                            shared_reason.get()->insert(it*-1);
                                                                        }
                                                                        reasonForLiteral[-startVar]=shared_reason;
                                                                        handleConflict(-startVar, propagatedLiterals);
                                                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                                                    }else propagatedLiterals.push_back(1);
                                                                    return;
                                                                }
                                                            }
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
                    if(starter.getPredicateName() == _reachable){
                        int Y = starter.at(0);
                        int C = starter.at(1);
                        Tuple* head = factory.find({Y}, _reached);
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
                            const std::vector<int>* tuples = &preachable_0_.getValuesVec({Y});
                            const std::vector<int>* tuplesU = &ureachable_0_.getValuesVec({Y});
                            if(head != NULL && head->isTrue()){
                                if(tuples->size() == 0 && tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        int itHead = head->getId();
                                        const std::vector<int>* tuplesF = &freachable_0_.getValuesVec({Y});
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
                                        const std::vector<int>* tuplesF = &freachable_0_.getValuesVec({Y});
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
                                        const std::vector<int>* tuplesF = &freachable_0_.getValuesVec({Y});
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
                    }else if(starter.getPredicateName() == _reached){
                        int Y = starter.at(0);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        const std::vector<int>* tuples = &preachable_0_.getValuesVec({Y});
                        const std::vector<int>* tuplesU = &ureachable_0_.getValuesVec({Y});
                        if(startVar > 0){
                            if(tuples->size()==0){
                                if(tuplesU->size() == 0){
                                    if(currentDecisionLevel>0){
                                        const std::vector<int>* tuplesF = &freachable_0_.getValuesVec({Y});
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
                                        const std::vector<int>* tuplesF = &freachable_0_.getValuesVec({Y});
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
                        if(starter.getPredicateName() == _reached && startVar < 0){
                            int Y = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({Y},_end);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _end || tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _end && startVar > 0){
                            int Y = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            Tuple negativeTuple({Y},_reached);
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
                                        if(tupleU->getPredicateName() != _reached || !tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                    }else propagatedLiterals.push_back(1);
                                    return;
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                    {
                        if(starter.getPredicateName() == _bound && startVar > 0){
                            int B = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &pend_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &uend_.getValuesVec({});
                            else if(tupleU->getPredicateName() == _end && !tupleUNegated)
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
                                    int X = tuple1->at(0);
                                    const std::vector<int>* tuples = &preachable_0_.getValuesVec({X});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &ureachable_0_.getValuesVec({X});
                                    else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                            if(tupleU->at(0) == X)
                                                tuple2 = tupleU;
                                        }
                                        if(tuple2!=NULL){
                                            int C = tuple2->at(1);
                                            if(C < B){
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
                                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                        if(!itReason.second && itReason.first->second.get()->empty())
                                                            itReason.first->second=shared_reason;
                                                    }
                                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
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
                        if(starter.getPredicateName() == _reachable && startVar > 0){
                            int X = starter[0];
                            int C = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({X},_end);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _end || tupleUNegated || !(*tupleU == *tuple1))
                                        tuple1=NULL;
                                    }
                                }
                            }
                            if(tuple1!=NULL){
                                const std::vector<int>* tuples = &pbound_.getValuesVec({});
                                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ubound_.getValuesVec({});
                                else if(tupleU->getPredicateName() == _bound && !tupleUNegated)
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
                                        tuple2 = tupleU;
                                    }
                                    if(tuple2!=NULL){
                                        int B = tuple2->at(0);
                                        if(C < B){
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
                                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                    if(!itReason.second && itReason.first->second.get()->empty())
                                                        itReason.first->second=shared_reason;
                                                }
                                                if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                    for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
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
                        if(starter.getPredicateName() == _end && startVar > 0){
                            int X = starter[0];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const std::vector<int>* tuples = &preachable_0_.getValuesVec({X});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ureachable_0_.getValuesVec({X});
                            else if(tupleU->getPredicateName() == _reachable && !tupleUNegated)
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
                                    if(tupleU->at(0) == X)
                                        tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int C = tuple1->at(1);
                                    const std::vector<int>* tuples = &pbound_.getValuesVec({});
                                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                    std::vector<const Tuple*> undeRepeated;
                                    if(tupleU == NULL)
                                        tuplesU = &ubound_.getValuesVec({});
                                    else if(tupleU->getPredicateName() == _bound && !tupleUNegated)
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
                                            tuple2 = tupleU;
                                        }
                                        if(tuple2!=NULL){
                                            int B = tuple2->at(0);
                                            if(C < B){
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
                                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                        if(!itReason.second && itReason.first->second.get()->empty())
                                                            itReason.first->second=shared_reason;
                                                    }
                                                    if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                                        for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
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
                        if(starter.getPredicateName() == _sup_1 && startVar < 0){
                            int X0 = starter[0];
                            int X1 = starter[1];
                            const Tuple* tupleU = NULL;
                            bool tupleUNegated = false;
                            std::vector<std::pair<const Tuple*,bool>> internalProps;
                            const Tuple* tuple1 = factory.find({X0,X1},_reachable);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _reachable || tupleUNegated || !(*tupleU == *tuple1))
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
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                        }
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
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
                            const Tuple* tuple1 = factory.find({X0,X1},_reachable);
                            if(tuple1!=NULL){
                                if(tuple1->isFalse())
                                tuple1=NULL;
                                else if(tuple1->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple1;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != _reachable || tupleUNegated || !(*tupleU == *tuple1))
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
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                        }
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                        if(starter.getPredicateName() == _reachable && startVar > 0){
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
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                        }
                                        if(tupleU->getPredicateName() != _reachable && tupleU->getPredicateName() != _sup_0 && tupleU->getPredicateName() != _reached && tupleU->getPredicateName() != _aux_0 && tupleU->getPredicateName() != _sup_1 && tupleU->getPredicateName() != _aux_1)
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
                                            reasonForLiteral[-startVar]=shared_reason;
                                            handleConflict(-startVar, propagatedLiterals);
                                            for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}
                                        }else propagatedLiterals.push_back(1);
                                        return;
                                    }
                                }
                            }
                            for(auto pair : internalProps)
                                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }
                if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
            }
            }
