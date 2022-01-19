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
const std::string _aggr_id0 = "aggr_id0";
const std::string _aggr_id1 = "aggr_id1";
const std::string _aggr_id2 = "aggr_id2";
const std::string _aggr_id3 = "aggr_id3";
const std::string _aux0 = "aux0";
const std::string _aux2 = "aux2";
const std::string _body0 = "body0";
const std::string _node = "node";
const std::string _pathE = "pathE";
const std::string _r = "r";
const std::string _reached = "reached";
const std::string _start = "start";
const std::string _sup_0 = "sup_0";
const std::string _sup_1 = "sup_1";
const std::string _sup_2 = "sup_2";
const std::string _sup_3 = "sup_3";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
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
AuxMap<0> pnode_({});
AuxMap<0> unode_({});
AuxMap<0> fnode_({});
AuxMap<0> pstart_({});
AuxMap<0> ustart_({});
AuxMap<0> fstart_({});
AuxMap<32> pr_0_({0});
AuxMap<32> ur_0_({0});
AuxMap<32> fr_0_({0});
AuxMap<0> pr_({});
AuxMap<0> ur_({});
AuxMap<0> fr_({});
AuxMap<32> ppathE_0_({0});
AuxMap<32> upathE_0_({0});
AuxMap<32> fpathE_0_({0});
AuxMap<0> psup_0_({});
AuxMap<0> usup_0_({});
AuxMap<0> fsup_0_({});
AuxMap<0> ppathE_({});
AuxMap<0> upathE_({});
AuxMap<0> fpathE_({});
AuxMap<0> psup_1_({});
AuxMap<0> usup_1_({});
AuxMap<0> fsup_1_({});
AuxMap<64> paux0_0_1_({0,1});
AuxMap<64> uaux0_0_1_({0,1});
AuxMap<64> faux0_0_1_({0,1});
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<64> paux0_0_2_({0,2});
AuxMap<64> uaux0_0_2_({0,2});
AuxMap<64> faux0_0_2_({0,2});
AuxMap<64> paux0_1_2_({1,2});
AuxMap<64> uaux0_1_2_({1,2});
AuxMap<64> faux0_1_2_({1,2});
AuxMap<32> pr_1_({1});
AuxMap<32> ur_1_({1});
AuxMap<32> fr_1_({1});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<32> paggr_id0_0_({0});
AuxMap<32> uaggr_id0_0_({0});
AuxMap<32> faggr_id0_0_({0});
AuxMap<32> ppathE_1_({1});
AuxMap<32> upathE_1_({1});
AuxMap<32> fpathE_1_({1});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<32> paggr_id1_0_({0});
AuxMap<32> uaggr_id1_0_({0});
AuxMap<32> faggr_id1_0_({0});
AuxMap<0> psup_2_({});
AuxMap<0> usup_2_({});
AuxMap<0> fsup_2_({});
AuxMap<0> preached_({});
AuxMap<0> ureached_({});
AuxMap<0> freached_({});
AuxMap<32> paux2_0_({0});
AuxMap<32> uaux2_0_({0});
AuxMap<32> faux2_0_({0});
AuxMap<0> paux2_({});
AuxMap<0> uaux2_({});
AuxMap<0> faux2_({});
AuxMap<32> paux2_1_({1});
AuxMap<32> uaux2_1_({1});
AuxMap<32> faux2_1_({1});
AuxMap<0> psup_3_({});
AuxMap<0> usup_3_({});
AuxMap<0> fsup_3_({});
AuxMap<0> pbody0_({});
AuxMap<0> ubody0_({});
AuxMap<0> fbody0_({});
AuxMap<0> paggr_id2_({});
AuxMap<0> uaggr_id2_({});
AuxMap<0> faggr_id2_({});
AuxMap<32> paggr_id2_0_({0});
AuxMap<32> uaggr_id2_0_({0});
AuxMap<32> faggr_id2_0_({0});
AuxMap<0> paggr_id3_({});
AuxMap<0> uaggr_id3_({});
AuxMap<0> faggr_id3_({});
AuxMap<32> paggr_id3_0_({0});
AuxMap<32> uaggr_id3_0_({0});
AuxMap<32> faggr_id3_0_({0});
void Executor::handleConflict(int literal,std::vector<int>& propagatedLiterals){
    if(currentDecisionLevel <= 0){
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
    if(insertResult.first->getPredicateName() == &_body0){
        fbody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_node){
        fnode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_start){
        fstart_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_3){
        fsup_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_2){
        fsup_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id3){
        faggr_id3_.insert2Vec(*insertResult.first);
        faggr_id3_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_r){
        fr_.insert2Vec(*insertResult.first);
        fr_0_.insert2Vec(*insertResult.first);
        fr_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id2){
        faggr_id2_.insert2Vec(*insertResult.first);
        faggr_id2_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pathE){
        fpathE_.insert2Vec(*insertResult.first);
        fpathE_0_.insert2Vec(*insertResult.first);
        fpathE_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2Vec(*insertResult.first);
        faux0_0_1_.insert2Vec(*insertResult.first);
        faux0_0_2_.insert2Vec(*insertResult.first);
        faux0_1_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_0){
        fsup_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_reached){
        freached_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux2){
        faux2_.insert2Vec(*insertResult.first);
        faux2_0_.insert2Vec(*insertResult.first);
        faux2_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2Vec(*insertResult.first);
        faggr_id0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_1){
        fsup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2Vec(*insertResult.first);
        faggr_id1_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_body0){
        pbody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_node){
        pnode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_start){
        pstart_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_3){
        psup_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_2){
        psup_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id3){
        paggr_id3_.insert2Vec(*insertResult.first);
        paggr_id3_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_r){
        pr_.insert2Vec(*insertResult.first);
        pr_0_.insert2Vec(*insertResult.first);
        pr_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id2){
        paggr_id2_.insert2Vec(*insertResult.first);
        paggr_id2_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pathE){
        ppathE_.insert2Vec(*insertResult.first);
        ppathE_0_.insert2Vec(*insertResult.first);
        ppathE_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2Vec(*insertResult.first);
        paux0_0_1_.insert2Vec(*insertResult.first);
        paux0_0_2_.insert2Vec(*insertResult.first);
        paux0_1_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_0){
        psup_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_reached){
        preached_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux2){
        paux2_.insert2Vec(*insertResult.first);
        paux2_0_.insert2Vec(*insertResult.first);
        paux2_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2Vec(*insertResult.first);
        paggr_id0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_1){
        psup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2Vec(*insertResult.first);
        paggr_id1_0_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_body0){
        ubody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_node){
        unode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_start){
        ustart_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_3){
        usup_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_2){
        usup_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id3){
        uaggr_id3_.insert2Vec(*insertResult.first);
        uaggr_id3_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_r){
        ur_.insert2Vec(*insertResult.first);
        ur_0_.insert2Vec(*insertResult.first);
        ur_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id2){
        uaggr_id2_.insert2Vec(*insertResult.first);
        uaggr_id2_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pathE){
        upathE_.insert2Vec(*insertResult.first);
        upathE_0_.insert2Vec(*insertResult.first);
        upathE_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2Vec(*insertResult.first);
        uaux0_0_1_.insert2Vec(*insertResult.first);
        uaux0_0_2_.insert2Vec(*insertResult.first);
        uaux0_1_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_0){
        usup_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_reached){
        ureached_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux2){
        uaux2_.insert2Vec(*insertResult.first);
        uaux2_0_.insert2Vec(*insertResult.first);
        uaux2_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2Vec(*insertResult.first);
        uaggr_id0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_1){
        usup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2Vec(*insertResult.first);
        uaggr_id1_0_.insert2Vec(*insertResult.first);
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
    if(var<0) falseLits.push_back(var);
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
std::unordered_map<int,std::unordered_set<int>> supportedAux1;
std::unordered_map<int,std::unordered_set<int>> supportedLiterals1;
std::unordered_map<int,int> sourcePointers1;
std::unordered_set<int> unfoundedSetForComponent1;
void propFoundessForComponent1(std::unordered_set<int>& founded,int foundedLiteral){
    std::vector<int> foundedStack({foundedLiteral});
    while(!foundedStack.empty()){
        Tuple* starter = factory.getTupleFromInternalID(foundedStack.back());
        foundedStack.pop_back();
        if(starter->getPredicateName() == &_sup_1){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* head = factory.find({X,Y},&_r);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent1.count(head->getId())!=0){
                auto oldSP = sourcePointers1.find(head->getId());
                if(oldSP!=sourcePointers1.end())
                    supportedLiterals1[oldSP->second].erase(head->getId());
                supportedLiterals1[starter->getId()].insert(head->getId());
                sourcePointers1[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_aux0){
            int X=starter->at(0);
            int Y=starter->at(1);
            int Z=starter->at(2);
            Tuple* head = factory.find({X,Y},&_sup_1);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent1.count(head->getId())!=0){
                auto oldSP = sourcePointers1.find(head->getId());
                if(oldSP!=sourcePointers1.end())
                    supportedLiterals1[oldSP->second].erase(head->getId());
                supportedLiterals1[starter->getId()].insert(head->getId());
                sourcePointers1[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_r){
            int X=starter->at(0);
            int Z=starter->at(1);
            const std::vector<int>* tuples = &ppathE_0_.getValuesVec({Z});
            const std::vector<int>* tuplesU = &upathE_0_.getValuesVec({Z});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(Z == tuple1->at(0)){
                    int Y=tuple1->at(1);
                    Tuple* head = factory.find({X,Y,Z},&_aux0);
                    if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent1.count(head->getId())!=0){
                        foundedStack.push_back(head->getId());
                        founded.insert(head->getId());
                        supportedAux1[starter->getId()].insert(head->getId());
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_pathE){
            int Z=starter->at(0);
            int Y=starter->at(1);
            const std::vector<int>* tuples = &pr_1_.getValuesVec({Z});
            const std::vector<int>* tuplesU = &ur_1_.getValuesVec({Z});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X=tuple1->at(0);
                if(Z == tuple1->at(1)){
                    if(unfoundedSetForComponent1.count(tuple1->getId())==0 || founded.count(tuple1->getId())!=0){
                        Tuple* head = factory.find({X,Y,Z},&_aux0);
                        if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent1.count(head->getId())!=0){
                            foundedStack.push_back(head->getId());
                            founded.insert(head->getId());
                            if(tuple1!=NULL){
                                supportedAux1[tuple1->getId()].insert(head->getId());
                            }
                        }
                    }
                }
            }
        }
    }//close while 
}//close function
void unfoundedPropagatorForComponent1(std::vector<int>& literalToPropagate,Executor* executor){
    std::unordered_set<int> founded;
    for(int id : unfoundedSetForComponent1){
        Tuple* starter = factory.getTupleFromInternalID(id);
        if(founded.count(id)!=0) continue;
        bool spFound=false;
        if(!spFound && starter->getPredicateName() == &_r && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* body = factory.find({X,Y},&_sup_0);
            if(body!=NULL && !body->isFalse()){
                auto oldSP = sourcePointers1.find(starter->getId());
                if(oldSP!=sourcePointers1.end())
                    supportedLiterals1[oldSP->second].erase(starter->getId());
                sourcePointers1[starter->getId()]=body->getId();
                supportedLiterals1[body->getId()].insert(starter->getId());
                founded.insert(starter->getId());
                propFoundessForComponent1(founded,starter->getId());
                spFound=true;
            }
        }
        if(!spFound && starter->getPredicateName() == &_r && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* body = factory.find({X,Y},&_sup_1);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent1.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers1.find(starter->getId());
                    if(oldSP!=sourcePointers1.end())
                        supportedLiterals1[oldSP->second].erase(starter->getId());
                    sourcePointers1[starter->getId()]=body->getId();
                    supportedLiterals1[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent1(founded,starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_sup_1 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y=starter->at(1);
            const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({X,Y});
            const std::vector<int>* tuplesU = &uaux0_0_1_.getValuesVec({X,Y});
            for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){
                Tuple* body = NULL;
                if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));
                else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(body!=NULL){
                    if(unfoundedSetForComponent1.count(body->getId())==0 || founded.count(body->getId())!=0){
                        auto oldSP = sourcePointers1.find(starter->getId());
                        if(oldSP!=sourcePointers1.end())
                            supportedLiterals1[oldSP->second].erase(starter->getId());
                        sourcePointers1[starter->getId()]=body->getId();
                        supportedLiterals1[body->getId()].insert(starter->getId());
                        founded.insert(starter->getId());
                        propFoundessForComponent1(founded,starter->getId());
                        spFound=true;
                    }
                }
            }
        }
    } //close unfounded for
    for(int lit : founded) unfoundedSetForComponent1.erase(lit);
    if(!unfoundedSetForComponent1.empty()){
        int conflictDetected=0;
        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
        std::vector<int> propLiterals({currentDecisionLevel});
        for(int lit : unfoundedSetForComponent1){
            Tuple* starter = factory.getTupleFromInternalID(lit);
            if(starter == NULL) continue;
            if(currentDecisionLevel > 0){
                if(starter->getPredicateName() == &_r){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    reasonForLiteral[-lit]=shared_reason;
                    propLiterals.push_back(-lit);
                    int X=starter->at(0);
                    int Y=starter->at(1);
                    Tuple* tuple = factory.find({X,Y},&_sup_0);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_r){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    reasonForLiteral[-lit]=shared_reason;
                    propLiterals.push_back(-lit);
                    int X=starter->at(0);
                    int Y=starter->at(1);
                    Tuple* tuple = factory.find({X,Y},&_sup_1);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_sup_1){
                    int X=starter->at(0);
                    int Y=starter->at(1);
                    const std::vector<int>* tuplesF = &faux0_0_1_.getValuesVec({X,Y});
                    for(unsigned i=0; i<tuplesF->size();i++){
                        Tuple* tuple = factory.getTupleFromInternalID(tuplesF->at(i));
                        if(tuple!=NULL){
                            shared_reason.get()->insert(-tuple->getId());
                        }
                    }
                }
            }
        }
        if(conflictDetected!=0) {
            executor->handleConflict(conflictDetected,literalToPropagate);
            for(int i=1; i<propLiterals.size(); i++) reasonForLiteral[propLiterals[i]]->clear();
        }else{
            executor->executeProgramOnFacts(propLiterals,literalToPropagate,true);
        }
        unfoundedSetForComponent1.clear();
    }//close if empty unfounded set
}// close unfoundedPropagatorForComponent
void checkFoundness(){
    std::unordered_set<int> visited;
    while(!falseLits.empty()){
        int current = falseLits.back();
        falseLits.pop_back();
        if(current > 0 || visited.count(current)!=0) continue;
        visited.insert(current);
        const Tuple* tuple = factory.getTupleFromInternalID(-current);
        if(tuple != NULL){
            if(!tuple->isFalse()){
                auto it = predsToUnfoundedSet.find(tuple->getPredicateName());
                if(it!=predsToUnfoundedSet.end())
                    it->second->insert(tuple->getId());
            }
            {
                auto supported = supportedLiterals1.find(tuple->getId());
                if(supported!=supportedLiterals1.end()){
                    for(int lit : supported->second){
                        Tuple* removingLit = factory.getTupleFromInternalID(lit);
                        auto unfoundeRemovingLit = predsToUnfoundedSet.find(removingLit->getPredicateName());
                        if(!removingLit->isFalse() && unfoundeRemovingLit!=predsToUnfoundedSet.end() && unfoundeRemovingLit->second->count(removingLit->getId())==0)
                            falseLits.push_back(-removingLit->getId());
                    }//close for
                }//close if
                auto supAux = supportedAux1.find(tuple->getId());
                if(supAux!=supportedAux1.end()){
                    std::vector<int> toRemove;
                    for(int lit : supAux->second){
                        Tuple* removingLit = factory.getTupleFromInternalID(lit);
                        auto unfoundeRemovingLit = predsToUnfoundedSet.find(removingLit->getPredicateName());
                        if(!removingLit->isFalse() && unfoundeRemovingLit!=predsToUnfoundedSet.end() && unfoundeRemovingLit->second->count(removingLit->getId())==0)
                            falseLits.push_back(-removingLit->getId());
                    }//close for
                }//close if
            }//close local scope
        }//close if
    }//close while
}//close function
void Executor::checkUnfoundedSets(std::vector<int>& literalsToPropagate,Executor* executor){
    checkFoundness();
    unfoundedPropagatorForComponent1(literalsToPropagate,executor);
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {
        const std::vector<int>* tuples = &pnode_.getValuesVec({});
        const std::vector<int>* tuplesU = &unode_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            Tuple* aggr_id = factory.addNewInternalTuple({X},&_aggr_id3);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pnode_.getValuesVec({});
        const std::vector<int>* tuplesU = &unode_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            Tuple* aggr_id = factory.addNewInternalTuple({X},&_aggr_id1);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pnode_.getValuesVec({});
        const std::vector<int>* tuplesU = &unode_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            Tuple* aggr_id = factory.addNewInternalTuple({X},&_aggr_id0);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pnode_.getValuesVec({});
        const std::vector<int>* tuplesU = &unode_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple0->at(0);
            Tuple* tuple1 = factory.find({X},&_aggr_id0);
            if(tuple1!=NULL && !tuple1->isFalse()){
                Tuple* tuple2 = factory.find({X},&_aggr_id1);
                if(tuple2==NULL || !tuple2->isTrue()){
                    Tuple* saving1 = factory.addNewInternalTuple({X},&_start);
                    const auto& insertResult = saving1->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving1->getId());
                        insertUndef(insertResult);
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pnode_.getValuesVec({});
        const std::vector<int>* tuplesU = &unode_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple0->at(0);
            Tuple* tuple1 = factory.find({X},&_start);
            if(tuple1==NULL || !tuple1->isTrue()){
                Tuple* saving1 = factory.addNewInternalTuple({X},&_body0);
                const auto& insertResult = saving1->setStatus(Undef);
                if(insertResult.second){
                    factory.removeFromCollisionsList(saving1->getId());
                    insertUndef(insertResult);
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pbody0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ubody0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            Tuple* aggr_id = factory.addNewInternalTuple({X},&_aggr_id2);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    //---------------------------------Recursive Component---------------------------------
    {
        std::vector<int> generationStack;
        {
            const std::vector<int>* tuples = &ppathE_.getValuesVec({});
            const std::vector<int>* tuplesU = &upathE_.getValuesVec({});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple = NULL;
                if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
                else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X = tuple->at(0);
                int Y = tuple->at(1);
                Tuple* saving2 = factory.addNewInternalTuple({X,Y},&_sup_0);
                const auto& insertResult = saving2->setStatus(Undef);
                if(insertResult.second){
                    factory.removeFromCollisionsList(saving2->getId());
                    insertUndef(insertResult);
                    Tuple* saving0 = factory.addNewInternalTuple({X,Y},&_r);
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
            if(starter->getPredicateName() == &_r){
                int X = starter->at(0);
                int Z = starter->at(1);
                const std::vector<int>* tuples = &ppathE_0_.getValuesVec({Z});
                const std::vector<int>* tuplesU = &upathE_0_.getValuesVec({Z});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple1 = NULL;
                    if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    if(tuple1->at(0) == Z){
                        int Y = tuple1->at(1);
                        Tuple* saving2 = factory.addNewInternalTuple({X,Y,Z},&_aux0);
                        const auto& insertResult = saving2->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving2->getId());
                            insertUndef(insertResult);
                            Tuple* saving1 = factory.addNewInternalTuple({X,Y},&_sup_1);
                            const auto& insertResult = saving1->setStatus(Undef);
                            if(insertResult.second){
                                factory.removeFromCollisionsList(saving1->getId());
                                insertUndef(insertResult);
                                Tuple* saving0 = factory.addNewInternalTuple({X,Y},&_r);
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
    //---------------------------------Recursive Component---------------------------------
    {
        predsToUnfoundedSet[&_r]=&unfoundedSetForComponent1;
        const std::vector<int>* tuples = &pr_.getValuesVec({});
        const std::vector<int>* tuplesU = &ur_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent1.insert(tuples->at(i));
            else unfoundedSetForComponent1.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_sup_1]=&unfoundedSetForComponent1;
        const std::vector<int>* tuples = &psup_1_.getValuesVec({});
        const std::vector<int>* tuplesU = &usup_1_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent1.insert(tuples->at(i));
            else unfoundedSetForComponent1.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_aux0]=&unfoundedSetForComponent1;
        const std::vector<int>* tuples = &paux0_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaux0_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent1.insert(tuples->at(i));
            else unfoundedSetForComponent1.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        const std::vector<int>* tuples = &pstart_.getValuesVec({});
        const std::vector<int>* tuplesU = &ustart_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int Y = tuple0->at(0);
            const std::vector<int>* tuples = &pr_0_.getValuesVec({Y});
            const std::vector<int>* tuplesU = &ur_0_.getValuesVec({Y});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(tuple1->at(0) == Y){
                    int X = tuple1->at(1);
                    Tuple* saving3 = factory.addNewInternalTuple({X,Y},&_aux2);
                    const auto& insertResult = saving3->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving3->getId());
                        insertUndef(insertResult);
                        Tuple* saving1 = factory.addNewInternalTuple({X},&_sup_2);
                        const auto& insertResult = saving1->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving1->getId());
                            insertUndef(insertResult);
                            Tuple* saving0 = factory.addNewInternalTuple({X},&_reached);
                            const auto& insertResult = saving0->setStatus(Undef);
                            if(insertResult.second){
                                factory.removeFromCollisionsList(saving0->getId());
                                insertUndef(insertResult);
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pstart_.getValuesVec({});
        const std::vector<int>* tuplesU = &ustart_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            Tuple* saving2 = factory.addNewInternalTuple({X},&_sup_3);
            const auto& insertResult = saving2->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(saving2->getId());
                insertUndef(insertResult);
                Tuple* saving0 = factory.addNewInternalTuple({X},&_reached);
                const auto& insertResult = saving0->setStatus(Undef);
                if(insertResult.second){
                    factory.removeFromCollisionsList(saving0->getId());
                    insertUndef(insertResult);
                }
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
    psup_3_.clear();
    psup_2_.clear();
    paggr_id3_.clear();
    paggr_id3_0_.clear();
    paggr_id2_.clear();
    paggr_id2_0_.clear();
    psup_0_.clear();
    paggr_id0_.clear();
    paggr_id0_0_.clear();
    psup_1_.clear();
    paggr_id1_.clear();
    paggr_id1_0_.clear();
    fsup_3_.clear();
    fsup_2_.clear();
    faggr_id3_.clear();
    faggr_id3_0_.clear();
    faggr_id2_.clear();
    faggr_id2_0_.clear();
    fsup_0_.clear();
    faggr_id0_.clear();
    faggr_id0_0_.clear();
    fsup_1_.clear();
    faggr_id1_.clear();
    faggr_id1_0_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["aggr_id2"] = &_aggr_id2;
    stringToUniqueStringPointer["aggr_id3"] = &_aggr_id3;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    stringToUniqueStringPointer["aux2"] = &_aux2;
    stringToUniqueStringPointer["body0"] = &_body0;
    stringToUniqueStringPointer["node"] = &_node;
    stringToUniqueStringPointer["pathE"] = &_pathE;
    stringToUniqueStringPointer["r"] = &_r;
    stringToUniqueStringPointer["reached"] = &_reached;
    stringToUniqueStringPointer["start"] = &_start;
    stringToUniqueStringPointer["sup_0"] = &_sup_0;
    stringToUniqueStringPointer["sup_1"] = &_sup_1;
    stringToUniqueStringPointer["sup_2"] = &_sup_2;
    stringToUniqueStringPointer["sup_3"] = &_sup_3;
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
void Executor::printInternalLiterals(){
    for(int internalId : preached_.getValuesVec({})){
        std::cout << factory.getTupleFromInternalID(internalId)->toString()<<" ";
    }
    for(int internalId : pstart_.getValuesVec({})){
        std::cout << factory.getTupleFromInternalID(internalId)->toString()<<" ";
    }
    for(int internalId : pr_.getValuesVec({})){
        std::cout << factory.getTupleFromInternalID(internalId)->toString()<<" ";
    }
    std::cout << std::endl;
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
    currentDecisionLevel=decisionLevel;
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
    if(decisionLevel>-1) {
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            const std::vector<int>* trueHeads = &psup_0_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y}, &_pathE);
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
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y}, &_pathE);
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
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                const Tuple* currentBody = factory.find({X, Y}, &_pathE);
                if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(currentBody!=NULL && currentBody->isTrue())
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 0){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 0){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 0 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 0){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 0+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 0+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 0+1 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 0+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
                const std::vector<int>* tuples = &pnode_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &unode_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_node && !tupleUNegated)
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
                        Tuple negativeTuple({X},&_reached);
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
                                    if(tupleU->getPredicateName() != &_reached || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            const std::vector<int>* tuples = &paggr_id3_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id3_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id3_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_0_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_0_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 1+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_0_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_0_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_0_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 1+1 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_0_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_0_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_0_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
                const std::vector<int>* tuples = &pr_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ur_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_r && !tupleUNegated)
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
                        Tuple negativeTuple({X0,X1},&_sup_0);
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
                                    if(tupleU->getPredicateName() != &_sup_0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0,X1},&_sup_1);
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
                                        if(tupleU->getPredicateName() != &_sup_1 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &preached_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ureached_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_reached && !tupleUNegated)
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
                        Tuple negativeTuple({X0},&_sup_2);
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
                                    if(tupleU->getPredicateName() != &_sup_2 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0},&_sup_3);
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
                                        if(tupleU->getPredicateName() != &_sup_3 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pnode_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &unode_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_node && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({X},&_aggr_id3);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_aggr_id3 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                        int X = tuple0->at(0);
                        const Tuple* tuple1 = factory.find({X},&_aggr_id2);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_aggr_id2 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pnode_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &unode_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_node && !tupleUNegated)
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
                        Tuple negativeTuple({X},&_start);
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
                                    if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X},&_body0);
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
                                        if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                        int X = tuple0->at(0);
                        const Tuple* tuple1 = factory.find({X},&_start);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                        int X = tuple0->at(0);
                        Tuple negativeTuple({X},&_node);
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
                                    if(tupleU->getPredicateName() != &_node || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &psup_3_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usup_3_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_sup_3 && !tupleUNegated)
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
                        Tuple negativeTuple({X},&_reached);
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
                                    if(tupleU->getPredicateName() != &_reached || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        const std::vector<int>* tuples = &pr_0_.getValuesVec({Y});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ur_0_.getValuesVec({Y});
                        else if(tupleU->getPredicateName() == &_r && !tupleUNegated)
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
                                if(tupleU->at(0) == Y)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int X = tuple1->at(1);
                                Tuple negativeTuple({X,Y},&_aux2);
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
                                            if(tupleU->getPredicateName() != &_aux2 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &paux2_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux2_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux2 && !tupleUNegated)
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
                        Tuple negativeTuple({Y,X},&_r);
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
                                    if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &paux2_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux2_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux2 && !tupleUNegated)
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
                        Tuple negativeTuple({Y},&_start);
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
                                    if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &psup_2_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usup_2_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_sup_2 && !tupleUNegated)
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
                        Tuple negativeTuple({X},&_reached);
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
                                    if(tupleU->getPredicateName() != &_reached || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        const std::vector<int>* tuples = &pstart_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ustart_.getValuesVec({});
                        else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                                int Y = tuple1->at(0);
                                if(X != Y){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pnode_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &unode_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_node && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({X},&_aggr_id0);
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
                            Tuple negativeTuple({X},&_aggr_id1);
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
                                Tuple negativeTuple({X},&_start);
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
                                            if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({X},&_aggr_id1);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        Tuple negativeTuple({X},&_aggr_id0);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        Tuple negativeTuple({X},&_node);
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
                                    if(tupleU->getPredicateName() != &_node || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &pr_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ur_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_r && !tupleUNegated)
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
                        int Z = tuple0->at(1);
                        const std::vector<int>* tuples = &ppathE_0_.getValuesVec({Z});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &upathE_0_.getValuesVec({Z});
                        else if(tupleU->getPredicateName() == &_pathE && !tupleUNegated)
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
                                if(tupleU->at(0) == Z)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int Y = tuple1->at(1);
                                Tuple negativeTuple({X,Y,Z},&_aux0);
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
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                        int X = tuple0->at(0);
                        int Y = tuple0->at(1);
                        int Z = tuple0->at(2);
                        Tuple negativeTuple({Z,Y},&_pathE);
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
                                    if(tupleU->getPredicateName() != &_pathE || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                        int X = tuple0->at(0);
                        int Y = tuple0->at(1);
                        int Z = tuple0->at(2);
                        Tuple negativeTuple({X,Z},&_r);
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
                                    if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                else if(tupleU->getPredicateName() == &_sup_1 && !tupleUNegated)
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
                        Tuple negativeTuple({X,Y},&_r);
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
                                    if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                const std::vector<int>* tuples = &psup_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usup_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_sup_0 && !tupleUNegated)
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
                        Tuple negativeTuple({X,Y},&_r);
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
                                    if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({X, Y});
                const std::vector<int>* tuplesU = &uaux0_0_1_.getValuesVec({X, Y});
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
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({X, Y});
                const std::vector<int>* tuplesU = &uaux0_0_1_.getValuesVec({X, Y});
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
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({X, Y});
                const std::vector<int>* tuplesU = &uaux0_0_1_.getValuesVec({X, Y});
                if(tuples->size() > 0)
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(tuplesU->size()==0)
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* trueHeads = &psup_2_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = currentHead->at(0);
                const std::vector<int>* tuples = &paux2_0_.getValuesVec({X});
                const std::vector<int>* tuplesU = &uaux2_0_.getValuesVec({X});
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
                int X = currentHead->at(0);
                const std::vector<int>* tuples = &paux2_0_.getValuesVec({X});
                const std::vector<int>* tuplesU = &uaux2_0_.getValuesVec({X});
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
                int X = currentHead->at(0);
                const std::vector<int>* tuples = &paux2_0_.getValuesVec({X});
                const std::vector<int>* tuplesU = &uaux2_0_.getValuesVec({X});
                if(tuples->size() > 0)
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(tuplesU->size()==0)
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* trueHeads = &psup_3_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = currentHead->at(0);
                Tuple* currentBody = factory.find({X}, &_start);
                if(!currentBody->isUndef() && !currentBody->isTrue()){
                    propagatedLiterals.push_back(1);
                    return;
                }else if(currentBody->isUndef()){
                    propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* falseHeads = &fsup_3_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                int X = currentHead->at(0);
                Tuple* currentBody = factory.find({X}, &_start);
                if(currentBody->isTrue()){
                    propagatedLiterals.push_back(1);
                    return;
                }else if(currentBody->isUndef()){
                    propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* undefHeads = &usup_3_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                int X = currentHead->at(0);
                const Tuple* currentBody = factory.find({X}, &_start);
                if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(currentBody!=NULL && currentBody->isTrue())
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id2_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id2_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id2_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 1+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 1+1 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
    std::vector<int> propagated;
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        propagated.push_back(startVar);
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
        {
            if(starter.getPredicateName() == &_r && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_sup_0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_sup_0 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_sup_0 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y},&_r);
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
                            if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
        if(starter.getPredicateName() == &_pathE){
            int X = starter.at(0);
            int Y = starter.at(1);
            Tuple* head = factory.find({X,Y}, &_sup_0);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar > 0){
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
                if(head != NULL && head->isTrue()){
                    int it = head->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[-it]=shared_reason;
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(head != NULL && head->isUndef()){
                        int it = head->getId();
                        shared_reason.get()->insert(startVar);
                        auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }else if(starter.getPredicateName() == &_sup_0){
            int X = starter.at(0);
            int Y = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            Tuple* currentBody = factory.find({X,Y}, &_pathE);
            if(startVar > 0){
                if(currentBody->isFalse()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[it]=shared_reason;
                    handleConflict(it, propagatedLiterals);
                    return;
                }else if(currentBody->isUndef()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    auto itReason = reasonForLiteral.emplace(it,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                if(currentBody->isTrue()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[-it]=shared_reason;
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else if(currentBody->isUndef()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }
        {
            if(starter.getPredicateName() == &_r && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_sup_1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_sup_1 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_sup_1 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y},&_r);
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
                            if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
        if(starter.getPredicateName() == &_aux0){
            int X = starter.at(0);
            int Y = starter.at(1);
            int Z = starter.at(2);
            Tuple* head = factory.find({X,Y}, &_sup_1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar > 0){
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
                const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({X, Y});
                const std::vector<int>* tuplesU = &uaux0_0_1_.getValuesVec({X, Y});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux0_0_1_.getValuesVec({X, Y});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux0_0_1_.getValuesVec({X, Y});
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
                        const std::vector<int>* tuplesF = &faux0_0_1_.getValuesVec({X, Y});
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
        }else if(starter.getPredicateName() == &_sup_1){
            int X = starter.at(0);
            int Y = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux0_0_1_.getValuesVec({X,Y});
            const std::vector<int>* tuplesU = &uaux0_0_1_.getValuesVec({X,Y});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        const std::vector<int>* tuplesF = &faux0_0_1_.getValuesVec({X,Y});
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
                        const std::vector<int>* tuplesF = &faux0_0_1_.getValuesVec({X,Y});
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
            if(starter.getPredicateName() == &_r && startVar < 0){
                int X = starter[0];
                int Z = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux0_0_2_.getValuesVec({X,Z});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_0_2_.getValuesVec({X,Z});
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
                        if(tupleU->at(0) == X && tupleU->at(2) == Z)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(1);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                int Y = starter[1];
                int Z = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Z},&_r);
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
                            if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_pathE && startVar < 0){
                int Z = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux0_1_2_.getValuesVec({Y,Z});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_1_2_.getValuesVec({Y,Z});
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
                        if(tupleU->at(1) == Y && tupleU->at(2) == Z)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(0);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                int Y = starter[1];
                int Z = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({Z,Y},&_pathE);
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
                            if(tupleU->getPredicateName() != &_pathE || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                int Y = starter[1];
                int Z = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Z},&_r);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_r || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({Z,Y},&_pathE);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_pathE || tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_pathE && startVar > 0){
                int Z = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pr_1_.getValuesVec({Z});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ur_1_.getValuesVec({Z});
                else if(tupleU->getPredicateName() == &_r && !tupleUNegated)
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
                        if(tupleU->at(1) == Z)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(0);
                        Tuple negativeTuple({X,Y,Z},&_aux0);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_r && startVar > 0){
                int X = starter[0];
                int Z = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &ppathE_0_.getValuesVec({Z});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upathE_0_.getValuesVec({Z});
                else if(tupleU->getPredicateName() == &_pathE && !tupleUNegated)
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
                        if(tupleU->at(0) == Z)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(1);
                        Tuple negativeTuple({X,Y,Z},&_aux0);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            int X = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<int>* tuples = &ppathE_1_.getValuesVec(sharedVar);
            const std::vector<int>* tuplesU = &upathE_1_.getValuesVec(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                if(tuples->size()>=0){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 0 -1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    shared_reason.get()->insert(startVar);
                    for(unsigned i =0; i<tuplesU->size(); i++){
                        int itProp = tuplesU->at(i);
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 0){
                    const std::vector<int>* tuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() + tuplesU->size() == 0){
                    if(!tuplesU->empty()){
                        const std::vector<int>* tuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    for(unsigned index=0;index<tuplesU->size();index++){
                        int itProp = tuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_pathE){
            const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 0){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-itProp]=shared_reason;
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 0){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[itProp]=shared_reason;
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() == 0 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 0){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
            int X = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<int>* tuples = &ppathE_1_.getValuesVec(sharedVar);
            const std::vector<int>* tuplesU = &upathE_1_.getValuesVec(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                if(tuples->size()>=0+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 0+1 -1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    shared_reason.get()->insert(startVar);
                    for(unsigned i =0; i<tuplesU->size(); i++){
                        int itProp = tuplesU->at(i);
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 0+1){
                    const std::vector<int>* tuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() + tuplesU->size() == 0+1){
                    if(!tuplesU->empty()){
                        const std::vector<int>* tuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    for(unsigned index=0;index<tuplesU->size();index++){
                        int itProp = tuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_pathE){
            const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 0+1){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-itProp]=shared_reason;
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 0+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[itProp]=shared_reason;
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() == 0+1 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 0+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 0+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
            if(starter.getPredicateName() == &_node && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_start);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_node);
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
                            if(tupleU->getPredicateName() != &_node || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_start);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_aggr_id0);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_start);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_aggr_id1);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({X},&_aggr_id0);
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
                        Tuple negativeTuple({X},&_aggr_id1);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({X},&_aggr_id0);
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
                        Tuple negativeTuple({X},&_start);
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
                                    if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple3))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X},&_aggr_id1);
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
                        Tuple negativeTuple({X},&_start);
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
                                    if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple3))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_node && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_aggr_id0);
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
                    Tuple negativeTuple({X},&_aggr_id1);
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
                        Tuple negativeTuple({X},&_start);
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
                                    if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple3))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar > 0){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        if(X != Y){
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pstart_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ustart_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_start && !tupleUNegated)
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
                        int Y = tuple1->at(0);
                        if(X != Y){
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_reached && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_sup_2);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_sup_2 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_sup_2 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_reached);
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
                            if(tupleU->getPredicateName() != &_reached || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
        if(starter.getPredicateName() == &_aux2){
            int X = starter.at(0);
            int Y = starter.at(1);
            Tuple* head = factory.find({X}, &_sup_2);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar > 0){
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
                const std::vector<int>* tuples = &paux2_0_.getValuesVec({X});
                const std::vector<int>* tuplesU = &uaux2_0_.getValuesVec({X});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux2_0_.getValuesVec({X});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux2_0_.getValuesVec({X});
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
                        const std::vector<int>* tuplesF = &faux2_0_.getValuesVec({X});
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
        }else if(starter.getPredicateName() == &_sup_2){
            int X = starter.at(0);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux2_0_.getValuesVec({X});
            const std::vector<int>* tuplesU = &uaux2_0_.getValuesVec({X});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        const std::vector<int>* tuplesF = &faux2_0_.getValuesVec({X});
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
                        const std::vector<int>* tuplesF = &faux2_0_.getValuesVec({X});
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
            if(starter.getPredicateName() == &_start && startVar < 0){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux2_1_.getValuesVec({Y});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux2_1_.getValuesVec({Y});
                else if(tupleU->getPredicateName() == &_aux2 && !tupleUNegated)
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
                        if(tupleU->at(1) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(0);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_aux2 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({Y},&_start);
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
                            if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_r && startVar < 0){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_aux2);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux2 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_aux2 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({Y,X},&_r);
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
                            if(tupleU->getPredicateName() != &_r || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_aux2 && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({Y},&_start);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({Y,X},&_r);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_r || tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_r && startVar > 0){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({Y},&_start);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y},&_aux2);
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
                                if(tupleU->getPredicateName() != &_aux2 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_start && startVar > 0){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pr_0_.getValuesVec({Y});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ur_0_.getValuesVec({Y});
                else if(tupleU->getPredicateName() == &_r && !tupleUNegated)
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
                        if(tupleU->at(0) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(1);
                        Tuple negativeTuple({X,Y},&_aux2);
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
                                    if(tupleU->getPredicateName() != &_aux2 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
        {
            if(starter.getPredicateName() == &_reached && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_sup_3);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_sup_3 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_sup_3 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_reached);
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
                            if(tupleU->getPredicateName() != &_reached || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
        if(starter.getPredicateName() == &_start){
            int X = starter.at(0);
            Tuple* head = factory.find({X}, &_sup_3);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar > 0){
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
                if(head != NULL && head->isTrue()){
                    int it = head->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[-it]=shared_reason;
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(head != NULL && head->isUndef()){
                        int it = head->getId();
                        shared_reason.get()->insert(startVar);
                        auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }else if(starter.getPredicateName() == &_sup_3){
            int X = starter.at(0);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            Tuple* currentBody = factory.find({X}, &_start);
            if(startVar > 0){
                if(currentBody->isFalse()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[it]=shared_reason;
                    handleConflict(it, propagatedLiterals);
                    return;
                }else if(currentBody->isUndef()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    auto itReason = reasonForLiteral.emplace(it,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }else{
                if(currentBody->isTrue()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    reasonForLiteral[-it]=shared_reason;
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else if(currentBody->isUndef()){
                    int it = currentBody->getId();
                    shared_reason.get()->insert(startVar);
                    auto itReason = reasonForLiteral.emplace(-it,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }
        {
            if(starter.getPredicateName() == &_reached && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_node && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_reached);
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
                            if(tupleU->getPredicateName() != &_reached || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_node && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_body0);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_body0 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_node);
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
                            if(tupleU->getPredicateName() != &_node || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_start && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_body0);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_body0 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_start);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_start || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_body0 && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X},&_start);
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
                                if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_start && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X},&_body0);
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
                                if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_node && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X},&_start);
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
                            if(tupleU->getPredicateName() != &_start || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X},&_body0);
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
                                if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
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
                            return;
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        if(starter.getPredicateName() == &_aggr_id2){
            int X = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<int>* tuples = &ppathE_1_.getValuesVec(sharedVar);
            const std::vector<int>* tuplesU = &upathE_1_.getValuesVec(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                if(tuples->size()>=1+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 1+1 -1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    shared_reason.get()->insert(startVar);
                    for(unsigned i =0; i<tuplesU->size(); i++){
                        int itProp = tuplesU->at(i);
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 1+1){
                    const std::vector<int>* tuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() + tuplesU->size() == 1+1){
                    if(!tuplesU->empty()){
                        const std::vector<int>* tuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    for(unsigned index=0;index<tuplesU->size();index++){
                        int itProp = tuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_pathE){
            const std::vector<int>* tuples = &paggr_id2_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id2_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id2_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-itProp]=shared_reason;
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 1+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[itProp]=shared_reason;
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() == 1+1 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_1_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
            if(starter.getPredicateName() == &_aggr_id2 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_body0);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_body0 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_aggr_id2);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aggr_id2 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
        if(starter.getPredicateName() == &_aggr_id3){
            int X = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<int>* tuples = &ppathE_0_.getValuesVec(sharedVar);
            const std::vector<int>* tuplesU = &upathE_0_.getValuesVec(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                if(tuples->size()>=1+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 1+1 -1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        shared_reason.get()->insert(it);
                    }
                    shared_reason.get()->insert(startVar);
                    for(unsigned i =0; i<tuplesU->size(); i++){
                        int itProp = tuplesU->at(i);
                        auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 1+1){
                    const std::vector<int>* tuplesF = &fpathE_0_.getValuesVec(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() + tuplesU->size() == 1+1){
                    if(!tuplesU->empty()){
                        const std::vector<int>* tuplesF = &fpathE_0_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    for(unsigned index=0;index<tuplesU->size();index++){
                        int itProp = tuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_pathE){
            const std::vector<int>* tuples = &paggr_id3_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id3_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id3_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_0_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_0_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_0_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-itProp]=shared_reason;
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 1+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &fpathE_0_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_0_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_0_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[itProp]=shared_reason;
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() == 1+1 -1){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        int itProp = joinTuplesU->at(index);
                        if(shared_reason.get()->empty()){
                            for(unsigned i =0; i< joinTuples->size(); i++){
                                int it = joinTuples->at(i);
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
                int X = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &ppathE_0_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &upathE_0_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &fpathE_0_.getValuesVec(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
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
            if(starter.getPredicateName() == &_aggr_id3 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_node);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_node || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_node && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_aggr_id3);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aggr_id3 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
            if(starter.getPredicateName() == &_sup_3 && startVar < 0){
                int X0 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0},&_reached);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_reached || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0},&_sup_2);
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
                                if(tupleU->getPredicateName() != &_sup_2 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_sup_2 && startVar < 0){
                int X0 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0},&_reached);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_reached || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0},&_sup_3);
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
                                if(tupleU->getPredicateName() != &_sup_3 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_reached && startVar > 0){
                int X0 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X0},&_sup_2);
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
                            if(tupleU->getPredicateName() != &_sup_2 || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0},&_sup_3);
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
                                if(tupleU->getPredicateName() != &_sup_3 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
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
                            return;
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            if(starter.getPredicateName() == &_sup_1 && startVar < 0){
                int X0 = starter[0];
                int X1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0,X1},&_r);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_r || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0,X1},&_sup_0);
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
                                if(tupleU->getPredicateName() != &_sup_0 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_sup_0 && startVar < 0){
                int X0 = starter[0];
                int X1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0,X1},&_r);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_r || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0,X1},&_sup_1);
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
                                if(tupleU->getPredicateName() != &_sup_1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_r && startVar > 0){
                int X0 = starter[0];
                int X1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X0,X1},&_sup_0);
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
                            if(tupleU->getPredicateName() != &_sup_0 || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0,X1},&_sup_1);
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
                                if(tupleU->getPredicateName() != &_sup_1 || !tupleUNegated || !(*tupleU == *tuple2))
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
                                shared_reason.get()->insert(it*-1);
                            }
                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_id3 && tupleU->getPredicateName() != &_r && tupleU->getPredicateName() != &_start && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_reached && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3 && tupleU->getPredicateName() != &_aggr_id2)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
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
                            return;
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
