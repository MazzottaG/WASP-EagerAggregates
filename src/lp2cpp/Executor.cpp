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
const std::string _aux0 = "aux0";
const std::string _aux1 = "aux1";
const std::string _aux2 = "aux2";
const std::string _aux3 = "aux3";
const std::string _aux4 = "aux4";
const std::string _aux5 = "aux5";
const std::string _chain = "chain";
const std::string _node = "node";
const std::string _ord = "ord";
const std::string _ord_init = "ord_init";
const std::string _ord_last = "ord_last";
const std::string _ord_next = "ord_next";
const std::string _order = "order";
const std::string _order1 = "order1";
const std::string _parent = "parent";
const std::string _pot_parent = "pot_parent";
const std::string _sup_0 = "sup_0";
const std::string _sup_1 = "sup_1";
const std::string _sup_2 = "sup_2";
const std::string _sup_3 = "sup_3";
const std::string _sup_4 = "sup_4";
const std::string _sup_5 = "sup_5";
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
AuxMap<0> pord_next_({});
AuxMap<0> uord_next_({});
AuxMap<0> ford_next_({});
AuxMap<0> pord_init_({});
AuxMap<0> uord_init_({});
AuxMap<0> ford_init_({});
AuxMap<0> pnode_({});
AuxMap<0> unode_({});
AuxMap<0> fnode_({});
AuxMap<0> ppot_parent_({});
AuxMap<0> upot_parent_({});
AuxMap<0> fpot_parent_({});
AuxMap<0> pord_last_({});
AuxMap<0> uord_last_({});
AuxMap<0> ford_last_({});
AuxMap<0> psup_0_({});
AuxMap<0> usup_0_({});
AuxMap<0> fsup_0_({});
AuxMap<0> porder_({});
AuxMap<0> uorder_({});
AuxMap<0> forder_({});
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<0> pparent_({});
AuxMap<0> uparent_({});
AuxMap<0> fparent_({});
AuxMap<0> psup_1_({});
AuxMap<0> usup_1_({});
AuxMap<0> fsup_1_({});
AuxMap<0> paux1_({});
AuxMap<0> uaux1_({});
AuxMap<0> faux1_({});
AuxMap<0> porder1_({});
AuxMap<0> uorder1_({});
AuxMap<0> forder1_({});
AuxMap<32> paux1_1_({1});
AuxMap<32> uaux1_1_({1});
AuxMap<32> faux1_1_({1});
AuxMap<32> ppot_parent_1_({1});
AuxMap<32> upot_parent_1_({1});
AuxMap<32> fpot_parent_1_({1});
AuxMap<0> psup_2_({});
AuxMap<0> usup_2_({});
AuxMap<0> fsup_2_({});
AuxMap<32> paux2_0_({0});
AuxMap<32> uaux2_0_({0});
AuxMap<32> faux2_0_({0});
AuxMap<0> paux2_({});
AuxMap<0> uaux2_({});
AuxMap<0> faux2_({});
AuxMap<0> pchain_({});
AuxMap<0> uchain_({});
AuxMap<0> fchain_({});
AuxMap<0> psup_3_({});
AuxMap<0> usup_3_({});
AuxMap<0> fsup_3_({});
AuxMap<0> paux3_({});
AuxMap<0> uaux3_({});
AuxMap<0> faux3_({});
AuxMap<0> pord_({});
AuxMap<0> uord_({});
AuxMap<0> ford_({});
AuxMap<0> psup_4_({});
AuxMap<0> usup_4_({});
AuxMap<0> fsup_4_({});
AuxMap<0> paux4_({});
AuxMap<0> uaux4_({});
AuxMap<0> faux4_({});
AuxMap<0> psup_5_({});
AuxMap<0> usup_5_({});
AuxMap<0> fsup_5_({});
AuxMap<64> paux5_0_1_({0,1});
AuxMap<64> uaux5_0_1_({0,1});
AuxMap<64> faux5_0_1_({0,1});
AuxMap<0> paux5_({});
AuxMap<0> uaux5_({});
AuxMap<0> faux5_({});
AuxMap<64> paux5_0_2_({0,2});
AuxMap<64> uaux5_0_2_({0,2});
AuxMap<64> faux5_0_2_({0,2});
AuxMap<64> pord_next_0_1_({0,1});
AuxMap<64> uord_next_0_1_({0,1});
AuxMap<64> ford_next_0_1_({0,1});
AuxMap<64> pord_next_0_2_({0,2});
AuxMap<64> uord_next_0_2_({0,2});
AuxMap<64> ford_next_0_2_({0,2});
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
    if(insertResult.first->getPredicateName() == &_sup_4){
        fsup_4_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux3){
        faux3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux5){
        faux5_.insert2Vec(*insertResult.first);
        faux5_0_1_.insert2Vec(*insertResult.first);
        faux5_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_chain){
        fchain_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux2){
        faux2_.insert2Vec(*insertResult.first);
        faux2_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_node){
        fnode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord){
        ford_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_order){
        forder_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pot_parent){
        fpot_parent_.insert2Vec(*insertResult.first);
        fpot_parent_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_0){
        fsup_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_init){
        ford_init_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        faux1_.insert2Vec(*insertResult.first);
        faux1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_parent){
        fparent_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux4){
        faux4_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_order1){
        forder1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_next){
        ford_next_.insert2Vec(*insertResult.first);
        ford_next_0_1_.insert2Vec(*insertResult.first);
        ford_next_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_last){
        ford_last_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_1){
        fsup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_5){
        fsup_5_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_3){
        fsup_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_2){
        fsup_2_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_sup_4){
        psup_4_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux3){
        paux3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux5){
        paux5_.insert2Vec(*insertResult.first);
        paux5_0_1_.insert2Vec(*insertResult.first);
        paux5_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_chain){
        pchain_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux2){
        paux2_.insert2Vec(*insertResult.first);
        paux2_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_node){
        pnode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord){
        pord_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_order){
        porder_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pot_parent){
        ppot_parent_.insert2Vec(*insertResult.first);
        ppot_parent_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_0){
        psup_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_init){
        pord_init_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        paux1_.insert2Vec(*insertResult.first);
        paux1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_parent){
        pparent_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux4){
        paux4_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_order1){
        porder1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_next){
        pord_next_.insert2Vec(*insertResult.first);
        pord_next_0_1_.insert2Vec(*insertResult.first);
        pord_next_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_last){
        pord_last_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_1){
        psup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_5){
        psup_5_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_3){
        psup_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_2){
        psup_2_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_sup_4){
        usup_4_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux3){
        uaux3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux5){
        uaux5_.insert2Vec(*insertResult.first);
        uaux5_0_1_.insert2Vec(*insertResult.first);
        uaux5_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_chain){
        uchain_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux2){
        uaux2_.insert2Vec(*insertResult.first);
        uaux2_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_node){
        unode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord){
        uord_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_order){
        uorder_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_pot_parent){
        upot_parent_.insert2Vec(*insertResult.first);
        upot_parent_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_0){
        usup_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_init){
        uord_init_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        uaux1_.insert2Vec(*insertResult.first);
        uaux1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_parent){
        uparent_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux4){
        uaux4_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_order1){
        uorder1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_next){
        uord_next_.insert2Vec(*insertResult.first);
        uord_next_0_1_.insert2Vec(*insertResult.first);
        uord_next_0_2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_ord_last){
        uord_last_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_1){
        usup_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_5){
        usup_5_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_3){
        usup_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sup_2){
        usup_2_.insert2Vec(*insertResult.first);
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
std::unordered_map<int,std::unordered_set<int>> supportedAux0;
std::unordered_map<int,std::unordered_set<int>> supportedLiterals0;
std::unordered_map<int,int> sourcePointers0;
std::unordered_set<int> unfoundedSetForComponent0;
void propFoundessForComponent0(std::unordered_set<int>& founded,int foundedLiteral){
    std::vector<int> foundedStack({foundedLiteral});
    while(!foundedStack.empty()){
        Tuple* starter = factory.getTupleFromInternalID(foundedStack.back());
        foundedStack.pop_back();
        if(starter->getPredicateName() == &_sup_2){
            int X=starter->at(0);
            Tuple* head = factory.find({X},&_order1);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_aux2){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* head = factory.find({X},&_sup_2);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_ord_last){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* tuple1 = factory.find({X,Y},&_chain);
            if(tuple1!=NULL && !tuple1->isFalse()){
                if(unfoundedSetForComponent0.count(tuple1->getId())==0 || founded.count(tuple1->getId())!=0){
                    Tuple* head = factory.find({X,Y},&_aux2);
                    if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                        foundedStack.push_back(head->getId());
                        founded.insert(head->getId());
                        if(tuple1!=NULL){
                            supportedAux0[tuple1->getId()].insert(head->getId());
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_chain){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* tuple1 = factory.find({X,Y},&_ord_last);
            if(tuple1!=NULL && !tuple1->isFalse()){
                Tuple* head = factory.find({X,Y},&_aux2);
                if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                    foundedStack.push_back(head->getId());
                    founded.insert(head->getId());
                    supportedAux0[starter->getId()].insert(head->getId());
                }
            }
        }
        if(starter->getPredicateName() == &_sup_4){
            int X=starter->at(0);
            int Y1=starter->at(1);
            Tuple* head = factory.find({X,Y1},&_chain);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_aux4){
            int X=starter->at(0);
            int Y1=starter->at(1);
            Tuple* head = factory.find({X,Y1},&_sup_4);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_ord_init){
            int X=starter->at(0);
            int Y1=starter->at(1);
            Tuple* tuple1 = factory.find({X,Y1},&_order);
            if(tuple1!=NULL && !tuple1->isFalse()){
                if(unfoundedSetForComponent0.count(tuple1->getId())==0 || founded.count(tuple1->getId())!=0){
                    Tuple* head = factory.find({X,Y1},&_aux4);
                    if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                        foundedStack.push_back(head->getId());
                        founded.insert(head->getId());
                        if(tuple1!=NULL){
                            supportedAux0[tuple1->getId()].insert(head->getId());
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_order){
            int X=starter->at(0);
            int Y1=starter->at(1);
            Tuple* tuple1 = factory.find({X,Y1},&_ord_init);
            if(tuple1!=NULL && !tuple1->isFalse()){
                Tuple* head = factory.find({X,Y1},&_aux4);
                if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                    foundedStack.push_back(head->getId());
                    founded.insert(head->getId());
                    supportedAux0[starter->getId()].insert(head->getId());
                }
            }
        }
        if(starter->getPredicateName() == &_sup_5){
            int X=starter->at(0);
            int Y2=starter->at(1);
            Tuple* head = factory.find({X,Y2},&_chain);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_aux5){
            int X=starter->at(0);
            int Y2=starter->at(1);
            int Y1=starter->at(2);
            Tuple* head = factory.find({X,Y2},&_sup_5);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_ord_next){
            int X=starter->at(0);
            int Y1=starter->at(1);
            int Y2=starter->at(2);
            Tuple* tuple1 = factory.find({X,Y1},&_chain);
            if(tuple1!=NULL && !tuple1->isFalse()){
                if(unfoundedSetForComponent0.count(tuple1->getId())==0 || founded.count(tuple1->getId())!=0){
                    Tuple* tuple2 = factory.find({X,Y2},&_order);
                    if(tuple2!=NULL && !tuple2->isFalse()){
                        if(unfoundedSetForComponent0.count(tuple2->getId())==0 || founded.count(tuple2->getId())!=0){
                            Tuple* head = factory.find({X,Y2,Y1},&_aux5);
                            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                                foundedStack.push_back(head->getId());
                                founded.insert(head->getId());
                                if(tuple1!=NULL){
                                    supportedAux0[tuple1->getId()].insert(head->getId());
                                }
                                if(tuple2!=NULL){
                                    supportedAux0[tuple2->getId()].insert(head->getId());
                                }
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_chain){
            int X=starter->at(0);
            int Y1=starter->at(1);
            const std::vector<int>* tuples = &pord_next_0_1_.getValuesVec({X,Y1});
            const std::vector<int>* tuplesU = &uord_next_0_1_.getValuesVec({X,Y1});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(X == tuple1->at(0)){
                    if(Y1 == tuple1->at(1)){
                        int Y2=tuple1->at(2);
                        Tuple* tuple2 = factory.find({X,Y2},&_order);
                        if(tuple2!=NULL && !tuple2->isFalse()){
                            if(unfoundedSetForComponent0.count(tuple2->getId())==0 || founded.count(tuple2->getId())!=0){
                                Tuple* head = factory.find({X,Y2,Y1},&_aux5);
                                if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                                    foundedStack.push_back(head->getId());
                                    founded.insert(head->getId());
                                    if(tuple2!=NULL){
                                        supportedAux0[tuple2->getId()].insert(head->getId());
                                    }
                                    supportedAux0[starter->getId()].insert(head->getId());
                                }
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_order){
            int X=starter->at(0);
            int Y2=starter->at(1);
            const std::vector<int>* tuples = &pord_next_0_2_.getValuesVec({X,Y2});
            const std::vector<int>* tuplesU = &uord_next_0_2_.getValuesVec({X,Y2});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(X == tuple1->at(0)){
                    int Y1=tuple1->at(1);
                    if(Y2 == tuple1->at(2)){
                        Tuple* tuple2 = factory.find({X,Y1},&_chain);
                        if(tuple2!=NULL && !tuple2->isFalse()){
                            if(unfoundedSetForComponent0.count(tuple2->getId())==0 || founded.count(tuple2->getId())!=0){
                                Tuple* head = factory.find({X,Y2,Y1},&_aux5);
                                if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                                    foundedStack.push_back(head->getId());
                                    founded.insert(head->getId());
                                    if(tuple2!=NULL){
                                        supportedAux0[tuple2->getId()].insert(head->getId());
                                    }
                                    supportedAux0[starter->getId()].insert(head->getId());
                                }
                            }
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_sup_1){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* head = factory.find({X,Y},&_order);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_aux1){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* head = factory.find({X,Y},&_sup_1);
            if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                auto oldSP = sourcePointers0.find(head->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(head->getId());
                supportedLiterals0[starter->getId()].insert(head->getId());
                sourcePointers0[head->getId()] = starter->getId();
                foundedStack.push_back(head->getId());
                founded.insert(head->getId());
            }
        }
        if(starter->getPredicateName() == &_pot_parent){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* tuple1 = factory.find({Y},&_order1);
            if(tuple1!=NULL && !tuple1->isFalse()){
                if(unfoundedSetForComponent0.count(tuple1->getId())==0 || founded.count(tuple1->getId())!=0){
                    Tuple* head = factory.find({X,Y},&_aux1);
                    if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                        foundedStack.push_back(head->getId());
                        founded.insert(head->getId());
                        if(tuple1!=NULL){
                            supportedAux0[tuple1->getId()].insert(head->getId());
                        }
                    }
                }
            }
        }
        if(starter->getPredicateName() == &_order1){
            int Y=starter->at(0);
            const std::vector<int>* tuples = &ppot_parent_1_.getValuesVec({Y});
            const std::vector<int>* tuplesU = &upot_parent_1_.getValuesVec({Y});
            for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                else tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X=tuple1->at(0);
                if(Y == tuple1->at(1)){
                    Tuple* head = factory.find({X,Y},&_aux1);
                    if(head!=NULL && founded.count(head->getId())==0 && unfoundedSetForComponent0.count(head->getId())!=0){
                        foundedStack.push_back(head->getId());
                        founded.insert(head->getId());
                        supportedAux0[starter->getId()].insert(head->getId());
                    }
                }
            }
        }
    }//close while 
}//close function
void unfoundedPropagatorForComponent0(std::vector<int>& literalToPropagate,Executor* executor){
    std::unordered_set<int> founded;
    for(int id : unfoundedSetForComponent0){
        Tuple* starter = factory.getTupleFromInternalID(id);
        if(founded.count(id)!=0) continue;
        bool spFound=false;
        if(!spFound && starter->getPredicateName() == &_order1 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            Tuple* body = factory.find({X},&_sup_2);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers0.find(starter->getId());
                    if(oldSP!=sourcePointers0.end())
                        supportedLiterals0[oldSP->second].erase(starter->getId());
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent0(founded,starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_sup_2 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            const std::vector<int>* tuples = &paux2_0_.getValuesVec({X});
            const std::vector<int>* tuplesU = &uaux2_0_.getValuesVec({X});
            for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){
                Tuple* body = NULL;
                if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));
                else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(body!=NULL){
                    if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                        auto oldSP = sourcePointers0.find(starter->getId());
                        if(oldSP!=sourcePointers0.end())
                            supportedLiterals0[oldSP->second].erase(starter->getId());
                        sourcePointers0[starter->getId()]=body->getId();
                        supportedLiterals0[body->getId()].insert(starter->getId());
                        founded.insert(starter->getId());
                        propFoundessForComponent0(founded,starter->getId());
                        spFound=true;
                    }
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_order1 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            Tuple* body = factory.find({X},&_sup_3);
            if(body!=NULL && !body->isFalse()){
                auto oldSP = sourcePointers0.find(starter->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(starter->getId());
                sourcePointers0[starter->getId()]=body->getId();
                supportedLiterals0[body->getId()].insert(starter->getId());
                founded.insert(starter->getId());
                propFoundessForComponent0(founded,starter->getId());
                spFound=true;
            }
        }
        if(!spFound && starter->getPredicateName() == &_chain && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y1=starter->at(1);
            Tuple* body = factory.find({X,Y1},&_sup_4);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers0.find(starter->getId());
                    if(oldSP!=sourcePointers0.end())
                        supportedLiterals0[oldSP->second].erase(starter->getId());
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent0(founded,starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_sup_4 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y1=starter->at(1);
            Tuple* body = factory.find({X,Y1},&_aux4);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers0.find(starter->getId());
                    if(oldSP!=sourcePointers0.end())
                        supportedLiterals0[oldSP->second].erase(starter->getId());
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent0(founded,starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_chain && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y2=starter->at(1);
            Tuple* body = factory.find({X,Y2},&_sup_5);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers0.find(starter->getId());
                    if(oldSP!=sourcePointers0.end())
                        supportedLiterals0[oldSP->second].erase(starter->getId());
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent0(founded,starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_sup_5 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y2=starter->at(1);
            const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X,Y2});
            const std::vector<int>* tuplesU = &uaux5_0_1_.getValuesVec({X,Y2});
            for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){
                Tuple* body = NULL;
                if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));
                else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                if(body!=NULL){
                    if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                        auto oldSP = sourcePointers0.find(starter->getId());
                        if(oldSP!=sourcePointers0.end())
                            supportedLiterals0[oldSP->second].erase(starter->getId());
                        sourcePointers0[starter->getId()]=body->getId();
                        supportedLiterals0[body->getId()].insert(starter->getId());
                        founded.insert(starter->getId());
                        propFoundessForComponent0(founded,starter->getId());
                        spFound=true;
                    }
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_order && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* body = factory.find({X,Y},&_sup_0);
            if(body!=NULL && !body->isFalse()){
                auto oldSP = sourcePointers0.find(starter->getId());
                if(oldSP!=sourcePointers0.end())
                    supportedLiterals0[oldSP->second].erase(starter->getId());
                sourcePointers0[starter->getId()]=body->getId();
                supportedLiterals0[body->getId()].insert(starter->getId());
                founded.insert(starter->getId());
                propFoundessForComponent0(founded,starter->getId());
                spFound=true;
            }
        }
        if(!spFound && starter->getPredicateName() == &_order && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* body = factory.find({X,Y},&_sup_1);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers0.find(starter->getId());
                    if(oldSP!=sourcePointers0.end())
                        supportedLiterals0[oldSP->second].erase(starter->getId());
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent0(founded,starter->getId());
                    spFound=true;
                }
            }
        }
        if(!spFound && starter->getPredicateName() == &_sup_1 && founded.count(starter->getId())==0){
            int X=starter->at(0);
            int Y=starter->at(1);
            Tuple* body = factory.find({X,Y},&_aux1);
            if(body!=NULL && !body->isFalse()){
                if(unfoundedSetForComponent0.count(body->getId())==0 || founded.count(body->getId())!=0){
                    auto oldSP = sourcePointers0.find(starter->getId());
                    if(oldSP!=sourcePointers0.end())
                        supportedLiterals0[oldSP->second].erase(starter->getId());
                    sourcePointers0[starter->getId()]=body->getId();
                    supportedLiterals0[body->getId()].insert(starter->getId());
                    founded.insert(starter->getId());
                    propFoundessForComponent0(founded,starter->getId());
                    spFound=true;
                }
            }
        }
    } //close unfounded for
    for(int lit : founded) unfoundedSetForComponent0.erase(lit);
    if(!unfoundedSetForComponent0.empty()){
        int conflictDetected=0;
        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
        std::vector<int> propLiterals({currentDecisionLevel});
        for(int lit : unfoundedSetForComponent0){
            Tuple* starter = factory.getTupleFromInternalID(lit);
            if(starter == NULL) continue;
            if(currentDecisionLevel > 0){
                if(starter->getPredicateName() == &_order1){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    reasonForLiteral[-lit]=shared_reason;
                    propLiterals.push_back(-lit);
                    int X=starter->at(0);
                    Tuple* tuple = factory.find({X},&_sup_2);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_sup_2){
                    int X=starter->at(0);
                    const std::vector<int>* tuplesF = &faux2_0_.getValuesVec({X});
                    for(unsigned i=0; i<tuplesF->size();i++){
                        Tuple* tuple = factory.getTupleFromInternalID(tuplesF->at(i));
                        if(tuple!=NULL){
                            shared_reason.get()->insert(-tuple->getId());
                        }
                    }
                }
                if(starter->getPredicateName() == &_order1){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    reasonForLiteral[-lit]=shared_reason;
                    propLiterals.push_back(-lit);
                    int X=starter->at(0);
                    Tuple* tuple = factory.find({X},&_sup_3);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_chain){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    reasonForLiteral[-lit]=shared_reason;
                    propLiterals.push_back(-lit);
                    int X=starter->at(0);
                    int Y1=starter->at(1);
                    Tuple* tuple = factory.find({X,Y1},&_sup_4);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_sup_4){
                    int X=starter->at(0);
                    int Y1=starter->at(1);
                    Tuple* tuple = factory.find({X,Y1},&_aux4);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_chain){
                    if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;
                    reasonForLiteral[-lit]=shared_reason;
                    propLiterals.push_back(-lit);
                    int X=starter->at(0);
                    int Y2=starter->at(1);
                    Tuple* tuple = factory.find({X,Y2},&_sup_5);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
                    }
                }
                if(starter->getPredicateName() == &_sup_5){
                    int X=starter->at(0);
                    int Y2=starter->at(1);
                    const std::vector<int>* tuplesF = &faux5_0_1_.getValuesVec({X,Y2});
                    for(unsigned i=0; i<tuplesF->size();i++){
                        Tuple* tuple = factory.getTupleFromInternalID(tuplesF->at(i));
                        if(tuple!=NULL){
                            shared_reason.get()->insert(-tuple->getId());
                        }
                    }
                }
                if(starter->getPredicateName() == &_order){
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
                if(starter->getPredicateName() == &_order){
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
                    Tuple* tuple = factory.find({X,Y},&_aux1);
                    if(tuple!=NULL && tuple->isFalse()){
                        shared_reason.get()->insert(-tuple->getId());
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
        unfoundedSetForComponent0.clear();
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
                auto supported = supportedLiterals0.find(tuple->getId());
                if(supported!=supportedLiterals0.end()){
                    for(int lit : supported->second){
                        Tuple* removingLit = factory.getTupleFromInternalID(lit);
                        auto unfoundeRemovingLit = predsToUnfoundedSet.find(removingLit->getPredicateName());
                        if(!removingLit->isFalse() && unfoundeRemovingLit!=predsToUnfoundedSet.end() && unfoundeRemovingLit->second->count(removingLit->getId())==0)
                            falseLits.push_back(-removingLit->getId());
                    }//close for
                }//close if
                auto supAux = supportedAux0.find(tuple->getId());
                if(supAux!=supportedAux0.end()){
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
    unfoundedPropagatorForComponent0(literalsToPropagate,executor);
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    //---------------------------------Recursive Component---------------------------------
    {
        std::vector<int> generationStack;
        {
            const std::vector<int>* tuples = &ppot_parent_.getValuesVec({});
            const std::vector<int>* tuplesU = &upot_parent_.getValuesVec({});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple0 = NULL;
                if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
                else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X = tuple0->at(0);
                int Y = tuple0->at(1);
                Tuple* tuple1 = factory.find({X,Y},&_parent);
                if(tuple1==NULL || !tuple1->isTrue()){
                    Tuple* saving3 = factory.addNewInternalTuple({X,Y},&_aux0);
                    const auto& insertResult = saving3->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving3->getId());
                        insertUndef(insertResult);
                        Tuple* saving1 = factory.addNewInternalTuple({X,Y},&_sup_0);
                        const auto& insertResult = saving1->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving1->getId());
                            insertUndef(insertResult);
                            Tuple* saving0 = factory.addNewInternalTuple({X,Y},&_order);
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
        {
            const std::vector<int>* tuples = &pnode_.getValuesVec({});
            const std::vector<int>* tuplesU = &unode_.getValuesVec({});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple0 = NULL;
                if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
                else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X = tuple0->at(0);
                Tuple* tuple1 = factory.find({X},&_ord);
                if(tuple1==NULL || !tuple1->isTrue()){
                    Tuple* saving3 = factory.addNewInternalTuple({X},&_aux3);
                    const auto& insertResult = saving3->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving3->getId());
                        insertUndef(insertResult);
                        Tuple* saving1 = factory.addNewInternalTuple({X},&_sup_3);
                        const auto& insertResult = saving1->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving1->getId());
                            insertUndef(insertResult);
                            Tuple* saving0 = factory.addNewInternalTuple({X},&_order1);
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
            if(starter->getPredicateName() == &_order1){
                int Y = starter->at(0);
                const std::vector<int>* tuples = &ppot_parent_1_.getValuesVec({Y});
                const std::vector<int>* tuplesU = &upot_parent_1_.getValuesVec({Y});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple1 = NULL;
                    if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int X = tuple1->at(0);
                    if(tuple1->at(1) == Y){
                        Tuple* saving2 = factory.addNewInternalTuple({X,Y},&_aux1);
                        const auto& insertResult = saving2->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving2->getId());
                            insertUndef(insertResult);
                            Tuple* saving1 = factory.addNewInternalTuple({X,Y},&_sup_1);
                            const auto& insertResult = saving1->setStatus(Undef);
                            if(insertResult.second){
                                factory.removeFromCollisionsList(saving1->getId());
                                insertUndef(insertResult);
                                Tuple* saving0 = factory.addNewInternalTuple({X,Y},&_order);
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
            if(starter->getPredicateName() == &_chain){
                int X = starter->at(0);
                int Y = starter->at(1);
                Tuple* tuple1 = factory.find({X,Y},&_ord_last);
                if(tuple1!=NULL && !tuple1->isFalse()){
                    Tuple* saving2 = factory.addNewInternalTuple({X,Y},&_aux2);
                    const auto& insertResult = saving2->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving2->getId());
                        insertUndef(insertResult);
                        Tuple* saving1 = factory.addNewInternalTuple({X},&_sup_2);
                        const auto& insertResult = saving1->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving1->getId());
                            insertUndef(insertResult);
                            Tuple* saving0 = factory.addNewInternalTuple({X},&_order1);
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
            if(starter->getPredicateName() == &_order){
                int X = starter->at(0);
                int Y1 = starter->at(1);
                Tuple* tuple1 = factory.find({X,Y1},&_ord_init);
                if(tuple1!=NULL && !tuple1->isFalse()){
                    Tuple* saving2 = factory.addNewInternalTuple({X,Y1},&_aux4);
                    const auto& insertResult = saving2->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving2->getId());
                        insertUndef(insertResult);
                        Tuple* saving1 = factory.addNewInternalTuple({X,Y1},&_sup_4);
                        const auto& insertResult = saving1->setStatus(Undef);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(saving1->getId());
                            insertUndef(insertResult);
                            Tuple* saving0 = factory.addNewInternalTuple({X,Y1},&_chain);
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
            if(starter->getPredicateName() == &_chain){
                int X = starter->at(0);
                int Y1 = starter->at(1);
                const std::vector<int>* tuples = &pord_next_0_1_.getValuesVec({X,Y1});
                const std::vector<int>* tuplesU = &uord_next_0_1_.getValuesVec({X,Y1});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple1 = NULL;
                    if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    if(tuple1->at(0) == X){
                        if(tuple1->at(1) == Y1){
                            int Y2 = tuple1->at(2);
                            Tuple* tuple2 = factory.find({X,Y2},&_order);
                            if(tuple2!=NULL && !tuple2->isFalse()){
                                Tuple* saving2 = factory.addNewInternalTuple({X,Y2,Y1},&_aux5);
                                const auto& insertResult = saving2->setStatus(Undef);
                                if(insertResult.second){
                                    factory.removeFromCollisionsList(saving2->getId());
                                    insertUndef(insertResult);
                                    Tuple* saving1 = factory.addNewInternalTuple({X,Y2},&_sup_5);
                                    const auto& insertResult = saving1->setStatus(Undef);
                                    if(insertResult.second){
                                        factory.removeFromCollisionsList(saving1->getId());
                                        insertUndef(insertResult);
                                        Tuple* saving0 = factory.addNewInternalTuple({X,Y2},&_chain);
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
            if(starter->getPredicateName() == &_order){
                int X = starter->at(0);
                int Y2 = starter->at(1);
                const std::vector<int>* tuples = &pord_next_0_2_.getValuesVec({X,Y2});
                const std::vector<int>* tuplesU = &uord_next_0_2_.getValuesVec({X,Y2});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple1 = NULL;
                    if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    if(tuple1->at(0) == X){
                        int Y1 = tuple1->at(1);
                        if(tuple1->at(2) == Y2){
                            Tuple* tuple2 = factory.find({X,Y1},&_chain);
                            if(tuple2!=NULL && !tuple2->isFalse()){
                                Tuple* saving2 = factory.addNewInternalTuple({X,Y2,Y1},&_aux5);
                                const auto& insertResult = saving2->setStatus(Undef);
                                if(insertResult.second){
                                    factory.removeFromCollisionsList(saving2->getId());
                                    insertUndef(insertResult);
                                    Tuple* saving1 = factory.addNewInternalTuple({X,Y2},&_sup_5);
                                    const auto& insertResult = saving1->setStatus(Undef);
                                    if(insertResult.second){
                                        factory.removeFromCollisionsList(saving1->getId());
                                        insertUndef(insertResult);
                                        Tuple* saving0 = factory.addNewInternalTuple({X,Y2},&_chain);
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
    //---------------------------------Recursive Component---------------------------------
    {
        predsToUnfoundedSet[&_order]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &porder_.getValuesVec({});
        const std::vector<int>* tuplesU = &uorder_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_sup_1]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &psup_1_.getValuesVec({});
        const std::vector<int>* tuplesU = &usup_1_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_aux1]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &paux1_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaux1_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_order1]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &porder1_.getValuesVec({});
        const std::vector<int>* tuplesU = &uorder1_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_sup_2]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &psup_2_.getValuesVec({});
        const std::vector<int>* tuplesU = &usup_2_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_aux2]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &paux2_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaux2_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_chain]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &pchain_.getValuesVec({});
        const std::vector<int>* tuplesU = &uchain_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_sup_4]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &psup_4_.getValuesVec({});
        const std::vector<int>* tuplesU = &usup_4_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_aux4]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &paux4_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaux4_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_chain]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &pchain_.getValuesVec({});
        const std::vector<int>* tuplesU = &uchain_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_sup_5]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &psup_5_.getValuesVec({});
        const std::vector<int>* tuplesU = &usup_5_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
        }
    }
    {
        predsToUnfoundedSet[&_aux5]=&unfoundedSetForComponent0;
        const std::vector<int>* tuples = &paux5_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaux5_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            if(i<tuples->size()) unfoundedSetForComponent0.insert(tuples->at(i));
            else unfoundedSetForComponent0.insert(tuplesU->at(i-tuples->size()));
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
    psup_4_.clear();
    psup_0_.clear();
    psup_1_.clear();
    psup_5_.clear();
    psup_3_.clear();
    psup_2_.clear();
    fsup_4_.clear();
    fsup_0_.clear();
    fsup_1_.clear();
    fsup_5_.clear();
    fsup_3_.clear();
    fsup_2_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aux0"] = &_aux0;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    stringToUniqueStringPointer["aux2"] = &_aux2;
    stringToUniqueStringPointer["aux3"] = &_aux3;
    stringToUniqueStringPointer["aux4"] = &_aux4;
    stringToUniqueStringPointer["aux5"] = &_aux5;
    stringToUniqueStringPointer["chain"] = &_chain;
    stringToUniqueStringPointer["node"] = &_node;
    stringToUniqueStringPointer["ord"] = &_ord;
    stringToUniqueStringPointer["ord_init"] = &_ord_init;
    stringToUniqueStringPointer["ord_last"] = &_ord_last;
    stringToUniqueStringPointer["ord_next"] = &_ord_next;
    stringToUniqueStringPointer["order"] = &_order;
    stringToUniqueStringPointer["order1"] = &_order1;
    stringToUniqueStringPointer["parent"] = &_parent;
    stringToUniqueStringPointer["pot_parent"] = &_pot_parent;
    stringToUniqueStringPointer["sup_0"] = &_sup_0;
    stringToUniqueStringPointer["sup_1"] = &_sup_1;
    stringToUniqueStringPointer["sup_2"] = &_sup_2;
    stringToUniqueStringPointer["sup_3"] = &_sup_3;
    stringToUniqueStringPointer["sup_4"] = &_sup_4;
    stringToUniqueStringPointer["sup_5"] = &_sup_5;
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
    for(int internalId : pchain_.getValuesVec({})){
        std::cout << factory.getTupleFromInternalID(internalId)->toString()<<" ";
    }
    for(int internalId : porder1_.getValuesVec({})){
        std::cout << factory.getTupleFromInternalID(internalId)->toString()<<" ";
    }
    for(int internalId : porder_.getValuesVec({})){
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
                        Tuple negativeTuple({X},&_order1);
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
                                    if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &porder_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uorder_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_order && !tupleUNegated)
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
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &porder1_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uorder1_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_order1 && !tupleUNegated)
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
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &pchain_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uchain_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_chain && !tupleUNegated)
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
                        Tuple negativeTuple({X0,X1},&_sup_4);
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
                                    if(tupleU->getPredicateName() != &_sup_4 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X0,X1},&_sup_5);
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
                                        if(tupleU->getPredicateName() != &_sup_5 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &pord_next_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uord_next_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_ord_next && !tupleUNegated)
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
                        int Y1 = tuple0->at(1);
                        int Y2 = tuple0->at(2);
                        const Tuple* tuple1 = factory.find({X,Y1},&_chain);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            const Tuple* tuple2 = factory.find({X,Y2},&_order);
                            if(tuple2!=NULL){
                                if(tuple2->isFalse())
                                tuple2=NULL;
                                else if(tuple2->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple2;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({X,Y2,Y1},&_aux5);
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
                                            if(tupleU->getPredicateName() != &_aux5 || !tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux5_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux5_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux5 && !tupleUNegated)
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
                        int Y2 = tuple0->at(1);
                        int Y1 = tuple0->at(2);
                        Tuple negativeTuple({X,Y2},&_order);
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
                                    if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux5_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux5_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux5 && !tupleUNegated)
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
                        int Y2 = tuple0->at(1);
                        int Y1 = tuple0->at(2);
                        Tuple negativeTuple({X,Y1},&_chain);
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
                                    if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux5_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux5_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux5 && !tupleUNegated)
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
                        int Y2 = tuple0->at(1);
                        int Y1 = tuple0->at(2);
                        Tuple negativeTuple({X,Y1,Y2},&_ord_next);
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
                                    if(tupleU->getPredicateName() != &_ord_next || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &psup_5_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usup_5_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_sup_5 && !tupleUNegated)
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
                        int Y2 = tuple0->at(1);
                        Tuple negativeTuple({X,Y2},&_chain);
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
                                    if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &pord_init_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uord_init_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_ord_init && !tupleUNegated)
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
                        int Y1 = tuple0->at(1);
                        const Tuple* tuple1 = factory.find({X,Y1},&_order);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X,Y1},&_aux4);
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
                                        if(tupleU->getPredicateName() != &_aux4 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux4_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux4_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux4 && !tupleUNegated)
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
                        int Y1 = tuple0->at(1);
                        Tuple negativeTuple({X,Y1},&_order);
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
                                    if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux4_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux4_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux4 && !tupleUNegated)
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
                        int Y1 = tuple0->at(1);
                        Tuple negativeTuple({X,Y1},&_ord_init);
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
                                    if(tupleU->getPredicateName() != &_ord_init || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &psup_4_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usup_4_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_sup_4 && !tupleUNegated)
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
                        int Y1 = tuple0->at(1);
                        Tuple negativeTuple({X,Y1},&_chain);
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
                                    if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X},&_ord);
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
                                    if(tupleU->getPredicateName() != &_ord || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X},&_aux3);
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
                                        if(tupleU->getPredicateName() != &_aux3 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux3_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux3_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux3 && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({X},&_ord);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_ord || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &paux3_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux3_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux3 && !tupleUNegated)
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
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X},&_order1);
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
                                    if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &pord_last_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uord_last_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_ord_last && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({X,Y},&_chain);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple1))
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
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X,Y},&_chain);
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
                                    if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X,Y},&_ord_last);
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
                                    if(tupleU->getPredicateName() != &_ord_last || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X},&_order1);
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
                                    if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &ppot_parent_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upot_parent_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_pot_parent && !tupleUNegated)
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
                        const Tuple* tuple1 = factory.find({Y},&_order1);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_order1 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X,Y},&_aux1);
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
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        int X = tuple0->at(0);
                        int Y = tuple0->at(1);
                        Tuple negativeTuple({Y},&_order1);
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
                                    if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        int X = tuple0->at(0);
                        int Y = tuple0->at(1);
                        Tuple negativeTuple({X,Y},&_pot_parent);
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
                                    if(tupleU->getPredicateName() != &_pot_parent || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X,Y},&_order);
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
                                    if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const std::vector<int>* tuples = &ppot_parent_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upot_parent_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_pot_parent && !tupleUNegated)
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
                        Tuple negativeTuple({X,Y},&_parent);
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
                                    if(tupleU->getPredicateName() != &_parent || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple negativeTuple({X,Y},&_aux0);
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
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        const Tuple* tuple1 = factory.find({X,Y},&_parent);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_parent || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X,Y},&_pot_parent);
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
                                    if(tupleU->getPredicateName() != &_pot_parent || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                        Tuple negativeTuple({X,Y},&_order);
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
                                    if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y}, &_aux0);
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
                Tuple* currentBody = factory.find({X,Y}, &_aux0);
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
                const Tuple* currentBody = factory.find({X, Y}, &_aux0);
                if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(currentBody!=NULL && currentBody->isTrue())
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* trueHeads = &psup_1_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y}, &_aux1);
                if(!currentBody->isUndef() && !currentBody->isTrue()){
                    propagatedLiterals.push_back(1);
                    return;
                }else if(currentBody->isUndef()){
                    propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* falseHeads = &fsup_1_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y}, &_aux1);
                if(currentBody->isTrue()){
                    propagatedLiterals.push_back(1);
                    return;
                }else if(currentBody->isUndef()){
                    propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* undefHeads = &usup_1_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                int X = currentHead->at(0);
                int Y = currentHead->at(1);
                const Tuple* currentBody = factory.find({X, Y}, &_aux1);
                if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(currentBody!=NULL && currentBody->isTrue())
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
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
                Tuple* currentBody = factory.find({X}, &_aux3);
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
                Tuple* currentBody = factory.find({X}, &_aux3);
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
                const Tuple* currentBody = factory.find({X}, &_aux3);
                if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(currentBody!=NULL && currentBody->isTrue())
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* trueHeads = &psup_4_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = currentHead->at(0);
                int Y1 = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y1}, &_aux4);
                if(!currentBody->isUndef() && !currentBody->isTrue()){
                    propagatedLiterals.push_back(1);
                    return;
                }else if(currentBody->isUndef()){
                    propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* falseHeads = &fsup_4_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                int X = currentHead->at(0);
                int Y1 = currentHead->at(1);
                Tuple* currentBody = factory.find({X,Y1}, &_aux4);
                if(currentBody->isTrue()){
                    propagatedLiterals.push_back(1);
                    return;
                }else if(currentBody->isUndef()){
                    propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            const std::vector<int>* undefHeads = &usup_4_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                int X = currentHead->at(0);
                int Y1 = currentHead->at(1);
                const Tuple* currentBody = factory.find({X, Y1}, &_aux4);
                if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                    propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else if(currentBody!=NULL && currentBody->isTrue())
                    propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                else i++;
            }
        }
        {
            const std::vector<int>* trueHeads = &psup_5_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                int X = currentHead->at(0);
                int Y2 = currentHead->at(1);
                const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X, Y2});
                const std::vector<int>* tuplesU = &uaux5_0_1_.getValuesVec({X, Y2});
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
            const std::vector<int>* falseHeads = &fsup_5_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                int X = currentHead->at(0);
                int Y2 = currentHead->at(1);
                const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X, Y2});
                const std::vector<int>* tuplesU = &uaux5_0_1_.getValuesVec({X, Y2});
                if(tuples->size()>0){
                    propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const std::vector<int>* undefHeads = &usup_5_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                int X = currentHead->at(0);
                int Y2 = currentHead->at(1);
                const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X, Y2});
                const std::vector<int>* tuplesU = &uaux5_0_1_.getValuesVec({X, Y2});
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
            if(starter.getPredicateName() == &_order && startVar < 0){
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X,Y},&_order);
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
                            if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            Tuple* currentBody = factory.find({X,Y}, &_aux0);
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
            if(starter.getPredicateName() == &_pot_parent && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_aux0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux0 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y},&_pot_parent);
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
                            if(tupleU->getPredicateName() != &_pot_parent || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_parent && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_aux0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux0 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_parent);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_parent || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux0 && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_pot_parent);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_pot_parent || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y},&_parent);
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
                                if(tupleU->getPredicateName() != &_parent || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_parent && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_pot_parent);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_pot_parent || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y},&_aux0);
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_pot_parent && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y},&_parent);
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
                            if(tupleU->getPredicateName() != &_parent || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y},&_aux0);
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
                                shared_reason.get()->insert(it*-1);
                            }
                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                int it = tuple2->getId();
                                shared_reason.get()->insert(it*-1);
                            }
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order && startVar < 0){
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X,Y},&_order);
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
                            if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        if(starter.getPredicateName() == &_aux1){
            int X = starter.at(0);
            int Y = starter.at(1);
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
        }else if(starter.getPredicateName() == &_sup_1){
            int X = starter.at(0);
            int Y = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            Tuple* currentBody = factory.find({X,Y}, &_aux1);
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
            if(starter.getPredicateName() == &_pot_parent && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_aux1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux1 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux1 && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y},&_pot_parent);
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
                            if(tupleU->getPredicateName() != &_pot_parent || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order1 && startVar < 0){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux1_1_.getValuesVec({Y});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_1_.getValuesVec({Y});
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({Y},&_order1);
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
                            if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_pot_parent);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_pot_parent || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({Y},&_order1);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_order1 || tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order1 && startVar > 0){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &ppot_parent_1_.getValuesVec({Y});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upot_parent_1_.getValuesVec({Y});
                else if(tupleU->getPredicateName() == &_pot_parent && !tupleUNegated)
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
                        Tuple negativeTuple({X,Y},&_aux1);
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
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_pot_parent && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({Y},&_order1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_order1 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y},&_aux1);
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        }
        {
            if(starter.getPredicateName() == &_order1 && startVar < 0){
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X},&_order1);
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
                            if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_ord_last && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X,Y},&_ord_last);
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
                            if(tupleU->getPredicateName() != &_ord_last || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_chain && startVar < 0){
                int X = starter[0];
                int Y = starter[1];
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X,Y},&_chain);
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
                            if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const Tuple* tuple1 = factory.find({X,Y},&_ord_last);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_ord_last || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({X,Y},&_chain);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_chain && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_ord_last);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_ord_last || tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_ord_last && startVar > 0){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y},&_chain);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        }
        {
            if(starter.getPredicateName() == &_order1 && startVar < 0){
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X},&_order1);
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
                            if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        if(starter.getPredicateName() == &_aux3){
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
            Tuple* currentBody = factory.find({X}, &_aux3);
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
            if(starter.getPredicateName() == &_node && startVar < 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_aux3);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux3 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux3 && startVar > 0){
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_ord && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_aux3);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux3 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux3 && startVar > 0){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X},&_ord);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_ord || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux3 && startVar < 0){
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
                    Tuple negativeTuple({X},&_ord);
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
                                if(tupleU->getPredicateName() != &_ord || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_ord && startVar < 0){
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
                    Tuple negativeTuple({X},&_aux3);
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
                                if(tupleU->getPredicateName() != &_aux3 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X},&_ord);
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
                            if(tupleU->getPredicateName() != &_ord || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X},&_aux3);
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
                                if(tupleU->getPredicateName() != &_aux3 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_chain && startVar < 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_sup_4);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_sup_4 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_sup_4 && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y1},&_chain);
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
                            if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        if(starter.getPredicateName() == &_aux4){
            int X = starter.at(0);
            int Y1 = starter.at(1);
            Tuple* head = factory.find({X,Y1}, &_sup_4);
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
        }else if(starter.getPredicateName() == &_sup_4){
            int X = starter.at(0);
            int Y1 = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            Tuple* currentBody = factory.find({X,Y1}, &_aux4);
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
            if(starter.getPredicateName() == &_ord_init && startVar < 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_aux4);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux4 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux4 && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y1},&_ord_init);
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
                            if(tupleU->getPredicateName() != &_ord_init || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order && startVar < 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_aux4);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux4 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux4 && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y1},&_order);
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
                            if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux4 && startVar < 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_ord_init);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_ord_init || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({X,Y1},&_order);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_ord_init);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_ord_init || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y1},&_aux4);
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
                                if(tupleU->getPredicateName() != &_aux4 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_ord_init && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_order);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X,Y1},&_aux4);
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
                                if(tupleU->getPredicateName() != &_aux4 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        }
        {
            if(starter.getPredicateName() == &_chain && startVar < 0){
                int X = starter[0];
                int Y2 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y2},&_sup_5);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_sup_5 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_sup_5 && startVar > 0){
                int X = starter[0];
                int Y2 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y2},&_chain);
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
                            if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        if(starter.getPredicateName() == &_aux5){
            int X = starter.at(0);
            int Y2 = starter.at(1);
            int Y1 = starter.at(2);
            Tuple* head = factory.find({X,Y2}, &_sup_5);
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
                const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X, Y2});
                const std::vector<int>* tuplesU = &uaux5_0_1_.getValuesVec({X, Y2});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux5_0_1_.getValuesVec({X, Y2});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux5_0_1_.getValuesVec({X, Y2});
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
                        const std::vector<int>* tuplesF = &faux5_0_1_.getValuesVec({X, Y2});
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
        }else if(starter.getPredicateName() == &_sup_5){
            int X = starter.at(0);
            int Y2 = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X,Y2});
            const std::vector<int>* tuplesU = &uaux5_0_1_.getValuesVec({X,Y2});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        const std::vector<int>* tuplesF = &faux5_0_1_.getValuesVec({X,Y2});
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
                        const std::vector<int>* tuplesF = &faux5_0_1_.getValuesVec({X,Y2});
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
            if(starter.getPredicateName() == &_ord_next && startVar < 0){
                int X = starter[0];
                int Y1 = starter[1];
                int Y2 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y2,Y1},&_aux5);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux5 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux5 && startVar > 0){
                int X = starter[0];
                int Y2 = starter[1];
                int Y1 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y1,Y2},&_ord_next);
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
                            if(tupleU->getPredicateName() != &_ord_next || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_chain && startVar < 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux5_0_2_.getValuesVec({X,Y1});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux5_0_2_.getValuesVec({X,Y1});
                else if(tupleU->getPredicateName() == &_aux5 && !tupleUNegated)
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
                        if(tupleU->at(0) == X && tupleU->at(2) == Y1)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y2 = tuple1->at(1);
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux5 && startVar > 0){
                int X = starter[0];
                int Y2 = starter[1];
                int Y1 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y1},&_chain);
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
                            if(tupleU->getPredicateName() != &_chain || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order && startVar < 0){
                int X = starter[0];
                int Y2 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux5_0_1_.getValuesVec({X,Y2});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux5_0_1_.getValuesVec({X,Y2});
                else if(tupleU->getPredicateName() == &_aux5 && !tupleUNegated)
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
                        if(tupleU->at(0) == X && tupleU->at(1) == Y2)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y1 = tuple1->at(2);
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux5 && startVar > 0){
                int X = starter[0];
                int Y2 = starter[1];
                int Y1 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X,Y2},&_order);
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
                            if(tupleU->getPredicateName() != &_order || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_aux5 && startVar < 0){
                int X = starter[0];
                int Y2 = starter[1];
                int Y1 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1,Y2},&_ord_next);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_ord_next || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({X,Y1},&_chain);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
                        const Tuple* tuple3 = factory.find({X,Y2},&_order);
                        if(tuple3!=NULL){
                            if(tuple3->isFalse())
                            tuple3=NULL;
                            else if(tuple3->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple3;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple3))
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
                                    shared_reason.get()->insert(it*1);
                                }
                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order && startVar > 0){
                int X = starter[0];
                int Y2 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pord_next_0_2_.getValuesVec({X,Y2});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uord_next_0_2_.getValuesVec({X,Y2});
                else if(tupleU->getPredicateName() == &_ord_next && !tupleUNegated)
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
                        if(tupleU->at(0) == X && tupleU->at(2) == Y2)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y1 = tuple1->at(1);
                        const Tuple* tuple2 = factory.find({X,Y1},&_chain);
                        if(tuple2!=NULL){
                            if(tuple2->isFalse())
                            tuple2=NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple negativeTuple({X,Y2,Y1},&_aux5);
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
                                        if(tupleU->getPredicateName() != &_aux5 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        shared_reason.get()->insert(it*1);
                                    }
                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        shared_reason.get()->insert(it*-1);
                                    }
                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                    if(!itReason.second && itReason.first->second.get()->empty())
                                        itReason.first->second=shared_reason;
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_chain && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pord_next_0_1_.getValuesVec({X,Y1});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uord_next_0_1_.getValuesVec({X,Y1});
                else if(tupleU->getPredicateName() == &_ord_next && !tupleUNegated)
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
                        if(tupleU->at(0) == X && tupleU->at(1) == Y1)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y2 = tuple1->at(2);
                        const Tuple* tuple2 = factory.find({X,Y2},&_order);
                        if(tuple2!=NULL){
                            if(tuple2->isFalse())
                            tuple2=NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple negativeTuple({X,Y2,Y1},&_aux5);
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
                                        if(tupleU->getPredicateName() != &_aux5 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        shared_reason.get()->insert(it*1);
                                    }
                                    if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        shared_reason.get()->insert(it*-1);
                                    }
                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                    if(!itReason.second && itReason.first->second.get()->empty())
                                        itReason.first->second=shared_reason;
                                    if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_ord_next && startVar > 0){
                int X = starter[0];
                int Y1 = starter[1];
                int Y2 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X,Y1},&_chain);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({X,Y2},&_order);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple negativeTuple({X,Y2,Y1},&_aux5);
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
                                    if(tupleU->getPredicateName() != &_aux5 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                    shared_reason.get()->insert(it*1);
                                }
                                if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                    int it = tuple3->getId();
                                    shared_reason.get()->insert(it*-1);
                                }
                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
        }
        {
            if(starter.getPredicateName() == &_order1 && startVar < 0){
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                Tuple negativeTuple({X},&_order1);
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
                            if(tupleU->getPredicateName() != &_order1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_sup_5 && startVar < 0){
                int X0 = starter[0];
                int X1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0,X1},&_chain);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0,X1},&_sup_4);
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
                                if(tupleU->getPredicateName() != &_sup_4 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_sup_4 && startVar < 0){
                int X0 = starter[0];
                int X1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0,X1},&_chain);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_chain || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0,X1},&_sup_5);
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
                                if(tupleU->getPredicateName() != &_sup_5 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_chain && startVar > 0){
                int X0 = starter[0];
                int X1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({X0,X1},&_sup_4);
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
                            if(tupleU->getPredicateName() != &_sup_4 || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({X0,X1},&_sup_5);
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
                                if(tupleU->getPredicateName() != &_sup_5 || !tupleUNegated || !(*tupleU == *tuple2))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_sup_3 && startVar < 0){
                int X0 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({X0},&_order1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_order1 || tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const Tuple* tuple1 = factory.find({X0},&_order1);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_order1 || tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order1 && startVar > 0){
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const Tuple* tuple1 = factory.find({X0,X1},&_order);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
                const Tuple* tuple1 = factory.find({X0,X1},&_order);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_order || tupleUNegated || !(*tupleU == *tuple1))
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
            if(starter.getPredicateName() == &_order && startVar > 0){
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
                            if(tupleU->getPredicateName() != &_sup_4 && tupleU->getPredicateName() != &_aux5 && tupleU->getPredicateName() != &_chain && tupleU->getPredicateName() != &_aux3 && tupleU->getPredicateName() != &_order && tupleU->getPredicateName() != &_aux1 && tupleU->getPredicateName() != &_aux2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_sup_0 && tupleU->getPredicateName() != &_sup_1 && tupleU->getPredicateName() != &_aux4 && tupleU->getPredicateName() != &_order1 && tupleU->getPredicateName() != &_sup_5 && tupleU->getPredicateName() != &_sup_2 && tupleU->getPredicateName() != &_sup_3)
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
