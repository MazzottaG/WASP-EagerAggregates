#include "Executor.h"

#include "utils/ConstantsManager.h"

#include "DLV2libs/input/InputDirector.h"

#include "parsing/AspCore2InstanceBuilder.h"

#include "datastructures/PredicateSet.h"

#include "datastructures/ReasonTable.h"

#include "datastructures/PostponedReasons.h"

#include "datastructures/DynamicTrie.h"

#include "datastructures/VariablesMapping.h"

#include "datastructures/VarsIndex.h"

#include "datastructures/TupleFactory.h"

#include "datastructures/SmartPredicateSet.h"

#include "datastructures/AuxiliaryMapSmart.h"

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
Executor::Executor() {}

typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<Tuple,S> ;
typedef std::vector<const Tuple* > Tuples;
using PredicateWSet = SmartPredicateSet;

std::unordered_map<const std::string*, PredicateWSet*> predicateWSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateFSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateUSetMap;
const std::string _aggr_id0 = "aggr_id0";
PredicateWSet waggr_id0(2);
PredicateWSet uaggr_id0(2);
PredicateWSet faggr_id0(2);
const std::string _aggr_id1 = "aggr_id1";
PredicateWSet waggr_id1(2);
PredicateWSet uaggr_id1(2);
PredicateWSet faggr_id1(2);
const std::string _aggr_id2 = "aggr_id2";
PredicateWSet waggr_id2(2);
PredicateWSet uaggr_id2(2);
PredicateWSet faggr_id2(2);
const std::string _aggr_id3 = "aggr_id3";
PredicateWSet waggr_id3(2);
PredicateWSet uaggr_id3(2);
PredicateWSet faggr_id3(2);
const std::string _aggr_set0 = "aggr_set0";
PredicateWSet waggr_set0(4);
PredicateWSet uaggr_set0(4);
PredicateWSet faggr_set0(4);
const std::string _aux1 = "aux1";
PredicateWSet waux1(6);
PredicateWSet uaux1(6);
PredicateWSet faux1(6);
const std::string _body0 = "body0";
PredicateWSet wbody0(2);
PredicateWSet ubody0(2);
PredicateWSet fbody0(2);
const std::string _body1 = "body1";
PredicateWSet wbody1(2);
PredicateWSet ubody1(2);
PredicateWSet fbody1(2);
const std::string _body2 = "body2";
PredicateWSet wbody2(2);
PredicateWSet ubody2(2);
PredicateWSet fbody2(2);
const std::string _diff = "diff";
PredicateWSet wdiff(2);
PredicateWSet udiff(2);
PredicateWSet fdiff(2);
const std::string _lives = "lives";
PredicateWSet wlives(2);
PredicateWSet ulives(2);
PredicateWSet flives(2);
const std::string _value = "value";
PredicateWSet wvalue(1);
PredicateWSet uvalue(1);
PredicateWSet fvalue(1);
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,UnorderedSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
bool unRoll=false;
Executor::~Executor() {
}


const std::vector<const Tuple* > EMPTY_TUPLES;
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
AuxMap<0> pvalue_({});
AuxMap<0> uvalue_({});
AuxMap<0> fvalue_({});
AuxMap<0> plives_({});
AuxMap<0> ulives_({});
AuxMap<0> flives_({});
AuxMap<0> pdiff_({});
AuxMap<0> udiff_({});
AuxMap<0> fdiff_({});
AuxMap<0> pbody0_({});
AuxMap<0> ubody0_({});
AuxMap<0> fbody0_({});
AuxMap<32> pbody0_1_({1});
AuxMap<32> ubody0_1_({1});
AuxMap<32> fbody0_1_({1});
AuxMap<32> pbody0_0_({0});
AuxMap<32> ubody0_0_({0});
AuxMap<32> fbody0_0_({0});
AuxMap<32> plives_0_({0});
AuxMap<32> ulives_0_({0});
AuxMap<32> flives_0_({0});
AuxMap<32> plives_1_({1});
AuxMap<32> ulives_1_({1});
AuxMap<32> flives_1_({1});
AuxMap<128> paux1_0_1_2_3_({0,1,2,3});
AuxMap<128> uaux1_0_1_2_3_({0,1,2,3});
AuxMap<128> faux1_0_1_2_3_({0,1,2,3});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<0> paux1_({});
AuxMap<0> uaux1_({});
AuxMap<0> faux1_({});
AuxMap<64> paux1_4_5_({4,5});
AuxMap<64> uaux1_4_5_({4,5});
AuxMap<64> faux1_4_5_({4,5});
AuxMap<64> paux1_0_1_({0,1});
AuxMap<64> uaux1_0_1_({0,1});
AuxMap<64> faux1_0_1_({0,1});
AuxMap<1> paggr_id0_({});
AuxMap<1> uaggr_id0_({});
AuxMap<1> faggr_id0_({});
AuxMap<64> paggr_id0_0_1_({0,1});
AuxMap<64> uaggr_id0_0_1_({0,1});
AuxMap<64> faggr_id0_0_1_({0,1});
AuxMap<64> paggr_set0_2_3_({2,3});
AuxMap<64> uaggr_set0_2_3_({2,3});
AuxMap<64> faggr_set0_2_3_({2,3});
AuxMap<0> pbody1_({});
AuxMap<0> ubody1_({});
AuxMap<0> fbody1_({});
AuxMap<32> pbody1_1_({1});
AuxMap<32> ubody1_1_({1});
AuxMap<32> fbody1_1_({1});
AuxMap<32> pbody1_0_({0});
AuxMap<32> ubody1_0_({0});
AuxMap<32> fbody1_0_({0});
AuxMap<1> paggr_id1_({});
AuxMap<1> uaggr_id1_({});
AuxMap<1> faggr_id1_({});
AuxMap<64> paggr_id1_0_1_({0,1});
AuxMap<64> uaggr_id1_0_1_({0,1});
AuxMap<64> faggr_id1_0_1_({0,1});
AuxMap<0> pbody2_({});
AuxMap<0> ubody2_({});
AuxMap<0> fbody2_({});
AuxMap<32> pbody2_1_({1});
AuxMap<32> ubody2_1_({1});
AuxMap<32> fbody2_1_({1});
AuxMap<32> pbody2_0_({0});
AuxMap<32> ubody2_0_({0});
AuxMap<32> fbody2_0_({0});
AuxMap<1> paggr_id2_({});
AuxMap<1> uaggr_id2_({});
AuxMap<1> faggr_id2_({});
AuxMap<64> paggr_id2_0_1_({0,1});
AuxMap<64> uaggr_id2_0_1_({0,1});
AuxMap<64> faggr_id2_0_1_({0,1});
AuxMap<1> paggr_id3_({});
AuxMap<1> uaggr_id3_({});
AuxMap<1> faggr_id3_({});
AuxMap<64> paggr_id3_0_1_({0,1});
AuxMap<64> uaggr_id3_0_1_({0,1});
AuxMap<64> faggr_id3_0_1_({0,1});
void Executor::handleConflict(int literal){
    if(currentDecisionLevel == -1){
        propagatedLiterals.insert(-1);
        return;
    }

    std::unordered_set<int> visitedLiterals;
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    explainExternalLiteral(literal,conflictReason,visitedLiterals,true);
    explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);
    propagatedLiterals.insert(-1);
    reasonForLiteral.erase(literal);
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
        for(unsigned i = 0; i<reasonForLiteral[lit].size(); i++){
            int reasonLiteral=reasonForLiteral[lit][i];
            Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);
            if(visitedLiteral.count(reasonLiteral) == 0){
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

inline void insertFalse(std::pair<const TupleLight *, bool> insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id2){
        faggr_id2_.insert2(*insertResult.first);
        faggr_id2_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body2){
        fbody2_.insert2(*insertResult.first);
        fbody2_0_.insert2(*insertResult.first);
        fbody2_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body1){
        fbody1_.insert2(*insertResult.first);
        fbody1_0_.insert2(*insertResult.first);
        fbody1_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
        faggr_set0_2_3_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2(*insertResult.first);
        faggr_id1_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
        faggr_id0_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aux1){
        faux1_.insert2(*insertResult.first);
        faux1_0_1_.insert2(*insertResult.first);
        faux1_0_1_2_3_.insert2(*insertResult.first);
        faux1_4_5_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body0){
        fbody0_.insert2(*insertResult.first);
        fbody0_0_.insert2(*insertResult.first);
        fbody0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_diff){
        fdiff_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_lives){
        flives_.insert2(*insertResult.first);
        flives_0_.insert2(*insertResult.first);
        flives_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id3){
        faggr_id3_.insert2(*insertResult.first);
        faggr_id3_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_value){
        fvalue_.insert2(*insertResult.first);
    }
}
inline void insertTrue(std::pair<const TupleLight *, bool> insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id2){
        paggr_id2_.insert2(*insertResult.first);
        paggr_id2_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body2){
        pbody2_.insert2(*insertResult.first);
        pbody2_0_.insert2(*insertResult.first);
        pbody2_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body1){
        pbody1_.insert2(*insertResult.first);
        pbody1_0_.insert2(*insertResult.first);
        pbody1_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
        paggr_set0_2_3_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2(*insertResult.first);
        paggr_id1_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
        paggr_id0_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aux1){
        paux1_.insert2(*insertResult.first);
        paux1_0_1_.insert2(*insertResult.first);
        paux1_0_1_2_3_.insert2(*insertResult.first);
        paux1_4_5_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body0){
        pbody0_.insert2(*insertResult.first);
        pbody0_0_.insert2(*insertResult.first);
        pbody0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_diff){
        pdiff_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_lives){
        plives_.insert2(*insertResult.first);
        plives_0_.insert2(*insertResult.first);
        plives_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id3){
        paggr_id3_.insert2(*insertResult.first);
        paggr_id3_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_value){
        pvalue_.insert2(*insertResult.first);
    }
}
inline void insertUndef(std::pair<const TupleLight *, bool> insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id2){
        uaggr_id2_.insert2(*insertResult.first);
        uaggr_id2_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body2){
        ubody2_.insert2(*insertResult.first);
        ubody2_0_.insert2(*insertResult.first);
        ubody2_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body1){
        ubody1_.insert2(*insertResult.first);
        ubody1_0_.insert2(*insertResult.first);
        ubody1_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
        uaggr_set0_2_3_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2(*insertResult.first);
        uaggr_id1_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
        uaggr_id0_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aux1){
        uaux1_.insert2(*insertResult.first);
        uaux1_0_1_.insert2(*insertResult.first);
        uaux1_0_1_2_3_.insert2(*insertResult.first);
        uaux1_4_5_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_body0){
        ubody0_.insert2(*insertResult.first);
        ubody0_0_.insert2(*insertResult.first);
        ubody0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_diff){
        udiff_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_lives){
        ulives_.insert2(*insertResult.first);
        ulives_0_.insert2(*insertResult.first);
        ulives_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_id3){
        uaggr_id3_.insert2(*insertResult.first);
        uaggr_id3_0_1_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_value){
        uvalue_.insert2(*insertResult.first);
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
    std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple->getPredicateName());
    if(uSetIt!=predicateUSetMap.end()) {
        uSetIt->second->erase(*tuple);
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple->getPredicateName());
    if (it == predicateWSetMap.end()) {
        } else {
        if (var > 0) {
            const auto& insertResult = it->second->insert(tuple);
            if (insertResult.second) {
                insertTrue(insertResult);
            }
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
    if (fSetIt == predicateFSetMap.end()) {
        } else {
        if (var < 0) {
            const auto& insertResult = fSetIt->second->insert(tuple);
            if (insertResult.second) {
                insertFalse(insertResult);
            }
        }
    }
}
inline void Executor::onLiteralTrue(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    unRoll=false;
    std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple->getPredicateName());
    if(uSetIt!=predicateUSetMap.end()) {
        uSetIt->second->erase(*tuple);
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple->getPredicateName());
    if (it == predicateWSetMap.end()) {
        } else {
        if (var > 0) {
            const auto& insertResult = it->second->insert(tuple);
            if (insertResult.second) {
                insertTrue(insertResult);
            }
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
    if (fSetIt == predicateFSetMap.end()) {
        } else {
        if (var < 0) {
            const auto& insertResult = fSetIt->second->insert(tuple);
            if (insertResult.second) {
                insertFalse(insertResult);
            }
        }
    }
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    int internalVar = var > 0 ? tuple->getId() : -tuple->getId();
    reasonForLiteral.erase(internalVar);
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    if (var > 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple->getPredicateName());
        if (wSetIt != predicateWSetMap.end()) {
            wSetIt->second->erase(*tuple);
        }
    }
    if (var < 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
        if (fSetIt != predicateWSetMap.end()) {
            fSetIt->second->erase(*tuple);
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple->getPredicateName());
    if (it == predicateUSetMap.end()) {
        } else {
        const auto& insertResult = it->second->insert(tuple);
        if (insertResult.second) {
            insertUndef(insertResult);
        }
    }
    if(currentDecisionLevel >= 0){
    }
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {
        const std::vector<const Tuple*>* tuples = &plives_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ulives_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int XDX = tuple->at(0);
            int YDY = tuple->at(1);
            const std::vector<const Tuple*>* tuples = &pdiff_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &udiff_.getValues({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=tuples->at(i);
                else
                    tuple=tuplesU->at(i-tuples->size());
                int DX = tuple->at(0);
                int DY = tuple->at(1);
                int X = XDX - DX;
                int Y = YDY - DY;
                Tuple* aux = factory.addNewInternalTuple({DX,DY,Y,X,XDX,YDY}, &_aux1);
                if(uaux1.find(*aux) == NULL){
                    const auto& insertResult = uaux1.insert(aux);
                    if (insertResult.second) {
                        insertUndef(insertResult);
                        {
                            Tuple* head = factory.addNewInternalTuple({DX,DY,Y,X},&_aggr_set0);
                            if(uaggr_set0.find(*head)==NULL){
                                const auto& headInsertResult = uaggr_set0.insert(head);
                                if (headInsertResult.second) {
                                    insertUndef(headInsertResult);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &pvalue_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uvalue_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int X = tuple->at(0);
            const std::vector<const Tuple*>* tuples = &pvalue_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uvalue_.getValues({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=tuples->at(i);
                else
                    tuple=tuplesU->at(i-tuples->size());
                int Y = tuple->at(0);
                Tuple* boundTuple = factory.addNewInternalTuple({X,Y}, &_lives);
                if(wlives.find(*boundTuple)==NULL){
                    Tuple* aux = factory.addNewInternalTuple({Y,X}, &_body2);
                    if(ubody2.find(*aux) == NULL){
                        const auto& insertResult = ubody2.insert(aux);
                        if (insertResult.second) {
                            insertUndef(insertResult);
                            {
                                Tuple* head = factory.addNewInternalTuple({Y,X},&_aggr_id2);
                                if(uaggr_id2.find(*head)==NULL){
                                    const auto& headInsertResult = uaggr_id2.insert(head);
                                    if (headInsertResult.second) {
                                        insertUndef(headInsertResult);
                                    }
                                }
                            }
                            {
                                Tuple* head = factory.addNewInternalTuple({Y,X},&_aggr_id3);
                                if(uaggr_id3.find(*head)==NULL){
                                    const auto& headInsertResult = uaggr_id3.insert(head);
                                    if (headInsertResult.second) {
                                        insertUndef(headInsertResult);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &plives_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ulives_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int X = tuple->at(0);
            int Y = tuple->at(1);
            Tuple* boundTuple = factory.addNewInternalTuple({X}, &_value);
            if(uvalue.find(*boundTuple)!=NULL || wvalue.find(*boundTuple)!=NULL){
                Tuple* boundTuple = factory.addNewInternalTuple({Y}, &_value);
                if(uvalue.find(*boundTuple)!=NULL || wvalue.find(*boundTuple)!=NULL){
                    Tuple* aux = factory.addNewInternalTuple({Y,X}, &_body1);
                    if(ubody1.find(*aux) == NULL){
                        const auto& insertResult = ubody1.insert(aux);
                        if (insertResult.second) {
                            insertUndef(insertResult);
                            {
                                Tuple* head = factory.addNewInternalTuple({Y,X},&_aggr_id1);
                                if(uaggr_id1.find(*head)==NULL){
                                    const auto& headInsertResult = uaggr_id1.insert(head);
                                    if (headInsertResult.second) {
                                        insertUndef(headInsertResult);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &plives_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ulives_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int X = tuple->at(0);
            int Y = tuple->at(1);
            Tuple* boundTuple = factory.addNewInternalTuple({X}, &_value);
            if(uvalue.find(*boundTuple)!=NULL || wvalue.find(*boundTuple)!=NULL){
                Tuple* boundTuple = factory.addNewInternalTuple({Y}, &_value);
                if(uvalue.find(*boundTuple)!=NULL || wvalue.find(*boundTuple)!=NULL){
                    Tuple* aux = factory.addNewInternalTuple({Y,X}, &_body0);
                    if(ubody0.find(*aux) == NULL){
                        const auto& insertResult = ubody0.insert(aux);
                        if (insertResult.second) {
                            insertUndef(insertResult);
                            {
                                Tuple* head = factory.addNewInternalTuple({Y,X},&_aggr_id0);
                                if(uaggr_id0.find(*head)==NULL){
                                    const auto& headInsertResult = uaggr_id0.insert(head);
                                    if (headInsertResult.second) {
                                        insertUndef(headInsertResult);
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
inline void Executor::addedVarName(int var, const std::string & atom) {
    std::vector<int> terms;
    const std::string* predicate = parseTuple(atom,terms);
    factory.addNewTuple(terms,predicate,var);
}
void Executor::clearPropagations() {
    propagatedLiteralsAndReasons.clear();
}
void Executor::clear() {
    failedConstraints.clear();
    waggr_id0.clear();
    waggr_id1.clear();
    waggr_id2.clear();
    waggr_id3.clear();
    waggr_set0.clear();
    paggr_id2_.clear();
    paggr_id2_0_1_.clear();
    paggr_set0_.clear();
    paggr_set0_2_3_.clear();
    paggr_id1_.clear();
    paggr_id1_0_1_.clear();
    paggr_id0_.clear();
    paggr_id0_0_1_.clear();
    paggr_id3_.clear();
    paggr_id3_0_1_.clear();
    faggr_id2_.clear();
    faggr_id2_0_1_.clear();
    faggr_set0_.clear();
    faggr_set0_2_3_.clear();
    faggr_id1_.clear();
    faggr_id1_0_1_.clear();
    faggr_id0_.clear();
    faggr_id0_0_1_.clear();
    faggr_id3_.clear();
    faggr_id3_0_1_.clear();
}
void Executor::init() {
    predicateWSetMap[&_aggr_id0]=&waggr_id0;
    predicateUSetMap[&_aggr_id0]=&uaggr_id0;
    predicateFSetMap[&_aggr_id0]=&faggr_id0;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    predicateWSetMap[&_aggr_id1]=&waggr_id1;
    predicateUSetMap[&_aggr_id1]=&uaggr_id1;
    predicateFSetMap[&_aggr_id1]=&faggr_id1;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    predicateWSetMap[&_aggr_id2]=&waggr_id2;
    predicateUSetMap[&_aggr_id2]=&uaggr_id2;
    predicateFSetMap[&_aggr_id2]=&faggr_id2;
    stringToUniqueStringPointer["aggr_id2"] = &_aggr_id2;
    predicateWSetMap[&_aggr_id3]=&waggr_id3;
    predicateUSetMap[&_aggr_id3]=&uaggr_id3;
    predicateFSetMap[&_aggr_id3]=&faggr_id3;
    stringToUniqueStringPointer["aggr_id3"] = &_aggr_id3;
    predicateWSetMap[&_aggr_set0]=&waggr_set0;
    predicateUSetMap[&_aggr_set0]=&uaggr_set0;
    predicateFSetMap[&_aggr_set0]=&faggr_set0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    predicateWSetMap[&_aux1]=&waux1;
    predicateUSetMap[&_aux1]=&uaux1;
    predicateFSetMap[&_aux1]=&faux1;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    predicateWSetMap[&_body0]=&wbody0;
    predicateUSetMap[&_body0]=&ubody0;
    predicateFSetMap[&_body0]=&fbody0;
    stringToUniqueStringPointer["body0"] = &_body0;
    predicateWSetMap[&_body1]=&wbody1;
    predicateUSetMap[&_body1]=&ubody1;
    predicateFSetMap[&_body1]=&fbody1;
    stringToUniqueStringPointer["body1"] = &_body1;
    predicateWSetMap[&_body2]=&wbody2;
    predicateUSetMap[&_body2]=&ubody2;
    predicateFSetMap[&_body2]=&fbody2;
    stringToUniqueStringPointer["body2"] = &_body2;
    predicateWSetMap[&_diff]=&wdiff;
    predicateUSetMap[&_diff]=&udiff;
    predicateFSetMap[&_diff]=&fdiff;
    stringToUniqueStringPointer["diff"] = &_diff;
    predicateWSetMap[&_lives]=&wlives;
    predicateUSetMap[&_lives]=&ulives;
    predicateFSetMap[&_lives]=&flives;
    stringToUniqueStringPointer["lives"] = &_lives;
    predicateWSetMap[&_value]=&wvalue;
    predicateUSetMap[&_value]=&uvalue;
    predicateFSetMap[&_value]=&fvalue;
    stringToUniqueStringPointer["value"] = &_value;
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){
    if(tupleU->getWaspID() == 0){
        bool propagated=false;
        std::unordered_map<const std::string*,PredicateWSet*>::iterator falseSet = predicateFSetMap.find(tupleU->getPredicateName());
        std::unordered_map<const std::string*,PredicateWSet*>::iterator undefSet = predicateUSetMap.find(tupleU->getPredicateName());
        std::unordered_map<const std::string*,PredicateWSet*>::iterator trueSet = predicateWSetMap.find(tupleU->getPredicateName());
        if(falseSet==predicateFSetMap.end()){
            exit(180);
        }
        if(undefSet==predicateUSetMap.end()){
            exit(180);
        }
        if(trueSet==predicateWSetMap.end()){
            exit(180);
        }
        if(isNegated == asNegative){
            if(falseSet->second->find(*tupleU)!=NULL){
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                undefSet->second->erase(*tupleU);
                const auto& insertResult = trueSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));
                if (insertResult.second) {
                    insertTrue(insertResult);
                    propagated = true;
                }
            }
        }else{
            if(trueSet->second->find(*tupleU)!=NULL){
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                undefSet->second->erase(*tupleU);
                const auto& insertResult = falseSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));
                if (insertResult.second) {
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
        int sign = isNegated == asNegative ? -1 : 1;
        propagatedLiterals.insert(it*sign);
    }
    return false;
}
void Executor::printInternalLiterals(){
}
void Executor::unRollToLevel(int decisionLevel){
    for(unsigned i = 0; i<propagatedLiterals.size(); i++){
        int var = propagatedLiterals[i] > 0 ? propagatedLiterals[i] : -propagatedLiterals[i];
        int sign = propagatedLiterals[i] > 0 ? -1 : 1;
        Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
        if(literalNotPropagated!=NULL)
            reasonForLiteral.erase(sign*literalNotPropagated->getId());
    }
    propagatedLiterals.clear();
    while(currentDecisionLevel > decisionLevel){
        while(!levelToIntLiterals[currentDecisionLevel].empty()){
            int var = levelToIntLiterals[currentDecisionLevel].back();
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral.erase(var);
            int uVar = var>0 ? var : -var;
            Tuple* tuple = factory.getTupleFromInternalID(uVar);
            if (var > 0) {
                std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple->getPredicateName());
                if (wSetIt != predicateWSetMap.end()) {
                    wSetIt->second->erase(*tuple);
                }
            } //true removing
            if (var < 0) {
                std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
                if (fSetIt != predicateFSetMap.end()) {
                    fSetIt->second->erase(*tuple);
                }
            }//false removing
            std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple->getPredicateName());
            if (it == predicateUSetMap.end()) {
                } else {
                const auto& insertResult = it->second->insert(tuple);
                if (insertResult.second) {
                    insertUndef(insertResult);
                }
            } // close undef insert 
        }
        levelToIntLiterals.erase(currentDecisionLevel);
        currentDecisionLevel--;
    }
    clearConflictReason();
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts) {
    int decisionLevel = facts[0];
    currentDecisionLevel=decisionLevel;
    clearPropagations();
    std::vector<int> propagationStack;
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
        int factVar = facts[i]>0 ? facts[i] : -facts[i];
        int minus = facts[i]<0 ? -1 : 1;
        propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());
        if(propagatedLiterals.contains(-facts[i])) propagatedLiterals.erase(-facts[i]);
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
                const std::vector<const Tuple*>* tuples = &pbody2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody2_.getValues({});
                else if(tupleU->getPredicateName() == &_body2 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_aggr_id2);
                        const Tuple* tuple1 = waggr_id2.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaggr_id2.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                            if(tupleU == uaggr_id2.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_aggr_id3);
                            const Tuple* tuple2 = waggr_id3.find(*negativeTuple);
                            const Tuple* tupleUndef2 = uaggr_id3.find(*negativeTuple);
                            if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                                tuple2 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef2 != NULL){
                                tupleU = tuple2 = tupleUndef2;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id3 && tupleUNegated && tupleU==tupleUndef2){
                                tuple2=tupleU;
                            }else if(tuple2!=NULL){
                                tuple2=NULL;
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pvalue_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uvalue_.getValues({});
                else if(tupleU->getPredicateName() == &_value && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int X = tuple0->at(0);
                        const std::vector<const Tuple*>* tuples = &pvalue_.getValues({});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uvalue_.getValues({});
                        else if(tupleU->getPredicateName() == &_value && !tupleUNegated)
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
                                tuple1 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple1 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int Y = tuple1->at(0);
                                Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                                const Tuple* tuple2 = wlives.find(*negativeTuple);
                                const Tuple* tupleUndef2 = ulives.find(*negativeTuple);
                                if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                                    tuple2 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef2 != NULL){
                                    tupleU = tuple2 = tupleUndef2;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef2){
                                    tuple2=tupleU;
                                }else if(tuple2!=NULL){
                                    tuple2=NULL;
                                }
                                if(tuple2!=NULL){
                                    Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body2);
                                    const Tuple* tuple3 = wbody2.find(*negativeTuple);
                                    const Tuple* tupleUndef3 = ubody2.find(*negativeTuple);
                                    if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                        tuple3 = negativeTuple;
                                    else if(tupleU == NULL & tupleUndef3 != NULL){
                                        tupleU = tuple3 = tupleUndef3;
                                        tupleUNegated=true;
                                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body2 && tupleUNegated && tupleU==tupleUndef3){
                                        tuple3=tupleU;
                                    }else if(tuple3!=NULL){
                                        tuple3=NULL;
                                    }
                                    if(tuple3!=NULL){
                                        if(tupleU != NULL){
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                        }else{
                                            propagatedLiterals.insert(-1);
                                        }
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
                const std::vector<const Tuple*>* tuples = &pbody2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody2_.getValues({});
                else if(tupleU->getPredicateName() == &_body2 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple1 = wvalue.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody2_.getValues({});
                else if(tupleU->getPredicateName() == &_body2 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple1 = wvalue.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody2_.getValues({});
                else if(tupleU->getPredicateName() == &_body2 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({X,Y},&_lives);
                        const Tuple* tuple1 = wlives.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = ulives.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_lives && ! tupleUNegated){
                            if(tupleU == ulives.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_.getValues({});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_aggr_id1);
                        const Tuple* tuple1 = waggr_id1.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uaggr_id1.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id1 && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &plives_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_.getValues({});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int X = tuple0->at(0);
                        int Y = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple1 = wvalue.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                            const Tuple* tuple2 = wvalue.find(*positiveTuple);
                            if(tuple2 == tupleU && tupleU == NULL){
                                tuple2 = tupleU = uvalue.find(*positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                                if(tupleU == uvalue.find(*positiveTuple)){
                                    tuple2=tupleU;
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body1);
                                const Tuple* tuple3 = wbody1.find(*negativeTuple);
                                const Tuple* tupleUndef3 = ubody1.find(*negativeTuple);
                                if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                    tuple3 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef3 != NULL){
                                    tupleU = tuple3 = tupleUndef3;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body1 && tupleUNegated && tupleU==tupleUndef3){
                                    tuple3=tupleU;
                                }else if(tuple3!=NULL){
                                    tuple3=NULL;
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                    }else{
                                        propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_.getValues({});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple1 = wvalue.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_.getValues({});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple1 = wvalue.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_.getValues({});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                        const Tuple* tuple1 = wlives.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValues({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_aggr_id0);
                        const Tuple* tuple1 = waggr_id0.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaggr_id0.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0 && ! tupleUNegated){
                            if(tupleU == uaggr_id0.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &plives_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_.getValues({});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int XDX = tuple0->at(0);
                        int YDY = tuple0->at(1);
                        const std::vector<const Tuple*>* tuples = &pdiff_.getValues({});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &udiff_.getValues({});
                        else if(tupleU->getPredicateName() == &_diff && !tupleUNegated)
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
                                tuple1 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple1 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int DX = tuple1->at(0);
                                int DY = tuple1->at(1);
                                int X = XDX - DX;
                                int Y = YDY - DY;
                                Tuple* negativeTuple = factory.addNewInternalTuple({DX,DY,Y,X,XDX,YDY},&_aux1);
                                const Tuple* tuple4 = waux1.find(*negativeTuple);
                                const Tuple* tupleUndef4 = uaux1.find(*negativeTuple);
                                if(tuple4 == tupleUndef4 && tupleUndef4 == NULL)
                                    tuple4 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef4 != NULL){
                                    tupleU = tuple4 = tupleUndef4;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux1 && tupleUNegated && tupleU==tupleUndef4){
                                    tuple4=tupleU;
                                }else if(tuple4!=NULL){
                                    tuple4=NULL;
                                }
                                if(tuple4!=NULL){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                    }else{
                                        propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &paux1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_.getValues({});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int DX = tuple0->at(0);
                        int DY = tuple0->at(1);
                        int Y = tuple0->at(2);
                        int X = tuple0->at(3);
                        int XDX = tuple0->at(4);
                        int YDY = tuple0->at(5);
                        Tuple* negativeTuple = factory.addNewInternalTuple({DX,DY},&_diff);
                        const Tuple* tuple1 = wdiff.find(*negativeTuple);
                        const Tuple* tupleUndef1 = udiff.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_diff && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &paux1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_.getValues({});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int DX = tuple0->at(0);
                        int DY = tuple0->at(1);
                        int Y = tuple0->at(2);
                        int X = tuple0->at(3);
                        int XDX = tuple0->at(4);
                        int YDY = tuple0->at(5);
                        Tuple* negativeTuple = factory.addNewInternalTuple({XDX,YDY},&_lives);
                        const Tuple* tuple1 = wlives.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &plives_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_.getValues({});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int X = tuple0->at(0);
                        int Y = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple1 = wvalue.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                            const Tuple* tuple2 = wvalue.find(*positiveTuple);
                            if(tuple2 == tupleU && tupleU == NULL){
                                tuple2 = tupleU = uvalue.find(*positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                                if(tupleU == uvalue.find(*positiveTuple)){
                                    tuple2=tupleU;
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body0);
                                const Tuple* tuple3 = wbody0.find(*negativeTuple);
                                const Tuple* tupleUndef3 = ubody0.find(*negativeTuple);
                                if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                    tuple3 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef3 != NULL){
                                    tupleU = tuple3 = tupleUndef3;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body0 && tupleUNegated && tupleU==tupleUndef3){
                                    tuple3=tupleU;
                                }else if(tuple3!=NULL){
                                    tuple3=NULL;
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                    }else{
                                        propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValues({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple1 = wvalue.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValues({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple1 = wvalue.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
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
                const std::vector<const Tuple*>* tuples = &pbody0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValues({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                        const Tuple* tuple1 = wlives.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                propagatedLiterals.insert(-1);
                            }
                        }
                    }
                }
            }
        }
        {
            const std::vector<const Tuple*>* trueHeads = &paggr_set0_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = trueHeads->at(i);
                int DX = head->at(0);
                int DY = head->at(1);
                int Y = head->at(2);
                int X = head->at(3);
                const std::vector<const Tuple*>* tuples = &paux1_0_1_2_3_.getValues({DX,DY,Y,X});
                const std::vector<const Tuple*>* tuplesU = &uaux1_0_1_2_3_.getValues({DX,DY,Y,X});
                if(tuples->size() == 0){
                    if(tuplesU->size() == 0){
                        propagatedLiterals.insert(-1);
                    }else if(tuplesU->size() == 1){
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }else{
                }
            }
            const std::vector<const Tuple*>* undefHeads = &uaggr_set0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = undefHeads->at(i);
                int DX = head->at(0);
                int DY = head->at(1);
                int Y = head->at(2);
                int X = head->at(3);
                const std::vector<const Tuple*>* tuples = &paux1_0_1_2_3_.getValues({DX,DY,Y,X});
                if(tuples->size() == 0){
                    const std::vector<const Tuple*>* tuplesU = &uaux1_0_1_2_3_.getValues({DX,DY,Y,X});
                    if(tuplesU->size() == 0){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals);
                }
            }
            const std::vector<const Tuple*>* falseHeads = &faggr_set0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = falseHeads->at(i);
                int DX = head->at(0);
                int DY = head->at(1);
                int Y = head->at(2);
                int X = head->at(3);
                const std::vector<const Tuple*>* tuples = &paux1_0_1_2_3_.getValues({DX,DY,Y,X});
                if(tuples->size() == 0){
                    const std::vector<const Tuple*>* tuplesU = &uaux1_0_1_2_3_.getValues({DX,DY,Y,X});
                    for(unsigned j = 0; j < tuplesU->size();){
                        propUndefined(tuplesU->at(j),false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propagatedLiterals.insert(-1);
                }
            }
        }
        {
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 3+1){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 3+1 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 2){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 2){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 2){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 2 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<const Tuple*>* tuples = &paggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id2_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 3){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 3){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 3){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 3 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 3){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 3){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<const Tuple*>* tuples = &paggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id3_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 3+1){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 3+1 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
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
        starter.setNegated(startVar<0);
        std::string minus = starter.isNegated() ? "not " : "";
        propagationStack.pop_back();
        {
            if(starter.getPredicateName() == &_lives && starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body0);
                const Tuple* tuple1 = wbody0.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody0.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                    if(tupleU == ubody0.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                const Tuple* tuple1 = wlives.find(*negativeTuple);
                const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_value && starter.isNegated()){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody0_1_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_1_.getValues({X});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(0);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({X},&_value);
                const Tuple* tuple1 = wvalue.find(*negativeTuple);
                const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_value && starter.isNegated()){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody0_0_.getValues({Y});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_0_.getValues({Y});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(1);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({Y},&_value);
                const Tuple* tuple1 = wvalue.find(*negativeTuple);
                const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_body0 && starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({X,Y},&_lives);
                const Tuple* tuple1 = wlives.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ulives.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_lives && ! tupleUNegated){
                    if(tupleU == ulives.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                    const Tuple* tuple2 = wvalue.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uvalue.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                        if(tupleU == uvalue.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple3 = wvalue.find(*positiveTuple);
                        if(tuple3 == tupleU && tupleU == NULL){
                            tuple3 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple3=tupleU;
                            }
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_value && !starter.isNegated()){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &plives_1_.getValues({Y});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_1_.getValues({Y});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple2 = wvalue.find(*positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body0);
                            const Tuple* tuple3 = wbody0.find(*negativeTuple);
                            const Tuple* tupleUndef3 = ubody0.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body0 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple1!=tupleU){
                                            int it = tuple1->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_value && !starter.isNegated()){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &plives_0_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_0_.getValues({X});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple2 = wvalue.find(*positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body0);
                            const Tuple* tuple3 = wbody0.find(*negativeTuple);
                            const Tuple* tupleUndef3 = ubody0.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body0 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple1!=tupleU){
                                            int it = tuple1->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_lives && !starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                const Tuple* tuple1 = wvalue.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uvalue.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                    if(tupleU == uvalue.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                    const Tuple* tuple2 = wvalue.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uvalue.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                        if(tupleU == uvalue.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body0);
                        const Tuple* tuple3 = wbody0.find(*negativeTuple);
                        const Tuple* tupleUndef3 = ubody0.find(*negativeTuple);
                        if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                            tuple3 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef3 != NULL){
                            tupleU = tuple3 = tupleUndef3;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body0 && tupleUNegated && tupleU==tupleUndef3){
                            tuple3=tupleU;
                        }else if(tuple3!=NULL){
                            tuple3=NULL;
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_set0){
            int DX = starter[0];
            int DY = starter[1];
            int Y = starter[2];
            int X = starter[3];
            const std::vector<const Tuple*>* tuples = &paux1_0_1_2_3_.getValues({DX,DY,Y,X});
            const std::vector<const Tuple*>* tuplesU = &uaux1_0_1_2_3_.getValues({DX,DY,Y,X});
            if(!starter.isNegated()){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    int itProp = tuplesU->at(0)->getId();
                    if(reasonForLiteral.count(itProp) == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i)->getId();
                            reasonForLiteral[itProp].insert(-it);
                        }
                        reasonForLiteral[itProp].insert(startVar);
                    }
                    propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                }
            }else{
                if(tuples->size()>0){
                    int it = tuples->at(0)->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        int it = tuplesU->back()->getId();
                        if(reasonForLiteral.count(-it) == 0 )
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux1){
            int DX = starter[0];
            int DY = starter[1];
            int Y = starter[2];
            int X = starter[3];
            int XDX = starter[4];
            int YDY = starter[5];
            if(!starter.isNegated()){
                Tuple* head = factory.addNewInternalTuple({DX,DY,Y,X}, &_aggr_set0);
                const Tuple* tupleU = uaggr_set0.find(*head);
                if(waggr_set0.find(*head) == tupleU && tupleU==NULL){
                    int it = head->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it);
                    return;
                }else if(tupleU != NULL){
                    int it = head->getId();
                    if(reasonForLiteral.count(it) == 0 )
                        reasonForLiteral[it].insert(startVar);
                    propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                }
            }else{
                Tuple* head = factory.addNewInternalTuple({DX,DY,Y,X}, &_aggr_set0);
                const std::vector<const Tuple*>* tuples = &paux1_0_1_2_3_.getValues({DX,DY,Y,X});
                const std::vector<const Tuple*>* tuplesU = &uaux1_0_1_2_3_.getValues({DX,DY,Y,X});
                if(waggr_set0.find(*head) != NULL){
                    if(tuples->size()==0 && tuplesU->size()==0){
                        int itHead = head->getId();
                        const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i)->getId();
                            reasonForLiteral[-itHead].insert(-it);
                        }
                        handleConflict(-itHead);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int it = head->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }else{
                    const Tuple* tupleU = uaggr_set0.find(*head);
                    if(tupleU != NULL && tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        if(reasonForLiteral.count(-itHead) == 0 ){
                            const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[-itHead].insert(-it);
                            }
                        }
                        propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_set0){
            int DX = starter[0];
            int DY = starter[1];
            int Y = starter[2];
            int X = starter[3];
            const std::vector<const Tuple*>* tuples = &paux1_0_1_2_3_.getValues({DX,DY,Y,X});
            const std::vector<const Tuple*>* tuplesU = &uaux1_0_1_2_3_.getValues({DX,DY,Y,X});
            if(!starter.isNegated()){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    int itProp = tuplesU->at(0)->getId();
                    if(reasonForLiteral.count(itProp) == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux1_0_1_2_3_.getValues({DX,DY,Y,X});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i)->getId();
                            reasonForLiteral[itProp].insert(-it);
                        }
                        reasonForLiteral[itProp].insert(startVar);
                    }
                    propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                }
            }else{
                if(tuples->size()>0){
                    int it = tuples->at(0)->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        int it = tuplesU->back()->getId();
                        if(reasonForLiteral.count(-it) == 0 )
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }
        }//close if starter
        {
            if(starter.getPredicateName() == &_lives && starter.isNegated()){
                int XDX = starter[0];
                int YDY = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paux1_4_5_.getValues({XDX,YDY});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_4_5_.getValues({XDX,YDY});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(4) == XDX && tupleU->at(5) == YDY)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int DX = tuple1->at(0);
                        int DY = tuple1->at(1);
                        int Y = tuple1->at(2);
                        int X = tuple1->at(3);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aux1 && !starter.isNegated()){
                int DX = starter[0];
                int DY = starter[1];
                int Y = starter[2];
                int X = starter[3];
                int XDX = starter[4];
                int YDY = starter[5];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({XDX,YDY},&_lives);
                const Tuple* tuple1 = wlives.find(*negativeTuple);
                const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_diff && starter.isNegated()){
                int DX = starter[0];
                int DY = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paux1_0_1_.getValues({DX,DY});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_0_1_.getValues({DX,DY});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == DX && tupleU->at(1) == DY)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(2);
                        int X = tuple1->at(3);
                        int XDX = tuple1->at(4);
                        int YDY = tuple1->at(5);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aux1 && !starter.isNegated()){
                int DX = starter[0];
                int DY = starter[1];
                int Y = starter[2];
                int X = starter[3];
                int XDX = starter[4];
                int YDY = starter[5];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({DX,DY},&_diff);
                const Tuple* tuple1 = wdiff.find(*negativeTuple);
                const Tuple* tupleUndef1 = udiff.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_diff && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aux1 && starter.isNegated()){
                int DX = starter[0];
                int DY = starter[1];
                int Y = starter[2];
                int X = starter[3];
                int XDX = starter[4];
                int YDY = starter[5];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                if(XDX == X + DX){
                    if(YDY == Y + DY){
                        Tuple* positiveTuple = factory.addNewInternalTuple({XDX,YDY},&_lives);
                        const Tuple* tuple3 = wlives.find(*positiveTuple);
                        if(tuple3 == tupleU && tupleU == NULL){
                            tuple3 = tupleU = ulives.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_lives && ! tupleUNegated){
                            if(tupleU == ulives.find(*positiveTuple)){
                                tuple3=tupleU;
                            }
                        }
                        if(tuple3!=NULL){
                            Tuple* positiveTuple = factory.addNewInternalTuple({DX,DY},&_diff);
                            const Tuple* tuple4 = wdiff.find(*positiveTuple);
                            if(tuple4 == tupleU && tupleU == NULL){
                                tuple4 = tupleU = udiff.find(*positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple4==NULL && tupleU->getPredicateName() == &_diff && ! tupleUNegated){
                                if(tupleU == udiff.find(*positiveTuple)){
                                    tuple4=tupleU;
                                }
                            }
                            if(tuple4!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple4!=tupleU){
                                            int it = tuple4->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple4!=NULL){
                                        int it = tuple4->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_diff && !starter.isNegated()){
                int DX = starter[0];
                int DY = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &plives_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_.getValues({});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int XDX = tuple1->at(0);
                        int YDY = tuple1->at(1);
                        int X = XDX - DX;
                        int Y = YDY - DY;
                        Tuple* negativeTuple = factory.addNewInternalTuple({DX,DY,Y,X,XDX,YDY},&_aux1);
                        const Tuple* tuple4 = waux1.find(*negativeTuple);
                        const Tuple* tupleUndef4 = uaux1.find(*negativeTuple);
                        if(tuple4 == tupleUndef4 && tupleUndef4 == NULL)
                            tuple4 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef4 != NULL){
                            tupleU = tuple4 = tupleUndef4;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux1 && tupleUNegated && tupleU==tupleUndef4){
                            tuple4=tupleU;
                        }else if(tuple4!=NULL){
                            tuple4=NULL;
                        }
                        if(tuple4!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple4!=tupleU){
                                        int it = tuple4->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple4!=NULL){
                                    int it = tuple4->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_lives && !starter.isNegated()){
                int XDX = starter[0];
                int YDY = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pdiff_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &udiff_.getValues({});
                else if(tupleU->getPredicateName() == &_diff && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int DX = tuple1->at(0);
                        int DY = tuple1->at(1);
                        int X = XDX - DX;
                        int Y = YDY - DY;
                        Tuple* negativeTuple = factory.addNewInternalTuple({DX,DY,Y,X,XDX,YDY},&_aux1);
                        const Tuple* tuple4 = waux1.find(*negativeTuple);
                        const Tuple* tupleUndef4 = uaux1.find(*negativeTuple);
                        if(tuple4 == tupleUndef4 && tupleUndef4 == NULL)
                            tuple4 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef4 != NULL){
                            tupleU = tuple4 = tupleUndef4;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux1 && tupleUNegated && tupleU==tupleUndef4){
                            tuple4=tupleU;
                        }else if(tuple4!=NULL){
                            tuple4=NULL;
                        }
                        if(tuple4!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple4!=tupleU){
                                        int it = tuple4->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple4!=NULL){
                                    int it = tuple4->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            int Y = starter[0];
            int X = starter[1];
            std::vector<int> sharedVar({starter[0],starter[1]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_2_3_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=3+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 3+1 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 3+1){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 3+1){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 3+1){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 3+1 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id0 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body0);
                const Tuple* tuple1 = wbody0.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody0.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                    if(tupleU == ubody0.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_aggr_id0);
                const Tuple* tuple1 = waggr_id0.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_id0.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0 && ! tupleUNegated){
                    if(tupleU == uaggr_id0.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_lives && starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body1);
                const Tuple* tuple1 = wbody1.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody1.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body1 && ! tupleUNegated){
                    if(tupleU == ubody1.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_body1 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                const Tuple* tuple1 = wlives.find(*negativeTuple);
                const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_value && starter.isNegated()){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody1_1_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_1_.getValues({X});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(0);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body1 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({X},&_value);
                const Tuple* tuple1 = wvalue.find(*negativeTuple);
                const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_value && starter.isNegated()){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody1_0_.getValues({Y});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_0_.getValues({Y});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(1);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body1 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({Y},&_value);
                const Tuple* tuple1 = wvalue.find(*negativeTuple);
                const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_body1 && starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({X,Y},&_lives);
                const Tuple* tuple1 = wlives.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ulives.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_lives && ! tupleUNegated){
                    if(tupleU == ulives.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                    const Tuple* tuple2 = wvalue.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uvalue.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                        if(tupleU == uvalue.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple3 = wvalue.find(*positiveTuple);
                        if(tuple3 == tupleU && tupleU == NULL){
                            tuple3 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple3=tupleU;
                            }
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_value && !starter.isNegated()){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &plives_1_.getValues({Y});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_1_.getValues({Y});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                        const Tuple* tuple2 = wvalue.find(*positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body1);
                            const Tuple* tuple3 = wbody1.find(*negativeTuple);
                            const Tuple* tupleUndef3 = ubody1.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body1 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple1!=tupleU){
                                            int it = tuple1->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_value && !starter.isNegated()){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &plives_0_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulives_0_.getValues({X});
                else if(tupleU->getPredicateName() == &_lives && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple2 = wvalue.find(*positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body1);
                            const Tuple* tuple3 = wbody1.find(*negativeTuple);
                            const Tuple* tupleUndef3 = ubody1.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body1 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple1!=tupleU){
                                            int it = tuple1->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_lives && !starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                const Tuple* tuple1 = wvalue.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uvalue.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                    if(tupleU == uvalue.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                    const Tuple* tuple2 = wvalue.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uvalue.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                        if(tupleU == uvalue.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body1);
                        const Tuple* tuple3 = wbody1.find(*negativeTuple);
                        const Tuple* tupleUndef3 = ubody1.find(*negativeTuple);
                        if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                            tuple3 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef3 != NULL){
                            tupleU = tuple3 = tupleUndef3;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body1 && tupleUNegated && tupleU==tupleUndef3){
                            tuple3=tupleU;
                        }else if(tuple3!=NULL){
                            tuple3=NULL;
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id1){
            int Y = starter[0];
            int X = starter[1];
            std::vector<int> sharedVar({starter[0],starter[1]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_2_3_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=2){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 2 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 2){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 2){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 2){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 2){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 2 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id1 && starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body1);
                const Tuple* tuple1 = wbody1.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody1.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body1 && ! tupleUNegated){
                    if(tupleU == ubody1.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_body1 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_aggr_id1);
                const Tuple* tuple1 = waggr_id1.find(*negativeTuple);
                const Tuple* tupleUndef1 = uaggr_id1.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id1 && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_lives && !starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body2);
                const Tuple* tuple1 = wbody2.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody2.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body2 && ! tupleUNegated){
                    if(tupleU == ubody2.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_body2 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({X,Y},&_lives);
                const Tuple* tuple1 = wlives.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ulives.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_lives && ! tupleUNegated){
                    if(tupleU == ulives.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_value && starter.isNegated()){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody2_1_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody2_1_.getValues({X});
                else if(tupleU->getPredicateName() == &_body2 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(0);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body2 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({X},&_value);
                const Tuple* tuple1 = wvalue.find(*negativeTuple);
                const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_value && starter.isNegated()){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody2_0_.getValues({Y});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody2_0_.getValues({Y});
                else if(tupleU->getPredicateName() == &_body2 && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == Y)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(1);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body2 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({Y},&_value);
                const Tuple* tuple1 = wvalue.find(*negativeTuple);
                const Tuple* tupleUndef1 = uvalue.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_value && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_body2 && starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                const Tuple* tuple1 = wlives.find(*negativeTuple);
                const Tuple* tupleUndef1 = ulives.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                    const Tuple* tuple2 = wvalue.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uvalue.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                        if(tupleU == uvalue.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                        const Tuple* tuple3 = wvalue.find(*positiveTuple);
                        if(tuple3 == tupleU && tupleU == NULL){
                            tuple3 = tupleU = uvalue.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                            if(tupleU == uvalue.find(*positiveTuple)){
                                tuple3=tupleU;
                            }
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_value && !starter.isNegated()){
                int Y = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pvalue_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uvalue_.getValues({});
                else if(tupleU->getPredicateName() == &_value && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(0);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                        const Tuple* tuple2 = wlives.find(*negativeTuple);
                        const Tuple* tupleUndef2 = ulives.find(*negativeTuple);
                        if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                            tuple2 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef2 != NULL){
                            tupleU = tuple2 = tupleUndef2;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef2){
                            tuple2=tupleU;
                        }else if(tuple2!=NULL){
                            tuple2=NULL;
                        }
                        if(tuple2!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body2);
                            const Tuple* tuple3 = wbody2.find(*negativeTuple);
                            const Tuple* tupleUndef3 = ubody2.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body2 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple1!=tupleU){
                                            int it = tuple1->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_value && !starter.isNegated()){
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pvalue_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uvalue_.getValues({});
                else if(tupleU->getPredicateName() == &_value && !tupleUNegated)
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Y = tuple1->at(0);
                        Tuple* negativeTuple = factory.addNewInternalTuple({X,Y},&_lives);
                        const Tuple* tuple2 = wlives.find(*negativeTuple);
                        const Tuple* tupleUndef2 = ulives.find(*negativeTuple);
                        if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                            tuple2 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef2 != NULL){
                            tupleU = tuple2 = tupleUndef2;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_lives && tupleUNegated && tupleU==tupleUndef2){
                            tuple2=tupleU;
                        }else if(tuple2!=NULL){
                            tuple2=NULL;
                        }
                        if(tuple2!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body2);
                            const Tuple* tuple3 = wbody2.find(*negativeTuple);
                            const Tuple* tupleUndef3 = ubody2.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body2 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            int it = starter.getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple1!=tupleU){
                                            int it = tuple1->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_lives && starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({X},&_value);
                const Tuple* tuple1 = wvalue.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uvalue.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                    if(tupleU == uvalue.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({Y},&_value);
                    const Tuple* tuple2 = wvalue.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uvalue.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_value && ! tupleUNegated){
                        if(tupleU == uvalue.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_body2);
                        const Tuple* tuple3 = wbody2.find(*negativeTuple);
                        const Tuple* tupleUndef3 = ubody2.find(*negativeTuple);
                        if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                            tuple3 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef3 != NULL){
                            tupleU = tuple3 = tupleUndef3;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_body2 && tupleUNegated && tupleU==tupleUndef3){
                            tuple3=tupleU;
                        }else if(tuple3!=NULL){
                            tuple3=NULL;
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id2){
            int Y = starter[0];
            int X = starter[1];
            std::vector<int> sharedVar({starter[0],starter[1]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_2_3_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=3){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 3 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 3){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 3){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id2_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 3){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 3){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 3){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 3 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 3){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 3){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        if(starter.getPredicateName() == &_aggr_id3){
            int Y = starter[0];
            int X = starter[1];
            std::vector<int> sharedVar({starter[0],starter[1]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_2_3_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=3+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 3+1 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 3+1){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 3+1){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id3_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int X = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 3+1){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int Y = tuplesF->at(i)->at(0);
                int X = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 3+1 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int Y = tuplesU->at(i)->at(0);
                int X = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(1)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_2_3_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_2_3_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 3+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_2_3_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id3 && starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body2);
                const Tuple* tuple1 = wbody2.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody2.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body2 && ! tupleUNegated){
                    if(tupleU == ubody2.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_aggr_id2);
                    const Tuple* tuple2 = waggr_id2.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uaggr_id2.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                        if(tupleU == uaggr_id2.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aggr_id2 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_body2);
                const Tuple* tuple1 = wbody2.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody2.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body2 && ! tupleUNegated){
                    if(tupleU == ubody2.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_aggr_id3);
                    const Tuple* tuple2 = waggr_id3.find(*negativeTuple);
                    const Tuple* tupleUndef2 = uaggr_id3.find(*negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id3 && tupleUNegated && tupleU==tupleUndef2){
                        tuple2=tupleU;
                    }else if(tuple2!=NULL){
                        tuple2=NULL;
                    }
                    if(tuple2!=NULL){
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*-1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body2 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({Y,X},&_aggr_id2);
                const Tuple* tuple1 = waggr_id2.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_id2.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                    if(tupleU == uaggr_id2.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* negativeTuple = factory.addNewInternalTuple({Y,X},&_aggr_id3);
                    const Tuple* tuple2 = waggr_id3.find(*negativeTuple);
                    const Tuple* tupleUndef2 = uaggr_id3.find(*negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id3 && tupleUNegated && tupleU==tupleUndef2){
                        tuple2=tupleU;
                    }else if(tuple2!=NULL){
                        tuple2=NULL;
                    }
                    if(tuple2!=NULL){
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*-1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
        }
    }
}
}
