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

typedef TupleWithReasons Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<Tuple,S> ;
typedef std::vector<const Tuple* > Tuples;
using PredicateWSet = SmartPredicateSet;

std::unordered_map<const std::string*, PredicateWSet*> predicateWSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateFSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateUSetMap;
const std::string _a = "a";
PredicateWSet wa(2);
PredicateWSet ua(2);
PredicateWSet fa(2);
const std::string _aggr_id0 = "aggr_id0";
PredicateWSet waggr_id0(0);
PredicateWSet uaggr_id0(0);
PredicateWSet faggr_id0(0);
const std::string _aggr_set0 = "aggr_set0";
PredicateWSet waggr_set0(2);
PredicateWSet uaggr_set0(2);
PredicateWSet faggr_set0(2);
const std::string _aux0 = "aux0";
PredicateWSet waux0(3);
PredicateWSet uaux0(3);
PredicateWSet faux0(3);
const std::string _b = "b";
PredicateWSet wb(1);
PredicateWSet ub(1);
PredicateWSet fb(1);
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
typedef void (*ExplainNegative)(const std::vector<int> & lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output);

TupleFactory factory;
std::unordered_map<const std::string*, ExplainNegative> explainNegativeFunctionsMap;

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
void explainNegativeLiteral(const Tuple * lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output) {
    explainNegativeFunctionsMap[lit->getPredicateName()](*lit, open_set, output);
}

AuxMap<0> pa_({});
AuxMap<0> ua_({});
AuxMap<0> fa_({});
AuxMap<0> pb_({});
AuxMap<0> ub_({});
AuxMap<0> fb_({});
AuxMap<64> paux0_0_1_({0,1});
AuxMap<64> uaux0_0_1_({0,1});
AuxMap<64> faux0_0_1_({0,1});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<32> paux0_2_({2});
AuxMap<32> uaux0_2_({2});
AuxMap<32> faux0_2_({2});
AuxMap<32> paux0_1_({1});
AuxMap<32> uaux0_1_({1});
AuxMap<32> faux0_1_({1});
AuxMap<32> pa_1_({1});
AuxMap<32> ua_1_({1});
AuxMap<32> fa_1_({1});
AuxMap<1> paggr_id0_({});
AuxMap<1> uaggr_id0_({});
AuxMap<1> faggr_id0_({});
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
void explainPositiveLiteral(const Tuple * tuple, std::unordered_set<std::string> & open_set, std::vector<const Tuple*> & outputReasons) {
    const std::vector<const Tuple*> & tupleReasons = tuple->getPositiveReasons();
     if (tupleReasons.empty()) {
        outputReasons.push_back(tuple);
    }
    else {
        for (const Tuple * reason : tupleReasons) {
            explainPositiveLiteral(reason, open_set, outputReasons);
        }
    }
    for (const Tuple & reason : tuple->getNegativeReasons()) {
        explainNegativeLiteral(&reason, open_set, outputReasons);
    }
}

aspc::Literal tupleToLiteral(const Tuple & tuple) {
    aspc::Literal literal(*tuple.getPredicateName(), tuple.isNegated());
    for (int v : tuple) {
        literal.addTerm(ConstantsManager::getInstance().unmapConstant(v));
    }
    return literal;
}
void printTuples(const std::string & predicateName, const Tuples & tuples) {
    for (const std::vector<int> * tuple : tuples) {
        std::cout <<predicateName<< "(";
        for (unsigned i = 0; i < tuple->size(); i++) {
            if (i > 0) {
                std::cout << ",";
            }
            std::cout << ConstantsManager::getInstance().unmapConstant((*tuple)[i]);
        }
        std::cout << ").\n";
    }
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

inline void insertFalse(std::pair<const TupleWithReasons *, bool> insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2(*insertResult.first);
        faux0_0_1_.insert2(*insertResult.first);
        faux0_1_.insert2(*insertResult.first);
        faux0_2_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_b){
        fb_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_a){
        fa_.insert2(*insertResult.first);
        fa_1_.insert2(*insertResult.first);
    }
}
inline void insertTrue(std::pair<const TupleWithReasons *, bool> insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2(*insertResult.first);
        paux0_0_1_.insert2(*insertResult.first);
        paux0_1_.insert2(*insertResult.first);
        paux0_2_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_b){
        pb_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_a){
        pa_.insert2(*insertResult.first);
        pa_1_.insert2(*insertResult.first);
    }
}
inline void insertUndef(std::pair<const TupleWithReasons *, bool> insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2(*insertResult.first);
        uaux0_0_1_.insert2(*insertResult.first);
        uaux0_1_.insert2(*insertResult.first);
        uaux0_2_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_b){
        ub_.insert2(*insertResult.first);
    }
    if(insertResult.first->getPredicateName() == &_a){
        ua_.insert2(*insertResult.first);
        ua_1_.insert2(*insertResult.first);
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
        const std::vector<const Tuple*>* tuples = &pa_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ua_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int V = tuple->at(0);
            int W = tuple->at(1);
            if(W >= V){
                Tuple* boundTuple = factory.addNewInternalTuple({W,W}, &_a);
                if(wa.find(*boundTuple)==NULL){
                    const std::vector<const Tuple*>* tuples = &pb_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &ub_.getValues({});
                    for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                        const Tuple* tuple = NULL;
                        if(i<tuples->size())
                            tuple=tuples->at(i);
                        else
                            tuple=tuplesU->at(i-tuples->size());
                        int U = tuple->at(0);
                        if(W >= U){
                            Tuple* aux = factory.addNewInternalTuple({V,W,U}, &_aux0);
                            if(uaux0.find(*aux) == NULL){
                                const auto& insertResult = uaux0.insert(aux);
                                if (insertResult.second) {
                                    insertUndef(insertResult);
                                    {
                                        Tuple* head = factory.addNewInternalTuple({V,W},&_aggr_set0);
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
            }
        }
    }
    {
        Tuple* aggrId = factory.addNewInternalTuple({},&_aggr_id0);
        const auto& insertResult = uaggr_id0.insert(aggrId);
        if (insertResult.second) {
            insertUndef(insertResult);
        }
    }
    {
        const std::vector<const Tuple*>* aggregateIds = &uaggr_id0_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i)->getId();
            const std::vector<const Tuple*>* aggrSetTuples = &uaggr_set0_.getValues({});
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possibleSum[it]+=aggrSetTuples->at(j)->at(0);
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
    waggr_set0.clear();
    paggr_id0_.clear();
    paggr_set0_.clear();
    faggr_id0_.clear();
    faggr_set0_.clear();
}
void Executor::init() {
    predicateWSetMap[&_a]=&wa;
    predicateUSetMap[&_a]=&ua;
    predicateFSetMap[&_a]=&fa;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_aggr_id0]=&waggr_id0;
    predicateUSetMap[&_aggr_id0]=&uaggr_id0;
    predicateFSetMap[&_aggr_id0]=&faggr_id0;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    predicateWSetMap[&_aggr_set0]=&waggr_set0;
    predicateUSetMap[&_aggr_set0]=&uaggr_set0;
    predicateFSetMap[&_aggr_set0]=&faggr_set0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    predicateWSetMap[&_aux0]=&waux0;
    predicateUSetMap[&_aux0]=&uaux0;
    predicateFSetMap[&_aux0]=&faux0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    predicateFSetMap[&_b]=&fb;
    stringToUniqueStringPointer["b"] = &_b;
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
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        int itAggrId = factory.addNewInternalTuple({},&_aggr_id0)->getId();
                        actualSum[itAggrId]+=tupleU->at(0);
                        possibleSum[itAggrId]-=tupleU->at(0);
                    }
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
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        int itAggrId = factory.addNewInternalTuple({},&_aggr_id0)->getId();
                        possibleSum[itAggrId]-=tupleU->at(0);
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
            if(tuple->getPredicateName() == &_aggr_set0){
                int itAggrId = factory.addNewInternalTuple({},&_aggr_id0)->getId();
                if(var>0)
                    actualSum[itAggrId]-=tuple->at(0);
                possibleSum[itAggrId]+=tuple->at(0);
            }
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
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 2+1){
                    propagatedLiterals.insert(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= 2+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(actualSum[aggrIdIt] >= 2+1){
                    propagatedLiterals.insert(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= 2+1){
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
                            propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(actualSum[aggrIdIt] >= 2+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 2+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
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
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({},&_aggr_id0);
                const Tuple* tuple0 = waggr_id0.find(*negativeTuple);
                const Tuple* tupleUndef0 = uaggr_id0.find(*negativeTuple);
                if(tuple0 == tupleUndef0 && tupleUndef0 == NULL)
                    tuple0 = negativeTuple;
                else if(tupleU == NULL & tupleUndef0 != NULL){
                    tupleU = tuple0 = tupleUndef0;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id0 && tupleUNegated && tupleU==tupleUndef0){
                    tuple0=tupleU;
                }else if(tuple0!=NULL){
                    tuple0=NULL;
                }
                if(tuple0!=NULL){
                    if(tupleU != NULL){
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        propagatedLiterals.insert(-1);
                    }
                }
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pa_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ua_.getValues({});
                else if(tupleU->getPredicateName() == &_a && !tupleUNegated)
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
                        int V = tuple0->at(0);
                        int W = tuple0->at(1);
                        if(W >= V){
                            Tuple* negativeTuple = factory.addNewInternalTuple({W,W},&_a);
                            const Tuple* tuple2 = wa.find(*negativeTuple);
                            const Tuple* tupleUndef2 = ua.find(*negativeTuple);
                            if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                                tuple2 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef2 != NULL){
                                tupleU = tuple2 = tupleUndef2;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef2){
                                tuple2=tupleU;
                            }else if(tuple2!=NULL){
                                tuple2=NULL;
                            }
                            if(tuple2!=NULL){
                                const std::vector<const Tuple*>* tuples = &pb_.getValues({});
                                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ub_.getValues({});
                                else if(tupleU->getPredicateName() == &_b && !tupleUNegated)
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
                                    const Tuple* tuple3 = NULL;
                                    if(i<tuples->size())
                                        tuple3 = tuples->at(i);
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int U = tuple3->at(0);
                                        if(W >= U){
                                            Tuple* negativeTuple = factory.addNewInternalTuple({V,W,U},&_aux0);
                                            const Tuple* tuple5 = waux0.find(*negativeTuple);
                                            const Tuple* tupleUndef5 = uaux0.find(*negativeTuple);
                                            if(tuple5 == tupleUndef5 && tupleUndef5 == NULL)
                                                tuple5 = negativeTuple;
                                            else if(tupleU == NULL & tupleUndef5 != NULL){
                                                tupleU = tuple5 = tupleUndef5;
                                                tupleUNegated=true;
                                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef5){
                                                tuple5=tupleU;
                                            }else if(tuple5!=NULL){
                                                tuple5=NULL;
                                            }
                                            if(tuple5!=NULL){
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
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int V = tuple0->at(0);
                        int W = tuple0->at(1);
                        int U = tuple0->at(2);
                        Tuple* positiveTuple = factory.addNewInternalTuple({W,W},&_a);
                        const Tuple* tuple1 = wa.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = ua.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                            if(tupleU == ua.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int V = tuple0->at(0);
                        int W = tuple0->at(1);
                        int U = tuple0->at(2);
                        Tuple* negativeTuple = factory.addNewInternalTuple({U},&_b);
                        const Tuple* tuple1 = wb.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ub.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_b && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int V = tuple0->at(0);
                        int W = tuple0->at(1);
                        int U = tuple0->at(2);
                        Tuple* negativeTuple = factory.addNewInternalTuple({V,W},&_a);
                        const Tuple* tuple1 = wa.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ua.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef1){
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
                int V = head->at(0);
                int W = head->at(1);
                const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
                const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_.getValues({V,W});
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
                int V = head->at(0);
                int W = head->at(1);
                const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
                if(tuples->size() == 0){
                    const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_.getValues({V,W});
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
                int V = head->at(0);
                int W = head->at(1);
                const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
                if(tuples->size() == 0){
                    const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_.getValues({V,W});
                    for(unsigned j = 0; j < tuplesU->size();){
                        propUndefined(tuplesU->at(j),false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propagatedLiterals.insert(-1);
                }
            }
        }
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        starter.setNegated(startVar<0);
        std::string minus = starter.isNegated() ? "not " : "";
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aggr_set0){
            int V = starter[0];
            int W = starter[1];
            const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
            const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_.getValues({V,W});
            if(!starter.isNegated()){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    int itProp = tuplesU->at(0)->getId();
                    if(reasonForLiteral.count(itProp) == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
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
        if(starter.getPredicateName() == &_aux0){
            int V = starter[0];
            int W = starter[1];
            int U = starter[2];
            if(!starter.isNegated()){
                Tuple* head = factory.addNewInternalTuple({V,W}, &_aggr_set0);
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
                Tuple* head = factory.addNewInternalTuple({V,W}, &_aggr_set0);
                const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
                const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_.getValues({V,W});
                if(waggr_set0.find(*head) != NULL){
                    if(tuples->size()==0 && tuplesU->size()==0){
                        int itHead = head->getId();
                        const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i)->getId();
                            reasonForLiteral[-itHead].insert(-it);
                        }
                        handleConflict(-itHead);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
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
                            const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
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
            int V = starter[0];
            int W = starter[1];
            const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
            const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_.getValues({V,W});
            if(!starter.isNegated()){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    int itProp = tuplesU->at(0)->getId();
                    if(reasonForLiteral.count(itProp) == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux0_0_1_.getValues({V,W});
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
            if(starter.getPredicateName() == &_a && starter.isNegated()){
                int V = starter[0];
                int W = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({V,W});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_0_1_.getValues({V,W});
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == V && tupleU->at(1) == W)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int U = tuple1->at(2);
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
            if(starter.getPredicateName() == &_aux0 && !starter.isNegated()){
                int V = starter[0];
                int W = starter[1];
                int U = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({V,W},&_a);
                const Tuple* tuple1 = wa.find(*negativeTuple);
                const Tuple* tupleUndef1 = ua.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef1){
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
            if(starter.getPredicateName() == &_b && starter.isNegated()){
                int U = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paux0_2_.getValues({U});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_2_.getValues({U});
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
                        tuple1 = tuples->at(i);
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = tuplesU->at(i-tuples->size());
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(2) == U)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int V = tuple1->at(0);
                        int W = tuple1->at(1);
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
            if(starter.getPredicateName() == &_aux0 && !starter.isNegated()){
                int V = starter[0];
                int W = starter[1];
                int U = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({U},&_b);
                const Tuple* tuple1 = wb.find(*negativeTuple);
                const Tuple* tupleUndef1 = ub.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_b && tupleUNegated && tupleU==tupleUndef1){
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
            if(starter.getPredicateName() == &_a && !starter.isNegated()){
                if(starter.at(0)==starter.at(1)){
                    int W = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &paux0_1_.getValues({W});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_1_.getValues({W});
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
                            tuple1 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple1 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            if(tupleU->at(1) == W)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int V = tuple1->at(0);
                            int U = tuple1->at(2);
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
            }
            if(starter.getPredicateName() == &_aux0 && !starter.isNegated()){
                int V = starter[0];
                int W = starter[1];
                int U = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({W,W},&_a);
                const Tuple* tuple1 = wa.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ua.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                    if(tupleU == ua.find(*positiveTuple)){
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
            if(starter.getPredicateName() == &_aux0 && starter.isNegated()){
                int V = starter[0];
                int W = starter[1];
                int U = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                if(W >= V){
                    if(W >= U){
                        Tuple* positiveTuple = factory.addNewInternalTuple({V,W},&_a);
                        const Tuple* tuple3 = wa.find(*positiveTuple);
                        if(tuple3 == tupleU && tupleU == NULL){
                            tuple3 = tupleU = ua.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                            if(tupleU == ua.find(*positiveTuple)){
                                tuple3=tupleU;
                            }
                        }
                        if(tuple3!=NULL){
                            Tuple* positiveTuple = factory.addNewInternalTuple({U},&_b);
                            const Tuple* tuple4 = wb.find(*positiveTuple);
                            if(tuple4 == tupleU && tupleU == NULL){
                                tuple4 = tupleU = ub.find(*positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple4==NULL && tupleU->getPredicateName() == &_b && ! tupleUNegated){
                                if(tupleU == ub.find(*positiveTuple)){
                                    tuple4=tupleU;
                                }
                            }
                            if(tuple4!=NULL){
                                Tuple* negativeTuple = factory.addNewInternalTuple({W,W},&_a);
                                const Tuple* tuple5 = wa.find(*negativeTuple);
                                const Tuple* tupleUndef5 = ua.find(*negativeTuple);
                                if(tuple5 == tupleUndef5 && tupleUndef5 == NULL)
                                    tuple5 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef5 != NULL){
                                    tupleU = tuple5 = tupleUndef5;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef5){
                                    tuple5=tupleU;
                                }else if(tuple5!=NULL){
                                    tuple5=NULL;
                                }
                                if(tuple5!=NULL){
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
                                            if(tuple5!=tupleU){
                                                int it = tuple5->getId();
                                                reasonForLiteral[var].insert(it*-1);
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
                                        if(tuple5!=NULL){
                                            int it = tuple5->getId();
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
            if(starter.getPredicateName() == &_a && starter.isNegated()){
                if(starter.at(0)==starter.at(1)){
                    int W = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &pa_1_.getValues({W});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ua_1_.getValues({W});
                    else if(tupleU->getPredicateName() == &_a && !tupleUNegated)
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
                            if(tupleU->at(1) == W)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int V = tuple1->at(0);
                            if(W >= V){
                                const std::vector<const Tuple*>* tuples = &pb_.getValues({});
                                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ub_.getValues({});
                                else if(tupleU->getPredicateName() == &_b && !tupleUNegated)
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
                                    const Tuple* tuple3 = NULL;
                                    if(i<tuples->size())
                                        tuple3 = tuples->at(i);
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int U = tuple3->at(0);
                                        if(W >= U){
                                            Tuple* negativeTuple = factory.addNewInternalTuple({V,W,U},&_aux0);
                                            const Tuple* tuple5 = waux0.find(*negativeTuple);
                                            const Tuple* tupleUndef5 = uaux0.find(*negativeTuple);
                                            if(tuple5 == tupleUndef5 && tupleUndef5 == NULL)
                                                tuple5 = negativeTuple;
                                            else if(tupleU == NULL & tupleUndef5 != NULL){
                                                tupleU = tuple5 = tupleUndef5;
                                                tupleUNegated=true;
                                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef5){
                                                tuple5=tupleU;
                                            }else if(tuple5!=NULL){
                                                tuple5=NULL;
                                            }
                                            if(tuple5!=NULL){
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
                                                        if(tuple3!=tupleU){
                                                            int it = tuple3->getId();
                                                            reasonForLiteral[var].insert(it*1);
                                                        }
                                                        if(tuple5!=tupleU){
                                                            int it = tuple5->getId();
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
                                                    if(tuple3!=NULL){
                                                        int it = tuple3->getId();
                                                        reasonForLiteral[-startVar].insert(it*1);
                                                    }
                                                    if(tuple5!=NULL){
                                                        int it = tuple5->getId();
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
                }
            }
            if(starter.getPredicateName() == &_b && !starter.isNegated()){
                int U = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pa_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ua_.getValues({});
                else if(tupleU->getPredicateName() == &_a && !tupleUNegated)
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
                        int V = tuple1->at(0);
                        int W = tuple1->at(1);
                        if(W >= V){
                            if(W >= U){
                                Tuple* negativeTuple = factory.addNewInternalTuple({W,W},&_a);
                                const Tuple* tuple4 = wa.find(*negativeTuple);
                                const Tuple* tupleUndef4 = ua.find(*negativeTuple);
                                if(tuple4 == tupleUndef4 && tupleUndef4 == NULL)
                                    tuple4 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef4 != NULL){
                                    tupleU = tuple4 = tupleUndef4;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef4){
                                    tuple4=tupleU;
                                }else if(tuple4!=NULL){
                                    tuple4=NULL;
                                }
                                if(tuple4!=NULL){
                                    Tuple* negativeTuple = factory.addNewInternalTuple({V,W,U},&_aux0);
                                    const Tuple* tuple5 = waux0.find(*negativeTuple);
                                    const Tuple* tupleUndef5 = uaux0.find(*negativeTuple);
                                    if(tuple5 == tupleUndef5 && tupleUndef5 == NULL)
                                        tuple5 = negativeTuple;
                                    else if(tupleU == NULL & tupleUndef5 != NULL){
                                        tupleU = tuple5 = tupleUndef5;
                                        tupleUNegated=true;
                                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef5){
                                        tuple5=tupleU;
                                    }else if(tuple5!=NULL){
                                        tuple5=NULL;
                                    }
                                    if(tuple5!=NULL){
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
                                                if(tuple5!=tupleU){
                                                    int it = tuple5->getId();
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
                                            if(tuple5!=NULL){
                                                int it = tuple5->getId();
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
            if(starter.getPredicateName() == &_a && !starter.isNegated()){
                int V = starter[0];
                int W = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                if(W >= V){
                    Tuple* negativeTuple = factory.addNewInternalTuple({W,W},&_a);
                    const Tuple* tuple2 = wa.find(*negativeTuple);
                    const Tuple* tupleUndef2 = ua.find(*negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef2){
                        tuple2=tupleU;
                    }else if(tuple2!=NULL){
                        tuple2=NULL;
                    }
                    if(tuple2!=NULL){
                        const std::vector<const Tuple*>* tuples = &pb_.getValues({});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ub_.getValues({});
                        else if(tupleU->getPredicateName() == &_b && !tupleUNegated)
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
                            const Tuple* tuple3 = NULL;
                            if(i<tuples->size())
                                tuple3 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                tuple3 = tupleU;
                            }
                            if(tuple3!=NULL){
                                int U = tuple3->at(0);
                                if(W >= U){
                                    Tuple* negativeTuple = factory.addNewInternalTuple({V,W,U},&_aux0);
                                    const Tuple* tuple5 = waux0.find(*negativeTuple);
                                    const Tuple* tupleUndef5 = uaux0.find(*negativeTuple);
                                    if(tuple5 == tupleUndef5 && tupleUndef5 == NULL)
                                        tuple5 = negativeTuple;
                                    else if(tupleU == NULL & tupleUndef5 != NULL){
                                        tupleU = tuple5 = tupleUndef5;
                                        tupleUNegated=true;
                                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef5){
                                        tuple5=tupleU;
                                    }else if(tuple5!=NULL){
                                        tuple5=NULL;
                                    }
                                    if(tuple5!=NULL){
                                        if(tupleU != NULL){
                                            int itUndef = tupleU->getId();
                                            int var = tupleUNegated ? 1 : -1;
                                            var*=itUndef;
                                            if(reasonForLiteral.count(var) == 0){
                                                {
                                                    int it = starter.getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                                if(tuple2!=tupleU){
                                                    int it = tuple2->getId();
                                                    reasonForLiteral[var].insert(it*-1);
                                                }
                                                if(tuple3!=tupleU){
                                                    int it = tuple3->getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                                if(tuple5!=tupleU){
                                                    int it = tuple5->getId();
                                                    reasonForLiteral[var].insert(it*-1);
                                                }
                                            }else{
                                            }
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                        }else{
                                            if(tuple2!=NULL){
                                                int it = tuple2->getId();
                                                reasonForLiteral[-startVar].insert(it*-1);
                                            }
                                            if(tuple3!=NULL){
                                                int it = tuple3->getId();
                                                reasonForLiteral[-startVar].insert(it*1);
                                            }
                                            if(tuple5!=NULL){
                                                int it = tuple5->getId();
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
        }
        if(starter.getPredicateName() == &_aggr_id0){
            std::vector<int> sharedVar({});
            const std::vector<const Tuple*>* tuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_.getValues(sharedVar);
            if(starter.isNegated()){
                if(actualSum[uStartVar]>=2+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(int index=0; index<tuplesU->size();){
                        if(actualSum[uStartVar]+tuplesU->at(index)->at(0) >= 2+1){
                            int itProp =tuplesU->at(index)->getId();
                            if(reasonForLiteral.count(-itProp)==0){
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        int it = tuples->at(i)->getId();
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    reason.push_back(startVar);
                                    reasonForLiteral[-itProp].insert(startVar);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(tuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                        }else index++;
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < 2+1){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();){
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at(0) < 2+1){
                            int itProp = tuplesU->at(index)->getId();
                            if(reasonForLiteral.count(itProp) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i)->getId();
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                        }else index++;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 2+1){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= 2+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(actualSum[aggrIdIt] >= 2+1){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= 2+1){
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
                            propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(actualSum[aggrIdIt] >= 2+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 2+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
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
            if(starter.getPredicateName() == &_aggr_id0 && starter.isNegated()){
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                if(tupleU != NULL){
                    int itUndef = tupleU->getId();
                    int var = tupleUNegated ? 1 : -1;
                    var*=itUndef;
                    if(reasonForLiteral.count(var) == 0){
                        {
                            int it = starter.getId();
                            reasonForLiteral[var].insert(it*-1);
                        }
                    }else{
                    }
                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                }else{
                    handleConflict(-startVar);
                    return;
                }
            }
        }
    }
}
}
