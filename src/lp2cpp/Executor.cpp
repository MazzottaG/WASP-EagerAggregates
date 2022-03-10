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
const std::string _reaches = "reaches";
const std::string _connected = "connected";
const std::string _offline = "offline";
const std::string _node = "node";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
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
AuxMap<0> preaches_({});
AuxMap<0> ureaches_({});
AuxMap<0> freaches_({});
AuxMap<32> pconnected_0_({0});
AuxMap<32> uconnected_0_({0});
AuxMap<32> fconnected_0_({0});
AuxMap<0> pnode_({});
AuxMap<0> unode_({});
AuxMap<0> fnode_({});
AuxMap<0> pconnected_({});
AuxMap<0> uconnected_({});
AuxMap<0> fconnected_({});
void Executor::handleConflict(int literal,std::vector<int>& propagatedLiterals){
    if(currentDecisionLevel <= 0){
        propagatedLiterals.push_back(1);
        return;
    }

    std::vector<int> visitedLiterals(2*factory.size());
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    explainExternalLiteral(literal,conflictReason,visitedLiterals,true);
    explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);
    propagatedLiterals.push_back(1);
    reasonForLiteral[literal].get()->clear();
}
int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,std::vector<int>& visitedLiteral,bool propagatorCall){
    int literalsCount = factory.size();
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        Tuple* waspTuple = factory.getTupleFromWASPID(uVar);
        if(waspTuple==NULL) std::cout << "WARNING: Unable to find tuple from wasp id in explainExternalLiteral"<<std::endl;
        int internalVar = waspTuple->getId();
        var = var>0 ? internalVar : -internalVar;
        visitedLiteral.resize(2*literalsCount);
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
            int& visitCount = reasonLiteral>=0 ? visitedLiteral[reasonLiteral] : visitedLiteral[literalsCount-reasonLiteral];
            if(visitCount == 0){
                visitCount++;
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
    if(insertResult.first->getPredicateName() == &_node){
        fnode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_connected){
        fconnected_.insert2Vec(*insertResult.first);
        fconnected_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_reaches){
        freaches_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_node){
        pnode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_connected){
        pconnected_.insert2Vec(*insertResult.first);
        pconnected_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_reaches){
        preaches_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_node){
        unode_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_connected){
        uconnected_.insert2Vec(*insertResult.first);
        uconnected_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_reaches){
        ureaches_.insert2Vec(*insertResult.first);
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
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    std::cout<<"Undef received"<<std::endl;
    foundnessFactory.resize(factory.size());
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
    stringToUniqueStringPointer["connected"] = &_connected;
    stringToUniqueStringPointer["node"] = &_node;
    stringToUniqueStringPointer["offline"] = &_offline;
    stringToUniqueStringPointer["reaches"] = &_reaches;
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
    fnode_.clear();
    freaches_.clear();
}
inline void clearTrue(){
    pnode_.clear();
    preaches_.clear();
}
inline void clearUndef(){
    unode_.clear();
    ureaches_.clear();
}
std::string Executor::printInternalLiterals(){
    std::string trueConstraint = "";
    std::cout << std::endl;
    TupleFactory lazyFactory;
    {
        {
            const std::vector<int>* tuples = &pconnected_.getValuesVec({});
            for(unsigned i=0; i<tuples->size();i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                int Y = currentTuple->at(1);
                std::vector<int> head({Y});
                Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,&_node);
                const auto& insertResult = tupleHead->setStatus(True);
                if (insertResult.second) {
                    lazyFactory.removeFromCollisionsList(tupleHead->getId());
                    insertTrue(insertResult);
                    std::cout<<"node("<<ConstantsManager::getInstance().unmapConstant(head[0])<<")"<<std::endl;
                }
            }
        }
        {
            const std::vector<int>* tuples = &pconnected_.getValuesVec({});
            for(unsigned i=0; i<tuples->size();i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                int Y = currentTuple->at(1);
                std::vector<int> head({X});
                Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,&_node);
                const auto& insertResult = tupleHead->setStatus(True);
                if (insertResult.second) {
                    lazyFactory.removeFromCollisionsList(tupleHead->getId());
                    insertTrue(insertResult);
                    std::cout<<"node("<<ConstantsManager::getInstance().unmapConstant(head[0])<<")"<<std::endl;
                }
            }
        }
    }
    {
        std::vector<int> stack;
        {
            const std::vector<int>* tuples = &pnode_.getValuesVec({});
            for(unsigned i=0; i<tuples->size();i++){
                const Tuple* currentTuple = lazyFactory.getTupleFromInternalID(tuples->at(i));
                int X = currentTuple->at(0);
                Tuple* boundTuple = factory.find({X},&_offline);
                if(boundTuple == NULL or boundTuple->isFalse()){
                    std::vector<int> head({X,X});
                    Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,&_reaches);
                    const auto& insertResult = tupleHead->setStatus(True);
                    if (insertResult.second) {
                        lazyFactory.removeFromCollisionsList(tupleHead->getId());
                        insertTrue(insertResult);
                        stack.push_back(tupleHead->getId());
                        std::cout<<"reaches("<<ConstantsManager::getInstance().unmapConstant(head[0])<<","<<ConstantsManager::getInstance().unmapConstant(head[1])<<")"<<std::endl;
                    }
                }
            }
        }
        while(!stack.empty()){
            Tuple* starter = lazyFactory.getTupleFromInternalID(stack.back());
            stack.pop_back();
            if(starter->getPredicateName() == &_reaches){
                int X = starter->at(0);
                int Y = starter->at(1);
                const std::vector<int>* tuples = &pconnected_0_.getValuesVec({Y});
                for(unsigned i=0; i<tuples->size();i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int Z = currentTuple->at(1);
                    Tuple* boundTuple = factory.find({Z},&_offline);
                    if(boundTuple == NULL or boundTuple->isFalse()){
                        std::vector<int> head({X,Z});
                        Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,&_reaches);
                        const auto& insertResult = tupleHead->setStatus(True);
                        if (insertResult.second) {
                            lazyFactory.removeFromCollisionsList(tupleHead->getId());
                            insertTrue(insertResult);
                            stack.push_back(tupleHead->getId());
                            std::cout<<"reaches("<<ConstantsManager::getInstance().unmapConstant(head[0])<<","<<ConstantsManager::getInstance().unmapConstant(head[1])<<")"<<std::endl;
                        }
                    }
                }
            }
        }
    }
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
    }//close decision level == -1
    std::vector<int> propagated;
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        propagated.push_back(startVar);
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
    }
    if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
}
}
