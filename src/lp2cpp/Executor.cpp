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
const std::string _aux1 = "aux1";
const std::string _body0 = "body0";
const std::string _dom0 = "dom0";
const std::string _l0 = "l0";
const std::string _l1 = "l1";
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
AuxMap<0> pl1_({});
AuxMap<0> ul1_({});
AuxMap<0> fl1_({});
AuxMap<0> pl0_({});
AuxMap<0> ul0_({});
AuxMap<0> fl0_({});
AuxMap<0> pdom0_({});
AuxMap<0> udom0_({});
AuxMap<0> fdom0_({});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<32> paggr_set0_0_({0});
AuxMap<32> uaggr_set0_0_({0});
AuxMap<32> faggr_set0_0_({0});
AuxMap<32> paggr_set0_1_({1});
AuxMap<32> uaggr_set0_1_({1});
AuxMap<32> faggr_set0_1_({1});
AuxMap<32> paux1_0_({0});
AuxMap<32> uaux1_0_({0});
AuxMap<32> faux1_0_({0});
AuxMap<0> paux1_({});
AuxMap<0> uaux1_({});
AuxMap<0> faux1_({});
AuxMap<0> pbody0_({});
AuxMap<0> ubody0_({});
AuxMap<0> fbody0_({});
AuxMap<32> paux1_1_({1});
AuxMap<32> uaux1_1_({1});
AuxMap<32> faux1_1_({1});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<32> paggr_id0_0_({0});
AuxMap<32> uaggr_id0_0_({0});
AuxMap<32> faggr_id0_0_({0});
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
    if(insertResult.first->getPredicateName() == &_body0){
        fbody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2Vec(*insertResult.first);
        faggr_id0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        faux1_.insert2Vec(*insertResult.first);
        faux1_0_.insert2Vec(*insertResult.first);
        faux1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2Vec(*insertResult.first);
        faggr_set0_0_.insert2Vec(*insertResult.first);
        faggr_set0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_dom0){
        fdom0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        fl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        fl1_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_body0){
        pbody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2Vec(*insertResult.first);
        paggr_id0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        paux1_.insert2Vec(*insertResult.first);
        paux1_0_.insert2Vec(*insertResult.first);
        paux1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2Vec(*insertResult.first);
        paggr_set0_0_.insert2Vec(*insertResult.first);
        paggr_set0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_dom0){
        pdom0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        pl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        pl1_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_body0){
        ubody0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2Vec(*insertResult.first);
        uaggr_id0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        uaux1_.insert2Vec(*insertResult.first);
        uaux1_0_.insert2Vec(*insertResult.first);
        uaux1_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2Vec(*insertResult.first);
        uaggr_set0_0_.insert2Vec(*insertResult.first);
        uaggr_set0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_dom0){
        udom0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        ul0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        ul1_.insert2Vec(*insertResult.first);
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
        const std::vector<int>* tuples = &pl1_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul1_.getValuesVec({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = tuple->at(0);
            const std::vector<int>* tuples = &pl1_.getValuesVec({});
            const std::vector<int>* tuplesU = &ul1_.getValuesVec({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int T1 = tuple->at(0);
                Tuple* aux = factory.addNewInternalTuple({T1,T0}, &_aux1);
                const auto& insertResult = aux->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(aux->getId());
                    insertUndef(insertResult);
                    {
                        Tuple* head = factory.addNewInternalTuple({T1},&_body0);
                        const auto& headInsertResult = head->setStatus(Undef);
                        if (headInsertResult.second) {
                            factory.removeFromCollisionsList(head->getId());
                            insertUndef(headInsertResult);
                        }
                        Tuple* aggr_id7 = factory.addNewInternalTuple({T1},&_aggr_id0);
                        const auto& aggrIdInsertResult7 = aggr_id7->setStatus(Undef);
                        if (aggrIdInsertResult7.second) {
                            factory.removeFromCollisionsList(aggr_id7->getId());
                            insertUndef(aggrIdInsertResult7);
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pbody0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ubody0_.getValuesVec({});
        const std::vector<int>* tuplesF = &fbody0_.getValuesVec({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size()+tuplesF->size();i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            }else if(i<tuples->size()+tuplesU->size()){
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            }else if(i<tuples->size()+tuplesU->size()+tuplesF->size()){
                tuple=factory.getTupleFromInternalID(tuplesF->at(i-tuples->size()-tuplesU->size()));
            }
            int T1 = tuple->at(0);
            Tuple* dom = factory.addNewInternalTuple({T1}, &_dom0);
            const auto& insertResult = dom->setStatus(True);
            if (insertResult.second) {
                factory.removeFromCollisionsList(dom->getId());
                insertTrue(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pl0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T2 = tuple->at(0);
            const std::vector<int>* tuples = &pdom0_.getValuesVec({});
            const std::vector<int>* tuplesU = &udom0_.getValuesVec({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int T1 = tuple->at(0);
                Tuple* boundTuple = factory.find({T1}, &_l0);
                if(boundTuple == NULL || !boundTuple->isTrue()){
                    Tuple* aux = factory.addNewInternalTuple({T2,T1}, &_aggr_set0);
                    const auto& insertResult = aux->setStatus(Undef);
                    if (insertResult.second) {
                        factory.removeFromCollisionsList(aux->getId());
                        insertUndef(insertResult);
                    }
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
    pbody0_.clear();
    paggr_id0_.clear();
    paggr_id0_0_.clear();
    fbody0_.clear();
    faggr_id0_.clear();
    faggr_id0_0_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    stringToUniqueStringPointer["body0"] = &_body0;
    stringToUniqueStringPointer["dom0"] = &_dom0;
    stringToUniqueStringPointer["l0"] = &_l0;
    stringToUniqueStringPointer["l1"] = &_l1;
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
                        int T1 = tuple0->at(0);
                        Tuple negativeTuple({T1},&_aggr_id0);
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
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &pl1_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ul1_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_l1 && !tupleUNegated)
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
                        int T0 = tuple0->at(0);
                        const std::vector<int>* tuples = &pl1_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ul1_.getValuesVec({});
                        else if(tupleU->getPredicateName() == &_l1 && !tupleUNegated)
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
                                int T1 = tuple1->at(0);
                                Tuple negativeTuple({T1,T0},&_aux1);
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
                                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        int T1 = tuple0->at(0);
                        int T0 = tuple0->at(1);
                        Tuple negativeTuple({T1},&_l1);
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
                                    if(tupleU->getPredicateName() != &_l1 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                        int T1 = tuple0->at(0);
                        int T0 = tuple0->at(1);
                        Tuple negativeTuple({T0},&_l1);
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
                                    if(tupleU->getPredicateName() != &_l1 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &pl0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ul0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_l0 && !tupleUNegated)
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
                        int T2 = tuple0->at(0);
                        const std::vector<int>* tuples = &pdom0_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &udom0_.getValuesVec({});
                        else if(tupleU->getPredicateName() == &_dom0 && !tupleUNegated)
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
                                int T1 = tuple1->at(0);
                                Tuple negativeTuple({T1},&_l0);
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
                                            if(tupleU->getPredicateName() != &_l0 || !tupleUNegated || !(*tupleU == *tuple2))
                                            tuple2=NULL;
                                        }
                                    }
                                }
                                if(tuple2!=NULL){
                                    Tuple negativeTuple({T2,T1},&_aggr_set0);
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
                                                if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
                                        if(tupleU != NULL){
                                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paggr_set0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        int T2 = tuple0->at(0);
                        int T1 = tuple0->at(1);
                        const Tuple* tuple1 = factory.find({T1},&_l0);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_l0 || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                const std::vector<int>* tuples = &paggr_set0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        int T2 = tuple0->at(0);
                        int T1 = tuple0->at(1);
                        Tuple negativeTuple({T2},&_l0);
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
                                    if(tupleU->getPredicateName() != &_l0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                int T1 = currentHead->at(0);
                const std::vector<int>* tuples = &paux1_0_.getValuesVec({T1});
                const std::vector<int>* tuplesU = &uaux1_0_.getValuesVec({T1});
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
                int T1 = currentHead->at(0);
                const std::vector<int>* tuples = &paux1_0_.getValuesVec({T1});
                const std::vector<int>* tuplesU = &uaux1_0_.getValuesVec({T1});
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
                int T1 = currentHead->at(0);
                const std::vector<int>* tuples = &paux1_0_.getValuesVec({T1});
                const std::vector<int>* tuplesU = &uaux1_0_.getValuesVec({T1});
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
                int T1 = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() + joinTuplesU->size() < 7+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 7+1){
                    if(!joinTuplesU->empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it = joinTuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        shared_reason.get()->insert(itAggrId);
                    }
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0);
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int T1 = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 7+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 7+1 -1){
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));
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
                int T1 = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValuesVec(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(joinTuples->size() >= 7+1){
                    int itProp = tuplesU->at(i);
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(joinTuples->size() + joinTuplesU->size() < 7+1){
                    int itProp = tuplesU->at(i);
                    const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
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
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
        {
            if(starter.getPredicateName() == &_l0 && startVar < 0){
                int T2 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paggr_set0_0_.getValuesVec({T2});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_0_.getValuesVec({T2});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        if(tupleU->at(0) == T2)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T1 = tuple1->at(1);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                int T2 = starter[0];
                int T1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({T2},&_l0);
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
                            if(tupleU->getPredicateName() != &_l0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            if(starter.getPredicateName() == &_l0 && startVar > 0){
                int T1 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paggr_set0_1_.getValuesVec({T1});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_1_.getValuesVec({T1});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        if(tupleU->at(1) == T1)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T2 = tuple1->at(0);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                int T2 = starter[0];
                int T1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({T1},&_l0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_l0 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            if(starter.getPredicateName() == &_aggr_set0 && startVar < 0){
                int T2 = starter[0];
                int T1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({T2},&_l0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_l0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    Tuple negativeTuple({T1},&_l0);
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
                                if(tupleU->getPredicateName() != &_l0 || !tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
                        const Tuple* tuple3 = factory.find({T1},&_dom0);
                        if(tuple3!=NULL){
                            if(tuple3->isFalse())
                            tuple3=NULL;
                            else if(tuple3->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple3;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_dom0 || tupleUNegated || !(*tupleU == *tuple3))
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
                                    shared_reason.get()->insert(it*-1);
                                }
                                if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                    int it = tuple3->getId();
                                    shared_reason.get()->insert(it*1);
                                }
                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            if(starter.getPredicateName() == &_dom0 && startVar > 0){
                int T1 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({T1},&_l0);
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
                            if(tupleU->getPredicateName() != &_l0 || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const std::vector<int>* tuples = &pl0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ul0_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_l0 && !tupleUNegated)
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
                            int T2 = tuple2->at(0);
                            Tuple negativeTuple({T2,T1},&_aggr_set0);
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
                                        if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                        shared_reason.get()->insert(it*-1);
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            if(starter.getPredicateName() == &_l0 && startVar < 0){
                int T1 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({T1},&_dom0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_dom0 || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const std::vector<int>* tuples = &pl0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ul0_.getValuesVec({});
                    else if(tupleU->getPredicateName() == &_l0 && !tupleUNegated)
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
                            int T2 = tuple2->at(0);
                            Tuple negativeTuple({T2,T1},&_aggr_set0);
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
                                        if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            if(starter.getPredicateName() == &_l0 && startVar > 0){
                int T2 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &pdom0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &udom0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_dom0 && !tupleUNegated)
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
                        int T1 = tuple1->at(0);
                        Tuple negativeTuple({T1},&_l0);
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
                                    if(tupleU->getPredicateName() != &_l0 || !tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple negativeTuple({T2,T1},&_aggr_set0);
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
                                        if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        if(starter.getPredicateName() == &_aux1){
            int T1 = starter.at(0);
            int T0 = starter.at(1);
            Tuple* head = factory.find({T1}, &_body0);
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
                const std::vector<int>* tuples = &paux1_0_.getValuesVec({T1});
                const std::vector<int>* tuplesU = &uaux1_0_.getValuesVec({T1});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux1_0_.getValuesVec({T1});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux1_0_.getValuesVec({T1});
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
                        const std::vector<int>* tuplesF = &faux1_0_.getValuesVec({T1});
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
            int T1 = starter.at(0);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux1_0_.getValuesVec({T1});
            const std::vector<int>* tuplesU = &uaux1_0_.getValuesVec({T1});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        const std::vector<int>* tuplesF = &faux1_0_.getValuesVec({T1});
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
                        const std::vector<int>* tuplesF = &faux1_0_.getValuesVec({T1});
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
        if(starter.getPredicateName() == &_l1 && startVar < 0){
            int T0 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &paux1_1_.getValuesVec({T0});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux1_1_.getValuesVec({T0});
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
                    if(tupleU->at(1) == T0)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int T1 = tuple1->at(0);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            int T1 = starter[0];
            int T0 = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({T0},&_l1);
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
                        if(tupleU->getPredicateName() != &_l1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_l1 && startVar < 0){
            int T1 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &paux1_0_.getValuesVec({T1});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux1_0_.getValuesVec({T1});
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
                    if(tupleU->at(0) == T1)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int T0 = tuple1->at(1);
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            int T1 = starter[0];
            int T0 = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({T1},&_l1);
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
                        if(tupleU->getPredicateName() != &_l1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            int T1 = starter[0];
            int T0 = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const Tuple* tuple1 = factory.find({T0},&_l1);
            if(tuple1!=NULL){
                if(tuple1->isFalse())
                tuple1=NULL;
                else if(tuple1->isUndef()){
                    if(tupleU == NULL){
                        tupleU = tuple1;
                        tupleUNegated=false;
                    }else{
                        if(tupleU->getPredicateName() != &_l1 || tupleUNegated || !(*tupleU == *tuple1))
                        tuple1=NULL;
                    }
                }
            }
            if(tuple1!=NULL){
                const Tuple* tuple2 = factory.find({T1},&_l1);
                if(tuple2!=NULL){
                    if(tuple2->isFalse())
                    tuple2=NULL;
                    else if(tuple2->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple2;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_l1 || tupleUNegated || !(*tupleU == *tuple2))
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
                        if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_l1 && startVar > 0){
            int T1 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &pl1_.getValuesVec({});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &ul1_.getValuesVec({});
            else if(tupleU->getPredicateName() == &_l1 && !tupleUNegated)
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
                    int T0 = tuple1->at(0);
                    Tuple negativeTuple({T1,T0},&_aux1);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_l1 && startVar > 0){
            int T0 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &pl1_.getValuesVec({});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &ul1_.getValuesVec({});
            else if(tupleU->getPredicateName() == &_l1 && !tupleUNegated)
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
                    int T1 = tuple1->at(0);
                    Tuple negativeTuple({T1,T0},&_aux1);
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
                            if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
        int T1 = starter[0];
        std::vector<int> sharedVar({starter[0]});
        const std::vector<int>* tuples = &paggr_set0_1_.getValuesVec(sharedVar);
        const std::vector<int>* tuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
        if(startVar < 0){
            if(tuples->size()>=7+1){
                for(unsigned i =0; i< tuples->size(); i++){
                    int it = tuples->at(i);
                    shared_reason.get()->insert(it);
                }
                reasonForLiteral[-startVar]=shared_reason;
                handleConflict(-startVar, propagatedLiterals);
                return;
            }else if(tuples->size() == 7+1 -1){
                for(unsigned i =0; i< tuples->size(); i++){
                    int it = tuples->at(i);
                    shared_reason.get()->insert(it);
                }
                shared_reason.get()->insert(startVar);
                while(!tuplesU->empty()){
                    int itProp = tuplesU->at(0);
                    auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }else{
            if(tuples->size()+tuplesU->size() < 7+1){
                const std::vector<int>* tuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
                for(unsigned i = 0; i < tuplesF->size(); i++){
                    int it = tuplesF->at(i);
                    shared_reason.get()->insert(-it);
                }
                reasonForLiteral[-startVar]=shared_reason;
                handleConflict(-startVar, propagatedLiterals);
                return;
            }else if(tuples->size() + tuplesU->size() == 7+1){
                if(tuplesU->size() > 0){
                    const std::vector<int>* tuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        shared_reason.get()->insert(-it);
                    }
                    shared_reason.get()->insert(startVar);
                }
                while(tuplesU->size()>0){
                    int itProp = tuplesU->at(0);
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
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
            int T1 = currentTuple->at(0);
            std::vector<int> sharedVar({currentTuple->at(0)});
            const std::vector<int>* joinTuples = &paggr_set0_1_.getValuesVec(sharedVar);
            const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
            int aggrIdIt=tuples->at(i);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(joinTuples->size() + joinTuplesU->size() < 7+1){
                int itProp = tuples->at(i);
                const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                    int it = joinTuplesF->at(j);
                    shared_reason.get()->insert(-it);
                }
                reasonForLiteral[-itProp]=shared_reason;
                handleConflict(-itProp, propagatedLiterals);
                return;
            }else if(joinTuples->size() + joinTuplesU->size() == 7+1){
                if(!joinTuplesU->empty()){
                    const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
                    for(unsigned i = 0; i < joinTuplesF->size(); i++){
                        int it = joinTuplesF->at(i);
                        shared_reason.get()->insert(-it);
                    }
                    int itAggrId = tuples->at(i);
                    shared_reason.get()->insert(itAggrId);
                }
                while(joinTuplesU->size()>0){
                    int itProp = joinTuplesU->at(0);
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
            int T1 = currentTuple->at(0);
            std::vector<int> sharedVar({currentTuple->at(0)});
            const std::vector<int>* joinTuples = &paggr_set0_1_.getValuesVec(sharedVar);
            const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
            int aggrIdIt=tuplesF->at(i);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(joinTuples->size() >= 7+1){
                int itProp = tuplesF->at(i);
                for(unsigned j =0; j< joinTuples->size(); j++){
                    int it = joinTuples->at(j);
                    shared_reason.get()->insert(it);
                }
                reasonForLiteral[itProp]=shared_reason;
                handleConflict(itProp, propagatedLiterals);
                return;
            }else if(joinTuples->size() == 7+1 -1){
                while(!joinTuplesU->empty()){
                    int itProp = joinTuplesU->at(0);
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));
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
            int T1 = currentTuple->at(0);
            std::vector<int> sharedVar({currentTuple->at(0)});
            const std::vector<int>* joinTuples = &paggr_set0_1_.getValuesVec(sharedVar);
            const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValuesVec(sharedVar);
            int aggrIdIt=tuplesU->at(i);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(joinTuples->size() >= 7+1){
                int itProp = tuplesU->at(i);
                for(unsigned j = 0; j < joinTuples->size(); j++){
                    int it = joinTuples->at(j);
                    shared_reason.get()->insert(it);
                }
                auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                if(!itReason.second && itReason.first->second.get()->empty())
                    itReason.first->second=shared_reason;
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }else if(joinTuples->size() + joinTuplesU->size() < 7+1){
                int itProp = tuplesU->at(i);
                const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValuesVec(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_id0 && startVar < 0){
            int T1 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const Tuple* tuple1 = factory.find({T1},&_body0);
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
                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
            int T1 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({T1},&_aggr_id0);
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
                    if(tupleU->getPredicateName() != &_body0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aux1)
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
}
if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
}
}
