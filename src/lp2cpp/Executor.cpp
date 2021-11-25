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
const std::string _l0 = "l0";
const std::string _l1 = "l1";
const std::string _l2 = "l2";
const std::string _l3 = "l3";
const std::string _l4 = "l4";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
tsl::hopscotch_map<int,int> actualSum;
tsl::hopscotch_map<int,int> possibleSum;
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
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<0> pl2_({});
AuxMap<0> ul2_({});
AuxMap<0> fl2_({});
AuxMap<32> paux0_0_({0});
AuxMap<32> uaux0_0_({0});
AuxMap<32> faux0_0_({0});
AuxMap<0> paux1_({});
AuxMap<0> uaux1_({});
AuxMap<0> faux1_({});
AuxMap<0> pl3_({});
AuxMap<0> ul3_({});
AuxMap<0> fl3_({});
AuxMap<0> pl0_({});
AuxMap<0> ul0_({});
AuxMap<0> fl0_({});
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
    if(insertResult.first->getPredicateName() == &_l3){
        fl3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        faux1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l2){
        fl2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2Vec(*insertResult.first);
        faux0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        fl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        fl1_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_l3){
        pl3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        paux1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l2){
        pl2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2Vec(*insertResult.first);
        paux0_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        pl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        pl1_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_l3){
        ul3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        uaux1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l2){
        ul2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2Vec(*insertResult.first);
        uaux0_0_.insert2Vec(*insertResult.first);
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
        int X0 = 2 + 2;
        Tuple* boundTuple = factory.find({3}, &_l1);
        if(boundTuple != NULL  && !boundTuple->isFalse()){
            const std::vector<int>* tuples = &pl1_.getValuesVec({});
            const std::vector<int>* tuplesU = &ul1_.getValuesVec({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int X1 = tuple->at(0);
                Tuple* aux = factory.addNewInternalTuple({X1,X0}, &_aux0);
                const auto& insertResult = aux->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(aux->getId());
                    insertUndef(insertResult);
                    {
                        Tuple* head = factory.addNewInternalTuple({2},&_l2);
                        const auto& headInsertResult = head->setStatus(Undef);
                        if (headInsertResult.second) {
                            factory.removeFromCollisionsList(head->getId());
                            insertUndef(headInsertResult);
                        }
                    }
                }
            }
        }
    }
    {
        Tuple* boundTuple = factory.find({2}, &_l2);
        if(boundTuple == NULL || !boundTuple->isTrue()){
            Tuple* aux = factory.addNewInternalTuple({}, &_aux1);
            const auto& insertResult = aux->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(aux->getId());
                insertUndef(insertResult);
                {
                    Tuple* head = factory.addNewInternalTuple({2},&_l3);
                    const auto& headInsertResult = head->setStatus(Undef);
                    if (headInsertResult.second) {
                        factory.removeFromCollisionsList(head->getId());
                        insertUndef(headInsertResult);
                    }
                }
            }
        }
    }
    std::cout<<possibleSum.size()<<std::endl;
    std::cout<<possibleSum.bucket_count()<<std::endl;
    std::cout<<possibleSum.load_factor()<<std::endl;
    std::cout<<"exit undef received"<<std::endl;
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
    pl3_.clear();
    pl2_.clear();
    fl3_.clear();
    fl2_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aux0"] = &_aux0;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    stringToUniqueStringPointer["l0"] = &_l0;
    stringToUniqueStringPointer["l1"] = &_l1;
    stringToUniqueStringPointer["l2"] = &_l2;
    stringToUniqueStringPointer["l3"] = &_l3;
    stringToUniqueStringPointer["l4"] = &_l4;
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
    for(int internalId : pl3_.getValuesVec({})){
        factory.getTupleFromInternalID(internalId)->print();
    }
    for(int internalId : pl2_.getValuesVec({})){
        factory.getTupleFromInternalID(internalId)->print();
    }
    {
        std::set<std::vector<int>> trueHeads;
        const std::vector<int>* tuples = &pl2_.getValuesVec({});
        for(unsigned i=0; i<tuples->size();i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int X0 = currentTuple->at(0);
            std::vector<int> head({X0,X0,X0});
            std::cout<<"l4("<<head[0]<<","<<head[1]<<","<<head[2]<<")"<<std::endl;
        }
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
                Tuple negativeTuple({2},&_l2);
                const Tuple* tuple0 = factory.find(negativeTuple);
                if(tuple0 == NULL)
                    tuple0 = &negativeTuple;
                else{
                    if(tuple0->isTrue())
                        tuple0 = NULL;
                    else if(tuple0->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple0;
                            tupleUNegated=true;
                        }else{
                            if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple0))
                            tuple0=NULL;
                        }
                    }
                }
                if(tuple0!=NULL){
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
                            int X0 = tuple1->at(0);
                            int X1 = tuple1->at(1);
                            int X2 = tuple1->at(2);
                            const std::vector<int>* tuples = &pl3_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ul3_.getValuesVec({});
                            else if(tupleU->getPredicateName() == &_l3 && !tupleUNegated)
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
                                    int X3 = tuple2->at(0);
                                    if(tupleU != NULL){
                                        if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
                Tuple negativeTuple({2},&_l2);
                const Tuple* tuple0 = factory.find(negativeTuple);
                if(tuple0 == NULL)
                    tuple0 = &negativeTuple;
                else{
                    if(tuple0->isTrue())
                        tuple0 = NULL;
                    else if(tuple0->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple0;
                            tupleUNegated=true;
                        }else{
                            if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple0))
                            tuple0=NULL;
                        }
                    }
                }
                if(tuple0!=NULL){
                    Tuple negativeTuple({},&_aux1);
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
                                if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
                        }
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            propagatedLiterals.push_back(1);
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
                const Tuple* tuple0 = factory.find({},&_aux1);
                if(tuple0!=NULL){
                    if(tuple0->isFalse())
                    tuple0=NULL;
                    else if(tuple0->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple0;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aux1 || tupleUNegated || !(*tupleU == *tuple0))
                            tuple0=NULL;
                        }
                    }
                }
                if(tuple0!=NULL){
                    const Tuple* tuple1 = factory.find({2},&_l2);
                    if(tuple1!=NULL){
                        if(tuple1->isFalse())
                        tuple1=NULL;
                        else if(tuple1->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple1;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_l2 || tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
                        }
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            propagatedLiterals.push_back(1);
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
                int X0 = 2 + 2;
                const Tuple* tuple1 = factory.find({3},&_l1);
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
                            int X1 = tuple2->at(0);
                            Tuple negativeTuple({X1,X0},&_aux0);
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
                                        if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple3))
                                        tuple3=NULL;
                                    }
                                }
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
                        int X1 = tuple0->at(0);
                        int X0 = tuple0->at(1);
                        Tuple negativeTuple({X1},&_l1);
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
                                if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
                Tuple negativeTuple({3},&_l1);
                const Tuple* tuple0 = factory.find(negativeTuple);
                if(tuple0 == NULL)
                    tuple0 = &negativeTuple;
                else{
                    if(tuple0->isTrue())
                        tuple0 = NULL;
                    else if(tuple0->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple0;
                            tupleUNegated=true;
                        }else{
                            if(tupleU->getPredicateName() != &_l1 || !tupleUNegated || !(*tupleU == *tuple0))
                            tuple0=NULL;
                        }
                    }
                }
                if(tuple0!=NULL){
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
                            int X1 = tuple1->at(0);
                            int X0 = tuple1->at(1);
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
            const std::vector<int>* trueHeads = &pl2_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                if(currentHead->at(0) == 2){
                    const std::vector<int>* tuples = &paux0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &uaux0_.getValuesVec({});
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
            const std::vector<int>* falseHeads = &fl2_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                if(currentHead->at(0) == 2){
                    const std::vector<int>* tuples = &paux0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &uaux0_.getValuesVec({});
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
            const std::vector<int>* undefHeads = &ul2_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                if(currentHead->at(0) == 2){
                    const std::vector<int>* tuples = &paux0_.getValuesVec({});
                    const std::vector<int>* tuplesU = &uaux0_.getValuesVec({});
                    if(tuples->size() > 0)
                        propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    else if(tuplesU->size()==0)
                        propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    else i++;
                }
            }
        }
        {
            const std::vector<int>* trueHeads = &pl3_.getValuesVec({});
            for(unsigned i = 0;i < trueHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));
                if(currentHead->at(0) == 2){
                    Tuple* currentBody = factory.find({}, &_aux1);
                    if(!currentBody->isUndef() && !currentBody->isTrue()){
                        propagatedLiterals.push_back(1);
                        return;
                    }else if(currentBody->isUndef()){
                        propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const std::vector<int>* falseHeads = &fl3_.getValuesVec({});
            for(unsigned i = 0;i < falseHeads->size(); i++){
                const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));
                if(currentHead->at(0) == 2){
                    Tuple* currentBody = factory.find({}, &_aux1);
                    if(currentBody->isTrue()){
                        propagatedLiterals.push_back(1);
                        return;
                    }else if(currentBody->isUndef()){
                        propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const std::vector<int>* undefHeads = &ul3_.getValuesVec({});
            for(unsigned i = 0; i < undefHeads->size();){
                const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));
                if(currentHead->at(0) == 2){
                    const Tuple* currentBody = factory.find({}, &_aux1);
                    if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))
                        propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    else if(currentBody!=NULL && currentBody->isTrue())
                        propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    else i++;
                }
            }
        }
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aux0){
            int X1 = starter.at(0);
            int X0 = starter.at(1);
            Tuple* head = factory.find({2}, &_l2);
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
                const std::vector<int>* tuples = &paux0_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaux0_.getValuesVec({});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux0_.getValuesVec({});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux0_.getValuesVec({});
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
                        const std::vector<int>* tuplesF = &faux0_.getValuesVec({});
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
        }else if(starter.getPredicateName() == &_l2){
            if(starter.at(0) == 2){
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                const std::vector<int>* tuples = &paux0_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaux0_.getValuesVec({});
                if(startVar > 0){
                    if(tuples->size()==0){
                        if(tuplesU->size() == 0){
                            const std::vector<int>* tuplesF = &faux0_.getValuesVec({});
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
                            const std::vector<int>* tuplesF = &faux0_.getValuesVec({});
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
    }
    {
        if(starter.getPredicateName() == &_l1 && startVar < 0){
            if(3 == starter[0]){
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
                        int X1 = tuple1->at(0);
                        int X0 = tuple1->at(1);
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
                            if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
        }
        if(starter.getPredicateName() == &_aux0 && startVar > 0){
            int X1 = starter[0];
            int X0 = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({3},&_l1);
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
                    if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
            int X1 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const std::vector<int>* tuples = &paux0_0_.getValuesVec({X1});
            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux0_0_.getValuesVec({X1});
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
                    if(tupleU->at(0) == X1)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int X0 = tuple1->at(1);
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
                        if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
            int X1 = starter[0];
            int X0 = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({X1},&_l1);
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
                    if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
            int X1 = starter[0];
            int X0 = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            if(X0 == 2 + 2){
                const Tuple* tuple2 = factory.find({3},&_l1);
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
                    const Tuple* tuple3 = factory.find({X1},&_l1);
                    if(tuple3!=NULL){
                        if(tuple3->isFalse())
                        tuple3=NULL;
                        else if(tuple3->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple3;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_l1 || tupleUNegated || !(*tupleU == *tuple3))
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
                            if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
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
        if(starter.getPredicateName() == &_l1 && startVar > 0){
            int X1 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            int X0 = 2 + 2;
            const Tuple* tuple2 = factory.find({3},&_l1);
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
                Tuple negativeTuple({X1,X0},&_aux0);
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
                            if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                        if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
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
            for(auto pair : internalProps)
                propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
        if(starter.getPredicateName() == &_l1 && startVar > 0){
            if(3 == starter[0]){
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                int X0 = 2 + 2;
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
                        int X1 = tuple2->at(0);
                        Tuple negativeTuple({X1,X0},&_aux0);
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
                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
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
    }
    if(starter.getPredicateName() == &_aux1){
        Tuple* head = factory.find({2}, &_l3);
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
    }else if(starter.getPredicateName() == &_l3){
        if(starter.at(0) == 2){
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            Tuple* currentBody = factory.find({}, &_aux1);
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
    }
    {
        if(starter.getPredicateName() == &_l2 && startVar > 0){
            if(2 == starter[0]){
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({},&_aux1);
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
                            shared_reason.get()->insert(it*1);
                        }
                        if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                            int it = tuple1->getId();
                            shared_reason.get()->insert(it*1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_aux1 && startVar > 0){
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            const Tuple* tuple1 = factory.find({2},&_l2);
            if(tuple1!=NULL){
                if(tuple1->isFalse())
                tuple1=NULL;
                else if(tuple1->isUndef()){
                    if(tupleU == NULL){
                        tupleU = tuple1;
                        tupleUNegated=false;
                    }else{
                        if(tupleU->getPredicateName() != &_l2 || tupleUNegated || !(*tupleU == *tuple1))
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
                    if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_aux1 && startVar < 0){
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({2},&_l2);
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
                        if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        shared_reason.get()->insert(it*-1);
                    }
                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_l2 && startVar < 0){
            if(2 == starter[0]){
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({},&_aux1);
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
                            if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                            shared_reason.get()->insert(it*-1);
                        }
                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
    {
        if(starter.getPredicateName() == &_l2 && startVar < 0){
            if(2 == starter[0]){
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
                        int X0 = tuple1->at(0);
                        int X1 = tuple1->at(1);
                        int X2 = tuple1->at(2);
                        const std::vector<int>* tuples = &pl3_.getValuesVec({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ul3_.getValuesVec({});
                        else if(tupleU->getPredicateName() == &_l3 && !tupleUNegated)
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
                                int X3 = tuple2->at(0);
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
                                    if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        if(starter.getPredicateName() == &_l3 && startVar > 0){
            int X3 = starter[0];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({2},&_l2);
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
                        if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        int X0 = tuple2->at(0);
                        int X1 = tuple2->at(1);
                        int X2 = tuple2->at(2);
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
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
        if(starter.getPredicateName() == &_l0 && startVar > 0){
            int X0 = starter[0];
            int X1 = starter[1];
            int X2 = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            std::vector<std::pair<const Tuple*,bool>> internalProps;
            Tuple negativeTuple({2},&_l2);
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
                        if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple1))
                        tuple1=NULL;
                    }
                }
            }
            if(tuple1!=NULL){
                const std::vector<int>* tuples = &pl3_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ul3_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_l3 && !tupleUNegated)
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
                        int X3 = tuple2->at(0);
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
                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            if(tupleU->getPredicateName() != &_l3 && tupleU->getPredicateName() != &_l2 && tupleU->getPredicateName() != &_aux0 && tupleU->getPredicateName() != &_aux1)
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
