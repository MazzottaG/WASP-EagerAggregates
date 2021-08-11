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
const std::string _iteration = "iteration";
const std::string _select = "select";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,VectorAsSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
bool unRoll=false;
Executor::~Executor() {
}


const std::vector<int> EMPTY_TUPLES;
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
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<0> pselect_({});
AuxMap<0> uselect_({});
AuxMap<0> fselect_({});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<32> paggr_id0_0_({0});
AuxMap<32> uaggr_id0_0_({0});
AuxMap<32> faggr_id0_0_({0});
AuxMap<32> paggr_set0_1_({1});
AuxMap<32> uaggr_set0_1_({1});
AuxMap<32> faggr_set0_1_({1});
AuxMap<0> piteration_({});
AuxMap<0> uiteration_({});
AuxMap<0> fiteration_({});
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
    reasonForLiteral[literal].clear();
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
        unsigned currentReasonSize=reasonForLiteral[lit].size();
        for(unsigned i = 0; i<currentReasonSize; i++){
            int reasonLiteral=reasonForLiteral[lit][i];
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
    if(insertResult.first->getPredicateName() == &_iteration){
        fiteration_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
        faggr_id0_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_select){
        fselect_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
        faggr_set0_1_.insert2(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_iteration){
        piteration_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
        paggr_id0_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_select){
        pselect_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
        paggr_set0_1_.insert2(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_iteration){
        uiteration_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
        uaggr_id0_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_select){
        uselect_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
        uaggr_set0_1_.insert2(*insertResult.first);
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
    reasonForLiteral[internalVar].clear();
    std::string minus = var < 0 ? "-" : "";
    const auto& insertResult = tuple->setStatus(Undef);
    if (insertResult.second) {
        factory.removeFromCollisionsList(tuple->getId());
        insertUndef(insertResult);
    }
    if(currentDecisionLevel >= 0){
    }
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {
        const std::vector<int>* tuples = &pselect_.getValues({});
        const std::vector<int>* tuplesU = &uselect_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
                Tuple* head = factory.addNewInternalTuple({tuple->at(0),tuple->at(1)},&_aggr_set0);
                const auto& insertResult = head->setStatus(True);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(head->getId());
                    insertTrue(insertResult);
                }
            }else{
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                Tuple* head = factory.addNewInternalTuple({tuple->at(0),tuple->at(1)},&_aggr_set0);
                const auto& insertResult = head->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(head->getId());
                    insertUndef(insertResult);
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &piteration_.getValues({});
        const std::vector<int>* tuplesU = &uiteration_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            }else{
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            }
            Tuple* head = factory.addNewInternalTuple({tuple->at(0)},&_aggr_id0);
            const auto& insertResult = head->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertUndef(insertResult);
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
    paggr_id0_.clear();
    paggr_id0_0_.clear();
    paggr_set0_.clear();
    paggr_set0_1_.clear();
    faggr_id0_.clear();
    faggr_id0_0_.clear();
    faggr_set0_.clear();
    faggr_set0_1_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["iteration"] = &_iteration;
    stringToUniqueStringPointer["select"] = &_select;
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,std::vector<int> & propagatedLiterals,std::unordered_set<int> & remainingPropagatingLiterals,const Solver* solver,PropComparator& propComparison){
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
        }
    }
    return false;
}
void Executor::printInternalLiterals(){
}
void Executor::unRollToLevel(int decisionLevel){
    for(int literealToProp : remainingPropagatingLiterals){
        int var = literealToProp > 0 ? literealToProp : -literealToProp;
        Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
        int internalLit = literealToProp > 0 ? literalNotPropagated->getId() : -literalNotPropagated->getId();
        if(literalNotPropagated!=NULL)
            reasonForLiteral[internalLit].clear();
    }
    remainingPropagatingLiterals.clear();
    while(currentDecisionLevel > decisionLevel){
        while(!levelToIntLiterals[currentDecisionLevel].empty()){
            int var = levelToIntLiterals[currentDecisionLevel].back();
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral[var].clear();
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
            const std::vector<int>* trueHeads = &paggr_set0_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
                int J = head->at(0);
                int I = head->at(1);
                const Tuple* tuple = factory.find({J,I},&_select);
                if(!tuple->isTrue()){
                    if(!tuple->isUndef()){
                        propagatedLiterals.push_back(1);
                    }else{
                        propUndefined(tuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }else{
                }
            }
            const std::vector<int>* undefHeads = &uaggr_set0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
                int J = head->at(0);
                int I = head->at(1);
                const Tuple* tuple = factory.find({J,I},&_select);
                if(!tuple->isTrue()){
                    if(!tuple->isUndef()){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                }
            }
            const std::vector<int>* falseHeads = &faggr_set0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
                int J = head->at(0);
                int I = head->at(1);
                const Tuple* tuple = factory.find({J,I},&_select);
                if(!tuple->isTrue()){
                    if(tuple->isUndef()){
                        propUndefined(tuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }else{
                    propagatedLiterals.push_back(1);
                }
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int I = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() + joinTuplesU->size() == 1+1){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int I = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(joinTuples->size() >= 1+1){
                    propagatedLiterals.push_back(1);
                }else if(joinTuples->size() == 1+1 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));
                        if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i);
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i);
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int I = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                }else if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &piteration_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uiteration_.getValues({});
                else if(tupleU->getPredicateName() == &_iteration && !tupleUNegated)
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int I = tuple0->at(0);
                        const Tuple* tuple1 = factory.find({I},&_aggr_id0);
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
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                            }else{
                                propagatedLiterals.push_back(1);
                            }
                        }
                    }
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
        if(starter.getPredicateName() == &_aggr_set0){
            int J = starter[0];
            int I = starter[1];
            const Tuple* tuple = factory.find({J,I}, &_select);
            if(startVar > 0){
                if(tuple->isFalse()){
                    int it = tuple->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it, propagatedLiterals);
                    return;
                }else{
                    if(tuple->isUndef()){
                        int it = tuple->getId();
                        if(reasonForLiteral.count(it) == 0 || reasonForLiteral[it].empty())
                            reasonForLiteral[it].insert(startVar);
                        propUndefined(tuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }else{
                if(tuple->isTrue()){
                    int it = tuple->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(tuple->isUndef()){
                        int it = tuple->getId();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(tuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_select){
            int J = starter[0];
            int I = starter[1];
            if(startVar > 0){
                Tuple* head = factory.find({J,I}, &_aggr_set0);
                if(!head->isTrue() && !head->isUndef()){
                    int it = head->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it, propagatedLiterals);
                    return;
                }else if(head->isUndef()){
                    int it = head->getId();
                    if(reasonForLiteral.count(it) == 0  || reasonForLiteral[it].empty())
                        reasonForLiteral[it].insert(startVar);
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                }
            }else{
                Tuple* head = factory.find({J,I}, &_aggr_set0);
                if(head != NULL && head->isTrue()){
                    int it = head->getId();
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it, propagatedLiterals);
                    return;
                }else{
                    if(head != NULL && head->isUndef()){
                        int it = head->getId();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            int I = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<int>* tuples = &paggr_set0_1_.getValues(sharedVar);
            const std::vector<int>* tuplesU = &uaggr_set0_1_.getValues(sharedVar);
            if(startVar < 0){
                if(tuples->size()>=1+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() == 1+1 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].empty()){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 1+1){
                    const std::vector<int>* tuplesF = &faggr_set0_1_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else if(tuples->size() + tuplesU->size() == 1+1){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* tuplesF = &faggr_set0_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int I = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 1+1){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int I = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else if(joinTuples->size() == 1+1 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));
                        if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i);
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i);
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int I = currentTuple->at(0);
                std::vector<int> sharedVar({currentTuple->at(0)});
                const std::vector<int>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(joinTuples->size() >= 1+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                }else if(joinTuples->size() + joinTuplesU->size() < 1+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id0 && startVar > 0){
                int I = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({I},&_iteration);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_iteration || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_iteration && startVar > 0){
                int I = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({I},&_aggr_id0);
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
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }
                }
            }
        }
    }
}
}
