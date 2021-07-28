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
const std::string _a = "a";
const std::string _aggr_id0 = "aggr_id0";
const std::string _aggr_id1 = "aggr_id1";
const std::string _aggr_set0 = "aggr_set0";
const std::string _aux0 = "aux0";
const std::string _b = "b";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,VectorAsSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
bool unRoll=false;
Executor::~Executor() {
}


const std::vector<unsigned> EMPTY_TUPLES;
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
AuxMap<0> pb_({});
AuxMap<0> ub_({});
AuxMap<0> fb_({});
AuxMap<0> pa_({});
AuxMap<0> ua_({});
AuxMap<0> fa_({});
AuxMap<32> pb_1_({1});
AuxMap<32> ub_1_({1});
AuxMap<32> fb_1_({1});
AuxMap<96> paux0_0_1_2_({0,1,2});
AuxMap<96> uaux0_0_1_2_({0,1,2});
AuxMap<96> faux0_0_1_2_({0,1,2});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<64> paux0_3_4_({3,4});
AuxMap<64> uaux0_3_4_({3,4});
AuxMap<64> faux0_3_4_({3,4});
AuxMap<32> paux0_1_({1});
AuxMap<32> uaux0_1_({1});
AuxMap<32> faux0_1_({1});
AuxMap<96> paux0_0_2_3_({0,2,3});
AuxMap<96> uaux0_0_2_3_({0,2,3});
AuxMap<96> faux0_0_2_3_({0,2,3});
AuxMap<64> pb_0_2_({0,2});
AuxMap<64> ub_0_2_({0,2});
AuxMap<64> fb_0_2_({0,2});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
void Executor::handleConflict(int literal){
    if(currentDecisionLevel == -1){
        propagatedLiterals.push_back(-1);
        return;
    }

    std::unordered_set<int> visitedLiterals;
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    explainExternalLiteral(literal,conflictReason,visitedLiterals,true);
    explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);
    propagatedLiterals.push_back(-1);
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
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2(*insertResult.first);
        faux0_0_1_2_.insert2(*insertResult.first);
        faux0_0_2_3_.insert2(*insertResult.first);
        faux0_1_.insert2(*insertResult.first);
        faux0_3_4_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_a){
        fa_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_b){
        fb_.insert2(*insertResult.first);
        fb_0_2_.insert2(*insertResult.first);
        fb_1_.insert2(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2(*insertResult.first);
        paux0_0_1_2_.insert2(*insertResult.first);
        paux0_0_2_3_.insert2(*insertResult.first);
        paux0_1_.insert2(*insertResult.first);
        paux0_3_4_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_a){
        pa_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_b){
        pb_.insert2(*insertResult.first);
        pb_0_2_.insert2(*insertResult.first);
        pb_1_.insert2(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2(*insertResult.first);
        uaux0_0_1_2_.insert2(*insertResult.first);
        uaux0_0_2_3_.insert2(*insertResult.first);
        uaux0_1_.insert2(*insertResult.first);
        uaux0_3_4_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_a){
        ua_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_b){
        ub_.insert2(*insertResult.first);
        ub_0_2_.insert2(*insertResult.first);
        ub_1_.insert2(*insertResult.first);
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
    trace_msg(eagerprop, 2, "Literal true received " << minus << tuple->toString());
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
    trace_msg(eagerprop, 2, "Literal True saved");
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    int internalVar = var > 0 ? tuple->getId() : -tuple->getId();
    reasonForLiteral[internalVar].clear();
    std::string minus = var < 0 ? "-" : "";
    trace_msg(eagerprop, 2, "Literal undef received " << minus << tuple->toString());
    const auto& insertResult = tuple->setStatus(Undef);
    if (insertResult.second) {
        factory.removeFromCollisionsList(tuple->getId());
        insertUndef(insertResult);
    }
    if(currentDecisionLevel >= 0){
    }
    trace_msg(eagerprop, 2, "Exit undef");
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    trace_msg(eagerprop,2,"Computing internalUndefined");
    undefinedLoaded=true;
    {
        const std::vector<unsigned>* tuples = &pb_.getValues({});
        const std::vector<unsigned>* tuplesU = &ub_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            int V = tuple->at(1);
            if(tuple->at(2) == X){
                const std::vector<unsigned>* tuples = &pa_.getValues({});
                const std::vector<unsigned>* tuplesU = &ua_.getValues({});
                for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                    const Tuple* tuple = NULL;
                    if(i<tuples->size())
                        tuple=factory.getTupleFromInternalID(tuples->at(i));
                    else
                        tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int Z = tuple->at(0);
                    Tuple* boundTuple = factory.find({Z}, &_a);
                    if(boundTuple == NULL || !boundTuple->isTrue()){
                        const std::vector<unsigned>* tuples = &pb_1_.getValues({X});
                        const std::vector<unsigned>* tuplesU = &ub_1_.getValues({X});
                        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                            const Tuple* tuple = NULL;
                            if(i<tuples->size())
                                tuple=factory.getTupleFromInternalID(tuples->at(i));
                            else
                                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                            int U = tuple->at(0);
                            if(tuple->at(1) == X){
                                int W = tuple->at(2);
                                if(X <= W){
                                    if(W <= U){
                                        Tuple* aux = factory.addNewInternalTuple({W,Z,U,X,V}, &_aux0);
                                        const auto& insertResult = aux->setStatus(Undef);
                                        if (insertResult.second) {
                                            factory.removeFromCollisionsList(aux->getId());
                                            insertUndef(insertResult);
                                            {
                                                Tuple* head = factory.addNewInternalTuple({W,Z,U},&_aggr_set0);
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
                        }
                    }
                }
            }
        }
    }
    trace_msg(eagerprop,2,"Computing aggr id no shared variables");
    {
        Tuple* aggrId = factory.addNewInternalTuple({},&_aggr_id1);
        const auto& insertResult = aggrId->setStatus(Undef);
        if (insertResult.second) {
            factory.removeFromCollisionsList(aggrId->getId());
            insertUndef(insertResult);
        }
    }
    {
        Tuple* aggrId = factory.addNewInternalTuple({},&_aggr_id0);
        const auto& insertResult = aggrId->setStatus(Undef);
        if (insertResult.second) {
            factory.removeFromCollisionsList(aggrId->getId());
            insertUndef(insertResult);
        }
    }
    trace_msg(eagerprop,2,"Computing sums");
    {
        const std::vector<unsigned>* aggregateIds = &uaggr_id0_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
            const std::vector<unsigned>* aggrSetTuples = &uaggr_set0_.getValues({});
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possibleSum[it]+=factory.getTupleFromInternalID(aggrSetTuples->at(j))->at(0);
        }
    }
    {
        const std::vector<unsigned>* aggregateIds = &uaggr_id1_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
            const std::vector<unsigned>* aggrSetTuples = &uaggr_set0_.getValues({});
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possibleSum[it]+=factory.getTupleFromInternalID(aggrSetTuples->at(j))->at(0);
        }
    }
    trace_msg(eagerprop,2,"Interna lUndefined Computed");
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
    paggr_id1_.clear();
    paggr_id0_.clear();
    paggr_set0_.clear();
    faggr_id1_.clear();
    faggr_id0_.clear();
    faggr_set0_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["a"] = &_a;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    stringToUniqueStringPointer["b"] = &_b;
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,std::vector<int> & propagatedLiterals,std::unordered_set<int> & remainingPropagatingLiterals){
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
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        int itAggrId = factory.find({},&_aggr_id0)->getId();
                        actualSum[itAggrId]+=tupleU->at(0);
                        possibleSum[itAggrId]-=tupleU->at(0);
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        int itAggrId = factory.find({},&_aggr_id1)->getId();
                        actualSum[itAggrId]+=tupleU->at(0);
                        possibleSum[itAggrId]-=tupleU->at(0);
                    }
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
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        int itAggrId = factory.find({},&_aggr_id0)->getId();
                        possibleSum[itAggrId]-=tupleU->at(0);
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        int itAggrId = factory.find({},&_aggr_id1)->getId();
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
    trace_msg(eagerprop,2,"Unrolling to level: "<<decisionLevel << " " <<currentDecisionLevel);
    for(int literealToProp : remainingPropagatingLiterals){
        int var = literealToProp > 0 ? literealToProp : -literealToProp;
        int sign = literealToProp > 0 ? -1 : 1;
        Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
        if(literalNotPropagated!=NULL)
            reasonForLiteral[sign*literalNotPropagated->getId()].clear();
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
            if(tuple->getPredicateName() == &_aggr_set0){
                int itAggrId = factory.find({},&_aggr_id0)->getId();
                if(var>0)
                    actualSum[itAggrId]-=tuple->at(0);
                possibleSum[itAggrId]+=tuple->at(0);
            }
            if(tuple->getPredicateName() == &_aggr_set0){
                int itAggrId = factory.find({},&_aggr_id1)->getId();
                if(var>0)
                    actualSum[itAggrId]-=tuple->at(0);
                possibleSum[itAggrId]+=tuple->at(0);
            }
        }
        levelToIntLiterals.erase(currentDecisionLevel);
        currentDecisionLevel--;
    }
    clearConflictReason();
    trace_msg(eagerprop,2,"Unrolling ended");
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts) {
    trace_msg(eagerprop,2,"Computing propagation");
    int decisionLevel = facts[0];
    currentDecisionLevel=decisionLevel;
    clearPropagations();
    std::vector<int> propagationStack;
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
        int factVar = facts[i]>0 ? facts[i] : -facts[i];
        int minus = facts[i]<0 ? -1 : 1;
        propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());
        remainingPropagatingLiterals.erase(-facts[i]);
    }
    if(decisionLevel>-1) {
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            const std::vector<unsigned>* tuples = &paggr_id0_.getValues({});
            const std::vector<unsigned>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<unsigned>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 3){
                    propagatedLiterals.push_back(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= 3) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= 3){
                    propagatedLiterals.push_back(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= 3){
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
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= 3){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 3){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<unsigned>* tuples = &paggr_id1_.getValues({});
            const std::vector<unsigned>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<unsigned>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 3+1){
                    propagatedLiterals.push_back(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= 3+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= 3+1){
                    propagatedLiterals.push_back(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= 3+1){
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
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= 3+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 3+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple0 = factory.find({},&_aggr_id0);
                if(tuple0!=NULL){
                    if(tuple0->isFalse())
                    tuple0=NULL;
                    else if(tuple0->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple0;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_aggr_id0 || tupleUNegated || !(*tupleU == *tuple0))
                            tuple0=NULL;
                        }
                    }
                }
                if(tuple0!=NULL){
                    Tuple negativeTuple({},&_aggr_id1);
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
                                if(tupleU->getPredicateName() != &_aggr_id1 || !tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
                        }
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else{
                            propagatedLiterals.push_back(-1);
                        }
                    }
                }
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<unsigned>* tuples = &pb_.getValues({});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                        if(tuple0->at(0)==tuple0->at(2)){
                            int X = tuple0->at(0);
                            int V = tuple0->at(1);
                            const std::vector<unsigned>* tuples = &pa_.getValues({});
                            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                                    tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                                else if(i<tuples->size()+tuplesU->size()){
                                    tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                    tupleUNegated=false;
                                }else if(!undeRepeated.empty()){
                                    tuple1 = tupleU;
                                }
                                if(tuple1!=NULL){
                                    int Z = tuple1->at(0);
                                    Tuple negativeTuple({Z},&_a);
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
                                                if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple2))
                                                tuple2=NULL;
                                            }
                                        }
                                    }
                                    if(tuple2!=NULL){
                                        const std::vector<unsigned>* tuples = &pb_1_.getValues({X});
                                        const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                                        std::vector<const Tuple*> undeRepeated;
                                        if(tupleU == NULL)
                                            tuplesU = &ub_1_.getValues({X});
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
                                                tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                            else if(i<tuples->size()+tuplesU->size()){
                                                tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                                tupleUNegated=false;
                                            }else if(!undeRepeated.empty()){
                                                if(tupleU->at(1) == X)
                                                    tuple3 = tupleU;
                                            }
                                            if(tuple3!=NULL){
                                                int U = tuple3->at(0);
                                                int W = tuple3->at(2);
                                                if(X <= W){
                                                    if(W <= U){
                                                        Tuple negativeTuple({W,Z,U,X,V},&_aux0);
                                                        const Tuple* tuple6 = factory.find(negativeTuple);
                                                        if(tuple6 == NULL)
                                                            tuple6 = &negativeTuple;
                                                        else{
                                                            if(tuple6->isTrue())
                                                                tuple6 = NULL;
                                                            else if(tuple6->isUndef()){
                                                                if(tupleU == NULL){
                                                                    tupleU = tuple6;
                                                                    tupleUNegated=true;
                                                                }else{
                                                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple6))
                                                                    tuple6=NULL;
                                                                }
                                                            }
                                                        }
                                                        if(tuple6!=NULL){
                                                            if(tupleU != NULL){
                                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                                                            }else{
                                                                propagatedLiterals.push_back(-1);
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
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<unsigned>* tuples = &paux0_.getValues({});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int W = tuple0->at(0);
                        int Z = tuple0->at(1);
                        int U = tuple0->at(2);
                        int X = tuple0->at(3);
                        int V = tuple0->at(4);
                        const Tuple* tuple1 = factory.find({Z},&_a);
                        if(tuple1!=NULL){
                            if(tuple1->isFalse())
                            tuple1=NULL;
                            else if(tuple1->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple1;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_a || tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                propagatedLiterals.push_back(-1);
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
                const std::vector<unsigned>* tuples = &paux0_.getValues({});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int W = tuple0->at(0);
                        int Z = tuple0->at(1);
                        int U = tuple0->at(2);
                        int X = tuple0->at(3);
                        int V = tuple0->at(4);
                        Tuple negativeTuple({U,X,W},&_b);
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
                                    if(tupleU->getPredicateName() != &_b || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                propagatedLiterals.push_back(-1);
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
                const std::vector<unsigned>* tuples = &paux0_.getValues({});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int W = tuple0->at(0);
                        int Z = tuple0->at(1);
                        int U = tuple0->at(2);
                        int X = tuple0->at(3);
                        int V = tuple0->at(4);
                        Tuple negativeTuple({Z},&_a);
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
                                    if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                propagatedLiterals.push_back(-1);
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
                const std::vector<unsigned>* tuples = &paux0_.getValues({});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int W = tuple0->at(0);
                        int Z = tuple0->at(1);
                        int U = tuple0->at(2);
                        int X = tuple0->at(3);
                        int V = tuple0->at(4);
                        Tuple negativeTuple({X,V,X},&_b);
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
                                    if(tupleU->getPredicateName() != &_b || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                propagatedLiterals.push_back(-1);
                            }
                        }
                    }
                }
            }
        }
        {
            const std::vector<unsigned>* trueHeads = &paggr_set0_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
                int W = head->at(0);
                int Z = head->at(1);
                int U = head->at(2);
                const std::vector<unsigned>* tuples = &paux0_0_1_2_.getValues({W,Z,U});
                const std::vector<unsigned>* tuplesU = &uaux0_0_1_2_.getValues({W,Z,U});
                if(tuples->size() == 0){
                    if(tuplesU->size() == 0){
                        propagatedLiterals.push_back(-1);
                    }else if(tuplesU->size() == 1){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }else{
                }
            }
            const std::vector<unsigned>* undefHeads = &uaggr_set0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
                int W = head->at(0);
                int Z = head->at(1);
                int U = head->at(2);
                const std::vector<unsigned>* tuples = &paux0_0_1_2_.getValues({W,Z,U});
                if(tuples->size() == 0){
                    const std::vector<unsigned>* tuplesU = &uaux0_0_1_2_.getValues({W,Z,U});
                    if(tuplesU->size() == 0){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }
            }
            const std::vector<unsigned>* falseHeads = &faggr_set0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
                int W = head->at(0);
                int Z = head->at(1);
                int U = head->at(2);
                const std::vector<unsigned>* tuples = &paux0_0_1_2_.getValues({W,Z,U});
                if(tuples->size() == 0){
                    const std::vector<unsigned>* tuplesU = &uaux0_0_1_2_.getValues({W,Z,U});
                    for(unsigned j = 0; j < tuplesU->size();){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(j)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }else{
                    propagatedLiterals.push_back(-1);
                }
            }
        }
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        std::string minus = startVar < 0 ? "not " : "";
        trace_msg(eagerprop,5,minus << starter.toString() << " as Starter");
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aggr_set0){
            trace_msg(eagerprop,5,"Evaluating rule: 0");
            int W = starter[0];
            int Z = starter[1];
            int U = starter[2];
            const std::vector<unsigned>* tuples = &paux0_0_1_2_.getValues({W,Z,U});
            const std::vector<unsigned>* tuplesU = &uaux0_0_1_2_.getValues({W,Z,U});
            if(startVar > 0){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));
                    int itProp = tuplesU->at(0);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        reasonForLiteral[itProp].insert(startVar);
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }
            }else{
                if(tuples->size()>0){
                    int it = tuples->at(0);
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        int it = tuplesU->back();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux0){
            trace_msg(eagerprop,5,"Evaluating rule: 0");
            int W = starter[0];
            int Z = starter[1];
            int U = starter[2];
            int X = starter[3];
            int V = starter[4];
            if(startVar > 0){
                Tuple* head = factory.find({W,Z,U}, &_aggr_set0);
                if(head == NULL) trace_msg(eagerprop,6,"WARNING: head not in storage");
                if(!head->isTrue() && !head->isUndef()){
                    int it = head->getId();
                    reasonForLiteral[it].insert(startVar);
                    handleConflict(it);
                    return;
                }else if(head->isUndef()){
                    int it = head->getId();
                    if(reasonForLiteral.count(it) == 0  || reasonForLiteral[it].empty())
                        reasonForLiteral[it].insert(startVar);
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }
            }else{
                Tuple* head = factory.find({W,Z,U}, &_aggr_set0);
                const std::vector<unsigned>* tuples = &paux0_0_1_2_.getValues({W,Z,U});
                const std::vector<unsigned>* tuplesU = &uaux0_0_1_2_.getValues({W,Z,U});
                if(head != NULL && head->isTrue()){
                    if(tuples->size()==0 && tuplesU->size()==0){
                        int itHead = head->getId();
                        const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[-itHead].insert(-it);
                        }
                        handleConflict(-itHead);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int it = head->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }else{
                    if(head != NULL && head->isUndef() && tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        if(reasonForLiteral.count(-itHead) == 0  || reasonForLiteral[-itHead].empty()){
                            const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                reasonForLiteral[-itHead].insert(-it);
                            }
                        }
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_set0){
            trace_msg(eagerprop,5,"Evaluating rule: 0");
            int W = starter[0];
            int Z = starter[1];
            int U = starter[2];
            const std::vector<unsigned>* tuples = &paux0_0_1_2_.getValues({W,Z,U});
            const std::vector<unsigned>* tuplesU = &uaux0_0_1_2_.getValues({W,Z,U});
            if(startVar > 0){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size()==1){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));
                    int itProp = tuplesU->at(0);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* tuplesF = &faux0_0_1_2_.getValues({W,Z,U});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        reasonForLiteral[itProp].insert(startVar);
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }
            }else{
                if(tuples->size()>0){
                    int it = tuples->at(0);
                    reasonForLiteral[-it].insert(startVar);
                    handleConflict(-it);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        int it = tuplesU->back();
                        if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                            reasonForLiteral[-it].insert(startVar);
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }
        }//close if starter
        {
            if(starter.getPredicateName() == &_b && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 1");
                if(starter.at(0)==starter.at(2)){
                    int X = starter[0];
                    int V = starter[1];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<unsigned>* tuples = &paux0_3_4_.getValues({X,V});
                    const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_3_4_.getValues({X,V});
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
                            tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            if(tupleU->at(3) == X && tupleU->at(4) == V)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int W = tuple1->at(0);
                            int Z = tuple1->at(1);
                            int U = tuple1->at(2);
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 1");
                int W = starter[0];
                int Z = starter[1];
                int U = starter[2];
                int X = starter[3];
                int V = starter[4];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,V,X},&_b);
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
                            if(tupleU->getPredicateName() != &_b || !tupleUNegated || !(*tupleU == *tuple1))
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_a && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 2");
                int Z = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<unsigned>* tuples = &paux0_1_.getValues({Z});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_1_.getValues({Z});
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
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == Z)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int W = tuple1->at(0);
                        int U = tuple1->at(2);
                        int X = tuple1->at(3);
                        int V = tuple1->at(4);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 2");
                int W = starter[0];
                int Z = starter[1];
                int U = starter[2];
                int X = starter[3];
                int V = starter[4];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({Z},&_a);
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
                            if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple1))
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_b && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 3");
                int U = starter[0];
                int X = starter[1];
                int W = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<unsigned>* tuples = &paux0_0_2_3_.getValues({W,U,X});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_0_2_3_.getValues({W,U,X});
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
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == W && tupleU->at(2) == U && tupleU->at(3) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int Z = tuple1->at(1);
                        int V = tuple1->at(4);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 3");
                int W = starter[0];
                int Z = starter[1];
                int U = starter[2];
                int X = starter[3];
                int V = starter[4];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({U,X,W},&_b);
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
                            if(tupleU->getPredicateName() != &_b || !tupleUNegated || !(*tupleU == *tuple1))
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_a && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 4");
                int Z = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<unsigned>* tuples = &paux0_1_.getValues({Z});
                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_1_.getValues({Z});
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
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == Z)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int W = tuple1->at(0);
                        int U = tuple1->at(2);
                        int X = tuple1->at(3);
                        int V = tuple1->at(4);
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
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_aux0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 4");
                int W = starter[0];
                int Z = starter[1];
                int U = starter[2];
                int X = starter[3];
                int V = starter[4];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({Z},&_a);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_a || tupleUNegated || !(*tupleU == *tuple1))
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
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_aux0 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 5");
                int W = starter[0];
                int Z = starter[1];
                int U = starter[2];
                int X = starter[3];
                int V = starter[4];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                if(X <= W){
                    if(W <= U){
                        const Tuple* tuple3 = factory.find({X,V,X},&_b);
                        if(tuple3!=NULL){
                            if(tuple3->isFalse())
                            tuple3=NULL;
                            else if(tuple3->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple3;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_b || tupleUNegated || !(*tupleU == *tuple3))
                                    tuple3=NULL;
                                }
                            }
                        }
                        if(tuple3!=NULL){
                            const Tuple* tuple4 = factory.find({Z},&_a);
                            if(tuple4!=NULL){
                                if(tuple4->isFalse())
                                tuple4=NULL;
                                else if(tuple4->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple4;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_a || tupleUNegated || !(*tupleU == *tuple4))
                                        tuple4=NULL;
                                    }
                                }
                            }
                            if(tuple4!=NULL){
                                const Tuple* tuple5 = factory.find({U,X,W},&_b);
                                if(tuple5!=NULL){
                                    if(tuple5->isFalse())
                                    tuple5=NULL;
                                    else if(tuple5->isUndef()){
                                        if(tupleU == NULL){
                                            tupleU = tuple5;
                                            tupleUNegated=false;
                                        }else{
                                            if(tupleU->getPredicateName() != &_b || tupleUNegated || !(*tupleU == *tuple5))
                                            tuple5=NULL;
                                        }
                                    }
                                }
                                if(tuple5!=NULL){
                                    Tuple negativeTuple({Z},&_a);
                                    const Tuple* tuple6 = factory.find(negativeTuple);
                                    if(tuple6 == NULL)
                                        tuple6 = &negativeTuple;
                                    else{
                                        if(tuple6->isTrue())
                                            tuple6 = NULL;
                                        else if(tuple6->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple6;
                                                tupleUNegated=true;
                                            }else{
                                                if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple6))
                                                tuple6=NULL;
                                            }
                                        }
                                    }
                                    if(tuple6!=NULL){
                                        if(tupleU != NULL){
                                            int itUndef = tupleU->getId();
                                            int var = tupleUNegated ? 1 : -1;
                                            var*=itUndef;
                                            if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                                {
                                                    int it = starter.getId();
                                                    reasonForLiteral[var].insert(it*-1);
                                                }
                                                if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                    int it = tuple3->getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                                if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                    int it = tuple4->getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                                if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                    int it = tuple5->getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                                if(factory.find(*tuple6) != NULL && tuple6!=tupleU){
                                                    int it = tuple6->getId();
                                                    reasonForLiteral[var].insert(it*-1);
                                                }
                                            }else{
                                            }
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
                                                reasonForLiteral[-startVar].insert(it*1);
                                            }
                                            if(tuple6!=NULL){
                                                int it = tuple6->getId();
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
            if(starter.getPredicateName() == &_a && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 5");
                int Z = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({Z},&_a);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_a || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const std::vector<unsigned>* tuples = &pb_.getValues({});
                    const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                            if(tuple2->at(0)==tuple2->at(2)){
                                int X = tuple2->at(0);
                                int V = tuple2->at(1);
                                const std::vector<unsigned>* tuples = &pb_1_.getValues({X});
                                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ub_1_.getValues({X});
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
                                        tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == X)
                                            tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int U = tuple3->at(0);
                                        int W = tuple3->at(2);
                                        if(X <= W){
                                            if(W <= U){
                                                Tuple negativeTuple({W,Z,U,X,V},&_aux0);
                                                const Tuple* tuple6 = factory.find(negativeTuple);
                                                if(tuple6 == NULL)
                                                    tuple6 = &negativeTuple;
                                                else{
                                                    if(tuple6->isTrue())
                                                        tuple6 = NULL;
                                                    else if(tuple6->isUndef()){
                                                        if(tupleU == NULL){
                                                            tupleU = tuple6;
                                                            tupleUNegated=true;
                                                        }else{
                                                            if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple6))
                                                            tuple6=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple6!=NULL){
                                                    if(tupleU != NULL){
                                                        int itUndef = tupleU->getId();
                                                        int var = tupleUNegated ? 1 : -1;
                                                        var*=itUndef;
                                                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                                            {
                                                                int it = starter.getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                                                int it = tuple1->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                                int it = tuple2->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                                int it = tuple3->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple6) != NULL && tuple6!=tupleU){
                                                                int it = tuple6->getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                        }else{
                                                        }
                                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
                                                        if(tuple6!=NULL){
                                                            int it = tuple6->getId();
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
            }
            if(starter.getPredicateName() == &_b && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 5");
                int U = starter[0];
                int X = starter[1];
                int W = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                if(X <= W){
                    if(W <= U){
                        const std::vector<unsigned>* tuples = &pb_0_2_.getValues({X,X});
                        const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ub_0_2_.getValues({X,X});
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
                                tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == X && tupleU->at(2) == X)
                                    tuple3 = tupleU;
                            }
                            if(tuple3!=NULL){
                                if(tuple3->at(0)==tuple3->at(2)){
                                    int V = tuple3->at(1);
                                    const std::vector<unsigned>* tuples = &pa_.getValues({});
                                    const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                                        const Tuple* tuple4 = NULL;
                                        if(i<tuples->size())
                                            tuple4 = factory.getTupleFromInternalID(tuples->at(i));
                                        else if(i<tuples->size()+tuplesU->size()){
                                            tupleU = tuple4 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                            tupleUNegated=false;
                                        }else if(!undeRepeated.empty()){
                                            tuple4 = tupleU;
                                        }
                                        if(tuple4!=NULL){
                                            int Z = tuple4->at(0);
                                            Tuple negativeTuple({Z},&_a);
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
                                                        if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple5))
                                                        tuple5=NULL;
                                                    }
                                                }
                                            }
                                            if(tuple5!=NULL){
                                                Tuple negativeTuple({W,Z,U,X,V},&_aux0);
                                                const Tuple* tuple6 = factory.find(negativeTuple);
                                                if(tuple6 == NULL)
                                                    tuple6 = &negativeTuple;
                                                else{
                                                    if(tuple6->isTrue())
                                                        tuple6 = NULL;
                                                    else if(tuple6->isUndef()){
                                                        if(tupleU == NULL){
                                                            tupleU = tuple6;
                                                            tupleUNegated=true;
                                                        }else{
                                                            if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple6))
                                                            tuple6=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple6!=NULL){
                                                    if(tupleU != NULL){
                                                        int itUndef = tupleU->getId();
                                                        int var = tupleUNegated ? 1 : -1;
                                                        var*=itUndef;
                                                        if(reasonForLiteral.count(var) == 0 || reasonForLiteral[var].empty()){
                                                            {
                                                                int it = starter.getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                                int it = tuple3->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                                int it = tuple4->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple5) != NULL && tuple5!=tupleU){
                                                                int it = tuple5->getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                            if(factory.find(*tuple6) != NULL && tuple6!=tupleU){
                                                                int it = tuple6->getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                        }else{
                                                        }
                                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
                                                        if(tuple6!=NULL){
                                                            int it = tuple6->getId();
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
            }
            if(starter.getPredicateName() == &_a && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 5");
                int Z = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({Z},&_a);
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
                            if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const std::vector<unsigned>* tuples = &pb_.getValues({});
                    const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                            if(tuple2->at(0)==tuple2->at(2)){
                                int X = tuple2->at(0);
                                int V = tuple2->at(1);
                                const std::vector<unsigned>* tuples = &pb_1_.getValues({X});
                                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ub_1_.getValues({X});
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
                                        tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == X)
                                            tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int U = tuple3->at(0);
                                        int W = tuple3->at(2);
                                        if(X <= W){
                                            if(W <= U){
                                                Tuple negativeTuple({W,Z,U,X,V},&_aux0);
                                                const Tuple* tuple6 = factory.find(negativeTuple);
                                                if(tuple6 == NULL)
                                                    tuple6 = &negativeTuple;
                                                else{
                                                    if(tuple6->isTrue())
                                                        tuple6 = NULL;
                                                    else if(tuple6->isUndef()){
                                                        if(tupleU == NULL){
                                                            tupleU = tuple6;
                                                            tupleUNegated=true;
                                                        }else{
                                                            if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple6))
                                                            tuple6=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple6!=NULL){
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
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                                int it = tuple2->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                                int it = tuple3->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple6) != NULL && tuple6!=tupleU){
                                                                int it = tuple6->getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                        }else{
                                                        }
                                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
                                                        if(tuple6!=NULL){
                                                            int it = tuple6->getId();
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
            }
            if(starter.getPredicateName() == &_b && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 5");
                if(starter.at(0)==starter.at(2)){
                    int X = starter[0];
                    int V = starter[1];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<unsigned>* tuples = &pa_.getValues({});
                    const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                            tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int Z = tuple1->at(0);
                            Tuple negativeTuple({Z},&_a);
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
                                        if(tupleU->getPredicateName() != &_a || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
                                const std::vector<unsigned>* tuples = &pb_1_.getValues({X});
                                const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &ub_1_.getValues({X});
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
                                        tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == X)
                                            tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int U = tuple3->at(0);
                                        int W = tuple3->at(2);
                                        if(X <= W){
                                            if(W <= U){
                                                Tuple negativeTuple({W,Z,U,X,V},&_aux0);
                                                const Tuple* tuple6 = factory.find(negativeTuple);
                                                if(tuple6 == NULL)
                                                    tuple6 = &negativeTuple;
                                                else{
                                                    if(tuple6->isTrue())
                                                        tuple6 = NULL;
                                                    else if(tuple6->isUndef()){
                                                        if(tupleU == NULL){
                                                            tupleU = tuple6;
                                                            tupleUNegated=true;
                                                        }else{
                                                            if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple6))
                                                            tuple6=NULL;
                                                        }
                                                    }
                                                }
                                                if(tuple6!=NULL){
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
                                                            if(factory.find(*tuple2) != NULL && tuple2!=tupleU){
                                                                int it = tuple2->getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                            if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                                                int it = tuple3->getId();
                                                                reasonForLiteral[var].insert(it*1);
                                                            }
                                                            if(factory.find(*tuple6) != NULL && tuple6!=tupleU){
                                                                int it = tuple6->getId();
                                                                reasonForLiteral[var].insert(it*-1);
                                                            }
                                                        }else{
                                                        }
                                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
                                                            reasonForLiteral[-startVar].insert(it*1);
                                                        }
                                                        if(tuple6!=NULL){
                                                            int it = tuple6->getId();
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
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            std::vector<int> sharedVar({});
            const std::vector<unsigned>* tuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<unsigned>* tuplesU = &uaggr_set0_.getValues(sharedVar);
            if(startVar < 0){
                if(actualSum[uStartVar]>=3){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(int index=0; index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+currentTuple->at(0) >= 3){
                            int itProp =currentTuple->getId();
                            if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].empty()){
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        int it = tuples->at(i);
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
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < 3){
                    const std::vector<unsigned>* tuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-currentTuple->at(0) < 3){
                            int itProp = tuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                                const std::vector<unsigned>* tuplesF = &faggr_set0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<unsigned>* tuples = &paggr_id0_.getValues({});
            const std::vector<unsigned>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<unsigned>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 3){
                    int itProp = tuples->at(i);
                    const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= 3) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= 3){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= 3){
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
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= 3){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 3){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        if(starter.getPredicateName() == &_aggr_id1){
            std::vector<int> sharedVar({});
            const std::vector<unsigned>* tuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<unsigned>* tuplesU = &uaggr_set0_.getValues(sharedVar);
            if(startVar < 0){
                if(actualSum[uStartVar]>=3+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(int index=0; index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+currentTuple->at(0) >= 3+1){
                            int itProp =currentTuple->getId();
                            if(reasonForLiteral.count(-itProp)==0 || reasonForLiteral[-itProp].empty()){
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        int it = tuples->at(i);
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
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < 3+1){
                    const std::vector<unsigned>* tuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-currentTuple->at(0) < 3+1){
                            int itProp = tuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                                const std::vector<unsigned>* tuplesF = &faggr_set0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<unsigned>* tuples = &paggr_id1_.getValues({});
            const std::vector<unsigned>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<unsigned>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 3+1){
                    int itProp = tuples->at(i);
                    const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= 3+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= 3+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index);
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= 3+1){
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
                            propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                std::vector<int> sharedVar({});
                const std::vector<unsigned>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<unsigned>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= 3+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 3+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j);
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id1 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 8");
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({},&_aggr_id0);
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                            if(factory.find(*tuple1) != NULL && tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
            if(starter.getPredicateName() == &_aggr_id0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 8");
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({},&_aggr_id1);
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
                            if(tupleU->getPredicateName() != &_aggr_id1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
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
    }
    trace_msg(eagerprop,2,"Propagations computed");
}
}
