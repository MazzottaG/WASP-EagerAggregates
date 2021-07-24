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
const std::string _aggr_id1 = "aggr_id1";
const std::string _aggr_set0 = "aggr_set0";
const std::string _assign = "assign";
const std::string _body0 = "body0";
const std::string _body1 = "body1";
const std::string _component = "component";
const std::string _user = "user";
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
AuxMap<0> passign_({});
AuxMap<0> uassign_({});
AuxMap<0> fassign_({});
AuxMap<32> pcomponent_0_({0});
AuxMap<32> ucomponent_0_({0});
AuxMap<32> fcomponent_0_({0});
AuxMap<64> puser_0_1_({0,1});
AuxMap<64> uuser_0_1_({0,1});
AuxMap<64> fuser_0_1_({0,1});
AuxMap<0> pbody0_({});
AuxMap<0> ubody0_({});
AuxMap<0> fbody0_({});
AuxMap<0> puser_({});
AuxMap<0> uuser_({});
AuxMap<0> fuser_({});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<64> paggr_set0_1_2_({1,2});
AuxMap<64> uaggr_set0_1_2_({1,2});
AuxMap<64> faggr_set0_1_2_({1,2});
AuxMap<0> pcomponent_({});
AuxMap<0> ucomponent_({});
AuxMap<0> fcomponent_({});
AuxMap<64> paggr_set0_0_1_({0,1});
AuxMap<64> uaggr_set0_0_1_({0,1});
AuxMap<64> faggr_set0_0_1_({0,1});
AuxMap<32> passign_0_({0});
AuxMap<32> uassign_0_({0});
AuxMap<32> fassign_0_({0});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<32> paggr_id0_1_({1});
AuxMap<32> uaggr_id0_1_({1});
AuxMap<32> faggr_id0_1_({1});
AuxMap<32> paggr_set0_2_({2});
AuxMap<32> uaggr_set0_2_({2});
AuxMap<32> faggr_set0_2_({2});
AuxMap<64> puser_0_2_({0,2});
AuxMap<64> uuser_0_2_({0,2});
AuxMap<64> fuser_0_2_({0,2});
AuxMap<0> pbody1_({});
AuxMap<0> ubody1_({});
AuxMap<0> fbody1_({});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<32> paggr_id1_1_({1});
AuxMap<32> uaggr_id1_1_({1});
AuxMap<32> faggr_id1_1_({1});
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
    if(insertResult.first->getPredicateName() == &_body1){
        fbody1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2(*insertResult.first);
        faggr_id1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
        faggr_id0_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2(*insertResult.first);
        faggr_set0_0_1_.insert2(*insertResult.first);
        faggr_set0_1_2_.insert2(*insertResult.first);
        faggr_set0_2_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        fbody0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        fuser_.insert2(*insertResult.first);
        fuser_0_1_.insert2(*insertResult.first);
        fuser_0_2_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_component){
        fcomponent_.insert2(*insertResult.first);
        fcomponent_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        fassign_.insert2(*insertResult.first);
        fassign_0_.insert2(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_body1){
        pbody1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2(*insertResult.first);
        paggr_id1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
        paggr_id0_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2(*insertResult.first);
        paggr_set0_0_1_.insert2(*insertResult.first);
        paggr_set0_1_2_.insert2(*insertResult.first);
        paggr_set0_2_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        pbody0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        puser_.insert2(*insertResult.first);
        puser_0_1_.insert2(*insertResult.first);
        puser_0_2_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_component){
        pcomponent_.insert2(*insertResult.first);
        pcomponent_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        passign_.insert2(*insertResult.first);
        passign_0_.insert2(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_body1){
        ubody1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2(*insertResult.first);
        uaggr_id1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
        uaggr_id0_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2(*insertResult.first);
        uaggr_set0_0_1_.insert2(*insertResult.first);
        uaggr_set0_1_2_.insert2(*insertResult.first);
        uaggr_set0_2_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        ubody0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_user){
        uuser_.insert2(*insertResult.first);
        uuser_0_1_.insert2(*insertResult.first);
        uuser_0_2_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_component){
        ucomponent_.insert2(*insertResult.first);
        ucomponent_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_assign){
        uassign_.insert2(*insertResult.first);
        uassign_0_.insert2(*insertResult.first);
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
    const std::vector<unsigned>* tuples = &passign_.getValues({});
    const std::vector<unsigned>* tuplesU = &uassign_.getValues({});
    for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
        const Tuple* tuple = NULL;
        if(i<tuples->size())
            tuple=factory.getTupleFromInternalID(tuples->at(i));
        else
            tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
        int C = tuple->at(0);
        int U = tuple->at(1);
        const std::vector<unsigned>* tuples = &pcomponent_0_.getValues({C});
        const std::vector<unsigned>* tuplesU = &ucomponent_0_.getValues({C});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            if(tuple->at(0) == C){
                int P = tuple->at(1);
                Tuple* aux = factory.addNewInternalTuple({P,C,U}, &_aggr_set0);
                const auto& insertResult = aux->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(aux->getId());
                    insertUndef(insertResult);
                }
            }
        }
    }
}
{
    const std::vector<unsigned>* tuples = &puser_.getValues({});
    const std::vector<unsigned>* tuplesU = &uuser_.getValues({});
    for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
        const Tuple* tuple = NULL;
        if(i<tuples->size()){
            tuple=factory.getTupleFromInternalID(tuples->at(i));
            Tuple* head = factory.addNewInternalTuple({tuple->at(2),tuple->at(0)},&_body1);
            const auto& insertResult = head->setStatus(True);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertTrue(insertResult);
            }
        }else{
            tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            Tuple* head = factory.addNewInternalTuple({tuple->at(2),tuple->at(0)},&_body1);
            const auto& insertResult = head->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertUndef(insertResult);
                trace_msg(eagerprop,3,"Saved new undef head for body1: " << head->toString());
            }
        }
        {
            Tuple* aggrId = factory.addNewInternalTuple({tuple->at(2),tuple->at(0)},&_aggr_id1);
            const auto& insertResult = aggrId->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(aggrId->getId());
                insertUndef(insertResult);
            }
        }
    }
}
{
    const std::vector<unsigned>* tuples = &puser_.getValues({});
    const std::vector<unsigned>* tuplesU = &uuser_.getValues({});
    for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
        const Tuple* tuple = NULL;
        if(i<tuples->size()){
            tuple=factory.getTupleFromInternalID(tuples->at(i));
            Tuple* head = factory.addNewInternalTuple({tuple->at(1),tuple->at(0)},&_body0);
            const auto& insertResult = head->setStatus(True);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertTrue(insertResult);
            }
        }else{
            tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            Tuple* head = factory.addNewInternalTuple({tuple->at(1),tuple->at(0)},&_body0);
            const auto& insertResult = head->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(head->getId());
                insertUndef(insertResult);
                trace_msg(eagerprop,3,"Saved new undef head for body0: " << head->toString());
            }
        }
        {
            Tuple* aggrId = factory.addNewInternalTuple({tuple->at(1),tuple->at(0)},&_aggr_id0);
            const auto& insertResult = aggrId->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(aggrId->getId());
                insertUndef(insertResult);
            }
        }
    }
}
trace_msg(eagerprop,2,"Computing aggr id no shared variables");
trace_msg(eagerprop,2,"Computing sums");
{
    const std::vector<unsigned>* aggregateIds = &uaggr_id0_.getValues({});
    for(unsigned i=0;i<aggregateIds->size();i++){
        int it = aggregateIds->at(i);
        const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
        const std::vector<unsigned>* aggrSetTuples = &uaggr_set0_2_.getValues({currentTuple->at(1)});
        for(unsigned j=0; j<aggrSetTuples->size(); j++)
            possibleSum[it]+=factory.getTupleFromInternalID(aggrSetTuples->at(j))->at(0);
    }
}
{
    const std::vector<unsigned>* aggregateIds = &uaggr_id1_.getValues({});
    for(unsigned i=0;i<aggregateIds->size();i++){
        int it = aggregateIds->at(i);
        const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
        const std::vector<unsigned>* aggrSetTuples = &uaggr_set0_2_.getValues({currentTuple->at(1)});
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
pbody1_.clear();
paggr_id1_.clear();
paggr_id1_1_.clear();
paggr_id0_.clear();
paggr_id0_1_.clear();
pbody0_.clear();
fbody1_.clear();
faggr_id1_.clear();
faggr_id1_1_.clear();
faggr_id0_.clear();
faggr_id0_1_.clear();
fbody0_.clear();
}
void Executor::init() {
stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
stringToUniqueStringPointer["assign"] = &_assign;
stringToUniqueStringPointer["body0"] = &_body0;
stringToUniqueStringPointer["body1"] = &_body1;
stringToUniqueStringPointer["component"] = &_component;
stringToUniqueStringPointer["user"] = &_user;
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){
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
                    {
                        const std::vector<unsigned>* aggrIds = &paggr_id0_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            actualSum[itAggrId]+=tupleU->at(0);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &uaggr_id0_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            actualSum[itAggrId]+=tupleU->at(0);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &faggr_id0_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            actualSum[itAggrId]+=tupleU->at(0);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                }
                if(tupleU->getPredicateName() == &_aggr_set0){
                    {
                        const std::vector<unsigned>* aggrIds = &paggr_id1_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            actualSum[itAggrId]+=tupleU->at(0);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &uaggr_id1_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            actualSum[itAggrId]+=tupleU->at(0);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &faggr_id1_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            actualSum[itAggrId]+=tupleU->at(0);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
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
                    {
                        const std::vector<unsigned>* aggrIds = &paggr_id0_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &uaggr_id0_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &faggr_id0_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                }
                if(tupleU->getPredicateName() == &_aggr_set0){
                    {
                        const std::vector<unsigned>* aggrIds = &paggr_id1_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &uaggr_id1_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
                    {
                        const std::vector<unsigned>* aggrIds = &faggr_id1_1_.getValues({tupleU->at(2)});
                        for(unsigned i=0;i<aggrIds->size();i++){
                            int itAggrId = aggrIds->at(i);
                            possibleSum[itAggrId]-=tupleU->at(0);
                        }
                    }
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
factory.printSize();
std::cout<<"On answerset:"<<reasonForLiteral.size()<<std::endl;
}
void Executor::unRollToLevel(int decisionLevel){
trace_msg(eagerprop,2,"Unrolling to level: "<<decisionLevel << " " <<currentDecisionLevel);
for(unsigned i = 0; i<propagatedLiterals.size(); i++){
    int var = propagatedLiterals[i] > 0 ? propagatedLiterals[i] : -propagatedLiterals[i];
    int sign = propagatedLiterals[i] > 0 ? -1 : 1;
    Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
    if(literalNotPropagated!=NULL)
        reasonForLiteral[sign*literalNotPropagated->getId()].clear();
}
propagatedLiterals.clear();
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
            {
                const std::vector<unsigned>* aggrIds = &paggr_id0_1_.getValues({tuple->at(2)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<unsigned>* aggrIds = &uaggr_id0_1_.getValues({tuple->at(2)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<unsigned>* aggrIds = &faggr_id0_1_.getValues({tuple->at(2)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
        }
        if(tuple->getPredicateName() == &_aggr_set0){
            {
                const std::vector<unsigned>* aggrIds = &paggr_id1_1_.getValues({tuple->at(2)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<unsigned>* aggrIds = &uaggr_id1_1_.getValues({tuple->at(2)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<unsigned>* aggrIds = &faggr_id1_1_.getValues({tuple->at(2)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
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
    if(propagatedLiterals.contains(-facts[i])) propagatedLiterals.erase(-facts[i]);
}
if(decisionLevel>-1) {
}
if(decisionLevel==-1) {
    if(!undefinedLoaded)
        undefLiteralsReceived();
    {
        const std::vector<unsigned>* trueHeads = &pbody0_.getValues({});
        for(unsigned i = 0; i < trueHeads->size(); i++){
            const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
            int MIN = head->at(0);
            int U = head->at(1);
            const std::vector<unsigned>* tuples = &puser_0_1_.getValues({U,MIN});
            const std::vector<unsigned>* tuplesU = &uuser_0_1_.getValues({U,MIN});
            if(tuples->size() == 0){
                if(tuplesU->size() == 0){
                    propagatedLiterals.insert(-1);
                }else if(tuplesU->size() == 1){
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals);
                }
            }else{
            }
        }
        const std::vector<unsigned>* undefHeads = &ubody0_.getValues({});
        for(unsigned i = 0; i < undefHeads->size(); i++){
            const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
            int MIN = head->at(0);
            int U = head->at(1);
            const std::vector<unsigned>* tuples = &puser_0_1_.getValues({U,MIN});
            if(tuples->size() == 0){
                const std::vector<unsigned>* tuplesU = &uuser_0_1_.getValues({U,MIN});
                if(tuplesU->size() == 0){
                    propUndefined(head,false,propagationStack,true,propagatedLiterals);
                }
            }else{
                propUndefined(head,false,propagationStack,false,propagatedLiterals);
            }
        }
        const std::vector<unsigned>* falseHeads = &fbody0_.getValues({});
        for(unsigned i = 0; i < falseHeads->size(); i++){
            const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
            int MIN = head->at(0);
            int U = head->at(1);
            const std::vector<unsigned>* tuples = &puser_0_1_.getValues({U,MIN});
            if(tuples->size() == 0){
                const std::vector<unsigned>* tuplesU = &uuser_0_1_.getValues({U,MIN});
                for(unsigned j = 0; j < tuplesU->size();){
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(j)),false,propagationStack,true,propagatedLiterals);
                }
            }else{
                propagatedLiterals.insert(-1);
            }
        }
    }
    {
        const std::vector<unsigned>* trueHeads = &pbody1_.getValues({});
        for(unsigned i = 0; i < trueHeads->size(); i++){
            const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
            int MAX = head->at(0);
            int U = head->at(1);
            const std::vector<unsigned>* tuples = &puser_0_2_.getValues({U,MAX});
            const std::vector<unsigned>* tuplesU = &uuser_0_2_.getValues({U,MAX});
            if(tuples->size() == 0){
                if(tuplesU->size() == 0){
                    propagatedLiterals.insert(-1);
                }else if(tuplesU->size() == 1){
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals);
                }
            }else{
            }
        }
        const std::vector<unsigned>* undefHeads = &ubody1_.getValues({});
        for(unsigned i = 0; i < undefHeads->size(); i++){
            const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
            int MAX = head->at(0);
            int U = head->at(1);
            const std::vector<unsigned>* tuples = &puser_0_2_.getValues({U,MAX});
            if(tuples->size() == 0){
                const std::vector<unsigned>* tuplesU = &uuser_0_2_.getValues({U,MAX});
                if(tuplesU->size() == 0){
                    propUndefined(head,false,propagationStack,true,propagatedLiterals);
                }
            }else{
                propUndefined(head,false,propagationStack,false,propagatedLiterals);
            }
        }
        const std::vector<unsigned>* falseHeads = &fbody1_.getValues({});
        for(unsigned i = 0; i < falseHeads->size(); i++){
            const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
            int MAX = head->at(0);
            int U = head->at(1);
            const std::vector<unsigned>* tuples = &puser_0_2_.getValues({U,MAX});
            if(tuples->size() == 0){
                const std::vector<unsigned>* tuplesU = &uuser_0_2_.getValues({U,MAX});
                for(unsigned j = 0; j < tuplesU->size();){
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(j)),false,propagationStack,true,propagatedLiterals);
                }
            }else{
                propagatedLiterals.insert(-1);
            }
        }
    }
    {
        {
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<unsigned>* tuples = &pbody1_.getValues({});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                    tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                else if(i<tuples->size()+tuplesU->size()){
                    tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    tupleUNegated=false;
                }else if(!undeRepeated.empty()){
                    tuple0 = tupleU;
                }
                if(tuple0!=NULL){
                    int MAX = tuple0->at(0);
                    int U = tuple0->at(1);
                    const Tuple* tuple1 = factory.find({MAX,U},&_aggr_id1);
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
            const std::vector<unsigned>* tuples = &pbody0_.getValues({});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
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
                    tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                else if(i<tuples->size()+tuplesU->size()){
                    tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    tupleUNegated=false;
                }else if(!undeRepeated.empty()){
                    tuple0 = tupleU;
                }
                if(tuple0!=NULL){
                    int MIN = tuple0->at(0);
                    int U = tuple0->at(1);
                    Tuple negativeTuple({MIN,U},&_aggr_id0);
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
            const std::vector<unsigned>* tuples = &passign_.getValues({});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uassign_.getValues({});
            else if(tupleU->getPredicateName() == &_assign && !tupleUNegated)
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
                    int C = tuple0->at(0);
                    int U = tuple0->at(1);
                    const std::vector<unsigned>* tuples = &pcomponent_0_.getValues({C});
                    const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ucomponent_0_.getValues({C});
                    else if(tupleU->getPredicateName() == &_component && !tupleUNegated)
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
                            if(tupleU->at(0) == C)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int P = tuple1->at(1);
                            Tuple negativeTuple({P,C,U},&_aggr_set0);
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
                                        if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
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
    }
    {
        {
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<unsigned>* tuples = &paggr_set0_.getValues({});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaggr_set0_.getValues({});
            else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                    int P = tuple0->at(0);
                    int C = tuple0->at(1);
                    int U = tuple0->at(2);
                    Tuple negativeTuple({C,P},&_component);
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
                                if(tupleU->getPredicateName() != &_component || !tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
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
            const std::vector<unsigned>* tuples = &paggr_set0_.getValues({});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaggr_set0_.getValues({});
            else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                    int P = tuple0->at(0);
                    int C = tuple0->at(1);
                    int U = tuple0->at(2);
                    Tuple negativeTuple({C,U},&_assign);
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
                                if(tupleU->getPredicateName() != &_assign || !tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
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
        const std::vector<unsigned>* tuples = &paggr_id0_.getValues({});
        const std::vector<unsigned>* tuplesU = &uaggr_id0_.getValues({});
        const std::vector<unsigned>* tuplesF = &faggr_id0_.getValues({});
        for(unsigned i = 0; i<tuples->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
            int MIN = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuples->at(i);
            if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < MIN){
                propagatedLiterals.insert(-1);
            }else{
                for(unsigned index=0; index<joinTuplesU->size();){
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                    if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= MIN) {index++; continue;}
                    int itProp = joinTuplesU->at(index);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it =joinTuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        reasonForLiteral[itProp].insert(itAggrId);
                    }
                    propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals);
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
            int MIN = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesF->at(i);
            if(actualSum[aggrIdIt] >= MIN){
                propagatedLiterals.insert(-1);
            }else{
                std::vector<int> reason;
                for(unsigned index=0;index<joinTuplesU->size();){
                    int itProp = joinTuplesU->at(index);
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                    if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= MIN){
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
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }//close false for
        for(unsigned i = 0; i<tuplesU->size();){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
            int MIN = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesU->at(i);
            if(actualSum[aggrIdIt] >= MIN){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < MIN){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                    const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals);
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
            int MAX = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuples->at(i);
            if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < MAX+1){
                propagatedLiterals.insert(-1);
            }else{
                for(unsigned index=0; index<joinTuplesU->size();){
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                    if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= MAX+1) {index++; continue;}
                    int itProp = joinTuplesU->at(index);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it =joinTuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        reasonForLiteral[itProp].insert(itAggrId);
                    }
                    propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals);
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
            int MAX = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesF->at(i);
            if(actualSum[aggrIdIt] >= MAX+1){
                propagatedLiterals.insert(-1);
            }else{
                std::vector<int> reason;
                for(unsigned index=0;index<joinTuplesU->size();){
                    int itProp = joinTuplesU->at(index);
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                    if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= MAX+1){
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
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }//close false for
        for(unsigned i = 0; i<tuplesU->size();){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
            int MAX = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesU->at(i);
            if(actualSum[aggrIdIt] >= MAX+1){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < MAX+1){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                    const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals);
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
    trace_msg(eagerprop,5,minus << starter.toString() << " as Starter");
    propagationStack.pop_back();
    if(starter.getPredicateName() == &_body0){
        trace_msg(eagerprop,5,"Evaluating rule: 0");
        int MIN = starter[0];
        int U = starter[1];
        const std::vector<unsigned>* tuples = &puser_0_1_.getValues({U,MIN});
        const std::vector<unsigned>* tuplesU = &uuser_0_1_.getValues({U,MIN});
        if(startVar > 0){
            if(tuples->size() == 0 && tuplesU->size() == 0){
                const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
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
                    const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[itProp].insert(-it);
                    }
                    reasonForLiteral[itProp].insert(startVar);
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }
        }else{
            if(tuples->size()>0){
                int it = tuples->at(0);
                reasonForLiteral[-it].insert(startVar);
                handleConflict(-it);
                return;
            }else{
                for(unsigned i =0; i<tuplesU->size(); i++){
                    int it = tuplesU->at(i);
                    if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                        reasonForLiteral[-it].insert(startVar);
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }//close if starter
    if(starter.getPredicateName() == &_user){
        trace_msg(eagerprop,5,"Evaluating rule: 0");
        int U = starter[0];
        int MIN = starter[1];
        int MAX = starter[2];
        if(startVar > 0){
            Tuple* head = factory.find({MIN,U}, &_body0);
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
                propUndefined(head,false,propagationStack,false,propagatedLiterals);
            }
        }else{
            Tuple* head = factory.find({MIN,U}, &_body0);
            const std::vector<unsigned>* tuples = &puser_0_1_.getValues({U,MIN});
            const std::vector<unsigned>* tuplesU = &uuser_0_1_.getValues({U,MIN});
            if(head != NULL && head->isTrue()){
                if(tuples->size()==0 && tuplesU->size()==0){
                    int itHead = head->getId();
                    const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
                    for(unsigned i=0;i<tuplesF->size();i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-itHead].insert(-it);
                    }
                    handleConflict(-itHead);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size() == 1){
                    int itProp = tuplesU->at(0);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        int it = head->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals);
                }
            }else{
                if(head != NULL && head->isUndef() && tuples->size() == 0 && tuplesU->size() == 0){
                    int itHead = head->getId();
                    if(reasonForLiteral.count(-itHead) == 0  || reasonForLiteral[-itHead].empty()){
                        const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[-itHead].insert(-it);
                        }
                    }
                    propUndefined(head,false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }
    if(starter.getPredicateName() == &_body0){
        trace_msg(eagerprop,5,"Evaluating rule: 0");
        int MIN = starter[0];
        int U = starter[1];
        const std::vector<unsigned>* tuples = &puser_0_1_.getValues({U,MIN});
        const std::vector<unsigned>* tuplesU = &uuser_0_1_.getValues({U,MIN});
        if(startVar > 0){
            if(tuples->size() == 0 && tuplesU->size() == 0){
                const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
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
                    const std::vector<unsigned>* tuplesF = &fuser_0_1_.getValues({U,MIN});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[itProp].insert(-it);
                    }
                    reasonForLiteral[itProp].insert(startVar);
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }
        }else{
            if(tuples->size()>0){
                int it = tuples->at(0);
                reasonForLiteral[-it].insert(startVar);
                handleConflict(-it);
                return;
            }else{
                for(unsigned i =0; i<tuplesU->size(); i++){
                    int it = tuplesU->at(i);
                    if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                        reasonForLiteral[-it].insert(startVar);
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }//close if starter
    {
        if(starter.getPredicateName() == &_assign && startVar < 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 1");
            int C = starter[0];
            int U = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<unsigned>* tuples = &paggr_set0_1_2_.getValues({C,U});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaggr_set0_1_2_.getValues({C,U});
            else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                    if(tupleU->at(1) == C && tupleU->at(2) == U)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int P = tuple1->at(0);
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
        if(starter.getPredicateName() == &_aggr_set0 && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 1");
            int P = starter[0];
            int C = starter[1];
            int U = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            Tuple negativeTuple({C,U},&_assign);
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
                        if(tupleU->getPredicateName() != &_assign || !tupleUNegated || !(*tupleU == *tuple1))
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
        if(starter.getPredicateName() == &_component && startVar < 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 2");
            int C = starter[0];
            int P = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<unsigned>* tuples = &paggr_set0_0_1_.getValues({P,C});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaggr_set0_0_1_.getValues({P,C});
            else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                    if(tupleU->at(0) == P && tupleU->at(1) == C)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
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
        if(starter.getPredicateName() == &_aggr_set0 && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 2");
            int P = starter[0];
            int C = starter[1];
            int U = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            Tuple negativeTuple({C,P},&_component);
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
                        if(tupleU->getPredicateName() != &_component || !tupleUNegated || !(*tupleU == *tuple1))
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
        if(starter.getPredicateName() == &_aggr_set0 && startVar < 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 3");
            int P = starter[0];
            int C = starter[1];
            int U = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const Tuple* tuple1 = factory.find({C,U},&_assign);
            if(tuple1!=NULL){
                if(tuple1->isFalse())
                tuple1=NULL;
                else if(tuple1->isUndef()){
                    if(tupleU == NULL){
                        tupleU = tuple1;
                        tupleUNegated=false;
                    }else{
                        if(tupleU->getPredicateName() != &_assign || tupleUNegated || !(*tupleU == *tuple1))
                        tuple1=NULL;
                    }
                }
            }
            if(tuple1!=NULL){
                const Tuple* tuple2 = factory.find({C,P},&_component);
                if(tuple2!=NULL){
                    if(tuple2->isFalse())
                    tuple2=NULL;
                    else if(tuple2->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple2;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_component || tupleUNegated || !(*tupleU == *tuple2))
                            tuple2=NULL;
                        }
                    }
                }
                if(tuple2!=NULL){
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
        if(starter.getPredicateName() == &_component && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 3");
            int C = starter[0];
            int P = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<unsigned>* tuples = &passign_0_.getValues({C});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uassign_0_.getValues({C});
            else if(tupleU->getPredicateName() == &_assign && !tupleUNegated)
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
                    if(tupleU->at(0) == C)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int U = tuple1->at(1);
                    Tuple negativeTuple({P,C,U},&_aggr_set0);
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
                                if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
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
        if(starter.getPredicateName() == &_assign && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 3");
            int C = starter[0];
            int U = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<unsigned>* tuples = &pcomponent_0_.getValues({C});
            const std::vector<unsigned>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &ucomponent_0_.getValues({C});
            else if(tupleU->getPredicateName() == &_component && !tupleUNegated)
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
                    if(tupleU->at(0) == C)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int P = tuple1->at(1);
                    Tuple negativeTuple({P,C,U},&_aggr_set0);
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
                                if(tupleU->getPredicateName() != &_aggr_set0 || !tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
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
    if(starter.getPredicateName() == &_aggr_id0){
        int MIN = starter[0];
        int U = starter[1];
        std::vector<int> sharedVar({starter[1]});
        const std::vector<unsigned>* tuples = &paggr_set0_2_.getValues(sharedVar);
        const std::vector<unsigned>* tuplesU = &uaggr_set0_2_.getValues(sharedVar);
        if(startVar < 0){
            if(actualSum[uStartVar]>=MIN){
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
                    if(actualSum[uStartVar]+currentTuple->at(0) >= MIN){
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
                        propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }else{
            if(actualSum[uStartVar]+possibleSum[uStartVar] < MIN){
                const std::vector<unsigned>* tuplesF = &faggr_set0_2_.getValues(sharedVar);
                for(unsigned i = 0; i < tuplesF->size(); i++){
                    int it = tuplesF->at(i);
                    reasonForLiteral[-startVar].insert(-it);
                }
                handleConflict(-startVar);
                return;
            }else{
                for(unsigned index=0;index<tuplesU->size();){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                    if(actualSum[uStartVar]+possibleSum[uStartVar]-currentTuple->at(0) < MIN){
                        int itProp = tuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* tuplesF = &faggr_set0_2_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
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
            int MIN = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuples->at(i);
            if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < MIN){
                int itProp = tuples->at(i);
                const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                    int it = joinTuplesF->at(j);
                    reasonForLiteral[-itProp].insert(-it);
                }
                handleConflict(-itProp);
                return;
            }else{
                for(unsigned index=0; index<joinTuplesU->size();){
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                    if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= MIN) {index++; continue;}
                    int itProp = joinTuplesU->at(index);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it =joinTuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        reasonForLiteral[itProp].insert(itAggrId);
                    }
                    propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals);
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
            int MIN = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesF->at(i);
            if(actualSum[aggrIdIt] >= MIN){
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
                    if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= MIN){
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
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }//close false for
        for(unsigned i = 0; i<tuplesU->size();){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
            int MIN = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesU->at(i);
            if(actualSum[aggrIdIt] >= MIN){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < MIN){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                    const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals);
            }else{
                i++;
            }
        }//close undef for
    }//close aggr set starter
    {
        if(starter.getPredicateName() == &_aggr_id0 && startVar < 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 5");
            int MIN = starter[0];
            int U = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const Tuple* tuple1 = factory.find({MIN,U},&_body0);
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
        if(starter.getPredicateName() == &_body0 && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 5");
            int MIN = starter[0];
            int U = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            Tuple negativeTuple({MIN,U},&_aggr_id0);
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
    if(starter.getPredicateName() == &_body1){
        trace_msg(eagerprop,5,"Evaluating rule: 6");
        int MAX = starter[0];
        int U = starter[1];
        const std::vector<unsigned>* tuples = &puser_0_2_.getValues({U,MAX});
        const std::vector<unsigned>* tuplesU = &uuser_0_2_.getValues({U,MAX});
        if(startVar > 0){
            if(tuples->size() == 0 && tuplesU->size() == 0){
                const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
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
                    const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[itProp].insert(-it);
                    }
                    reasonForLiteral[itProp].insert(startVar);
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }
        }else{
            if(tuples->size()>0){
                int it = tuples->at(0);
                reasonForLiteral[-it].insert(startVar);
                handleConflict(-it);
                return;
            }else{
                for(unsigned i =0; i<tuplesU->size(); i++){
                    int it = tuplesU->at(i);
                    if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                        reasonForLiteral[-it].insert(startVar);
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }//close if starter
    if(starter.getPredicateName() == &_user){
        trace_msg(eagerprop,5,"Evaluating rule: 6");
        int U = starter[0];
        int MIN = starter[1];
        int MAX = starter[2];
        if(startVar > 0){
            Tuple* head = factory.find({MAX,U}, &_body1);
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
                propUndefined(head,false,propagationStack,false,propagatedLiterals);
            }
        }else{
            Tuple* head = factory.find({MAX,U}, &_body1);
            const std::vector<unsigned>* tuples = &puser_0_2_.getValues({U,MAX});
            const std::vector<unsigned>* tuplesU = &uuser_0_2_.getValues({U,MAX});
            if(head != NULL && head->isTrue()){
                if(tuples->size()==0 && tuplesU->size()==0){
                    int itHead = head->getId();
                    const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
                    for(unsigned i=0;i<tuplesF->size();i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-itHead].insert(-it);
                    }
                    handleConflict(-itHead);
                    return;
                }else if(tuples->size() == 0 && tuplesU->size() == 1){
                    int itProp = tuplesU->at(0);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        int it = head->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals);
                }
            }else{
                if(head != NULL && head->isUndef() && tuples->size() == 0 && tuplesU->size() == 0){
                    int itHead = head->getId();
                    if(reasonForLiteral.count(-itHead) == 0  || reasonForLiteral[-itHead].empty()){
                        const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[-itHead].insert(-it);
                        }
                    }
                    propUndefined(head,false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }
    if(starter.getPredicateName() == &_body1){
        trace_msg(eagerprop,5,"Evaluating rule: 6");
        int MAX = starter[0];
        int U = starter[1];
        const std::vector<unsigned>* tuples = &puser_0_2_.getValues({U,MAX});
        const std::vector<unsigned>* tuplesU = &uuser_0_2_.getValues({U,MAX});
        if(startVar > 0){
            if(tuples->size() == 0 && tuplesU->size() == 0){
                const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
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
                    const std::vector<unsigned>* tuplesF = &fuser_0_2_.getValues({U,MAX});
                    for(unsigned i=0; i<tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[itProp].insert(-it);
                    }
                    reasonForLiteral[itProp].insert(startVar);
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }
        }else{
            if(tuples->size()>0){
                int it = tuples->at(0);
                reasonForLiteral[-it].insert(startVar);
                handleConflict(-it);
                return;
            }else{
                for(unsigned i =0; i<tuplesU->size(); i++){
                    int it = tuplesU->at(i);
                    if(reasonForLiteral.count(-it) == 0 || reasonForLiteral[-it].empty())
                        reasonForLiteral[-it].insert(startVar);
                    propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }//close if starter
    if(starter.getPredicateName() == &_aggr_id1){
        int MAX = starter[0];
        int U = starter[1];
        std::vector<int> sharedVar({starter[1]});
        const std::vector<unsigned>* tuples = &paggr_set0_2_.getValues(sharedVar);
        const std::vector<unsigned>* tuplesU = &uaggr_set0_2_.getValues(sharedVar);
        if(startVar < 0){
            if(actualSum[uStartVar]>=MAX+1){
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
                    if(actualSum[uStartVar]+currentTuple->at(0) >= MAX+1){
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
                        propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }else{
            if(actualSum[uStartVar]+possibleSum[uStartVar] < MAX+1){
                const std::vector<unsigned>* tuplesF = &faggr_set0_2_.getValues(sharedVar);
                for(unsigned i = 0; i < tuplesF->size(); i++){
                    int it = tuplesF->at(i);
                    reasonForLiteral[-startVar].insert(-it);
                }
                handleConflict(-startVar);
                return;
            }else{
                for(unsigned index=0;index<tuplesU->size();){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                    if(actualSum[uStartVar]+possibleSum[uStartVar]-currentTuple->at(0) < MAX+1){
                        int itProp = tuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<unsigned>* tuplesF = &faggr_set0_2_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i);
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
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
            int MAX = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuples->at(i);
            if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < MAX+1){
                int itProp = tuples->at(i);
                const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                    int it = joinTuplesF->at(j);
                    reasonForLiteral[-itProp].insert(-it);
                }
                handleConflict(-itProp);
                return;
            }else{
                for(unsigned index=0; index<joinTuplesU->size();){
                    const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                    if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(0) >= MAX+1) {index++; continue;}
                    int itProp = joinTuplesU->at(index);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                        for(unsigned i = 0; i < joinTuplesF->size(); i++){
                            int it =joinTuplesF->at(i);
                            reasonForLiteral[itProp].insert(-it);
                        }
                        int itAggrId = tuples->at(i);
                        reasonForLiteral[itProp].insert(itAggrId);
                    }
                    propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals);
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
            int MAX = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesF->at(i);
            if(actualSum[aggrIdIt] >= MAX+1){
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
                    if(actualSum[aggrIdIt]+currentJoinTuple->at(0) >= MAX+1){
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
                        propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }//close false for
        for(unsigned i = 0; i<tuplesU->size();){
            const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
            int MAX = currentTuple->at(0);
            int U = currentTuple->at(1);
            std::vector<int> sharedVar({currentTuple->at(1)});
            const std::vector<unsigned>* joinTuples = &paggr_set0_2_.getValues(sharedVar);
            const std::vector<unsigned>* joinTuplesU = &uaggr_set0_2_.getValues(sharedVar);
            int aggrIdIt=tuplesU->at(i);
            if(actualSum[aggrIdIt] >= MAX+1){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                    for(unsigned j = 0; j < joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals);
            }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < MAX+1){
                int itProp = tuplesU->at(i);
                if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                    const std::vector<unsigned>* joinTuplesF = &faggr_set0_2_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                }
                propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals);
            }else{
                i++;
            }
        }//close undef for
    }//close aggr set starter
    {
        if(starter.getPredicateName() == &_aggr_id1 && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 8");
            int MAX = starter[0];
            int U = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const Tuple* tuple1 = factory.find({MAX,U},&_body1);
            if(tuple1!=NULL){
                if(tuple1->isFalse())
                tuple1=NULL;
                else if(tuple1->isUndef()){
                    if(tupleU == NULL){
                        tupleU = tuple1;
                        tupleUNegated=false;
                    }else{
                        if(tupleU->getPredicateName() != &_body1 || tupleUNegated || !(*tupleU == *tuple1))
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
        if(starter.getPredicateName() == &_body1 && startVar > 0){
            trace_msg(eagerprop,5,"Evaluating constraint: 8");
            int MAX = starter[0];
            int U = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const Tuple* tuple1 = factory.find({MAX,U},&_aggr_id1);
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
trace_msg(eagerprop,2,"Propagations computed");
}
}
