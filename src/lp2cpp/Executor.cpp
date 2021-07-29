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
const std::string _aux1 = "aux1";
const std::string _aux_val0 = "aux_val0";
const std::string _body0 = "body0";
const std::string _f = "f";
const std::string _sum = "sum";
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
AuxMap<0> pbody0_({});
AuxMap<0> ubody0_({});
AuxMap<0> fbody0_({});
AuxMap<0> pf_({});
AuxMap<0> uf_({});
AuxMap<0> ff_({});
AuxMap<0> paux_val0_({});
AuxMap<0> uaux_val0_({});
AuxMap<0> faux_val0_({});
AuxMap<0> pb_({});
AuxMap<0> ub_({});
AuxMap<0> fb_({});
AuxMap<32> pbody0_1_({1});
AuxMap<32> ubody0_1_({1});
AuxMap<32> fbody0_1_({1});
AuxMap<32> pbody0_0_({0});
AuxMap<32> ubody0_0_({0});
AuxMap<32> fbody0_0_({0});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<32> paggr_id0_1_({1});
AuxMap<32> uaggr_id0_1_({1});
AuxMap<32> faggr_id0_1_({1});
AuxMap<32> pb_0_({0});
AuxMap<32> ub_0_({0});
AuxMap<32> fb_0_({0});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<32> paggr_id1_1_({1});
AuxMap<32> uaggr_id1_1_({1});
AuxMap<32> faggr_id1_1_({1});
AuxMap<32> paux1_0_({0});
AuxMap<32> uaux1_0_({0});
AuxMap<32> faux1_0_({0});
AuxMap<0> psum_({});
AuxMap<0> usum_({});
AuxMap<0> fsum_({});
AuxMap<0> paux1_({});
AuxMap<0> uaux1_({});
AuxMap<0> faux1_({});
AuxMap<0> pa_({});
AuxMap<0> ua_({});
AuxMap<0> fa_({});
void Executor::handleConflict(int literal){
    std::cout<<"Handle conflict"<<std::endl;
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
    std::cout<<"Explain "<<var<<std::endl;
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        int internalVar = factory.getTupleFromWASPID(uVar)->getId();
        var = var>0 ? internalVar : -internalVar;
    }
    std::vector<int> stack;
    stack.push_back(var);
    while(!stack.empty()){
        int lit = stack.back();
        std::cout<<"Reason Literal "<<lit<<" "<<std::endl;
        stack.pop_back();
        unsigned currentReasonSize=reasonForLiteral[lit].size();
        std::cout<<"Reason size: "<<currentReasonSize<<std::endl;
        for(unsigned i = 0; i<currentReasonSize; i++){
            int reasonLiteral=reasonForLiteral[lit][i];
            std::cout<<"Reason for Literal "<<reasonLiteral<<" "<<std::endl;
            if(visitedLiteral.count(reasonLiteral) == 0){
                Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);
                visitedLiteral.insert(reasonLiteral);
                if(literal->getWaspID()==0){
                    stack.push_back(reasonLiteral);
                    std::cout<<"Internal lit"<<std::endl;
                }else{
                    int sign = reasonLiteral>0 ? 1 : -1;
                    std::cout<<"External literal "<<sign * literal->getWaspID()<<std::endl;
                    reas.insert(sign * literal->getWaspID());
                }
            }
        }
        std::cout<<"Next"<<std::endl;
    }
    std::cout<<"End explaining"<<std::endl;
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
    if(insertResult.first->getPredicateName() == &_a){
        fa_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sum){
        fsum_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        faux1_.insert2(*insertResult.first);
        faux1_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2(*insertResult.first);
        faggr_id1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2(*insertResult.first);
        faggr_id0_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_b){
        fb_.insert2(*insertResult.first);
        fb_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        faux_val0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_f){
        ff_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        fbody0_.insert2(*insertResult.first);
        fbody0_0_.insert2(*insertResult.first);
        fbody0_1_.insert2(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_a){
        pa_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sum){
        psum_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        paux1_.insert2(*insertResult.first);
        paux1_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2(*insertResult.first);
        paggr_id1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2(*insertResult.first);
        paggr_id0_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_b){
        pb_.insert2(*insertResult.first);
        pb_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        paux_val0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_f){
        pf_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        pbody0_.insert2(*insertResult.first);
        pbody0_0_.insert2(*insertResult.first);
        pbody0_1_.insert2(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_a){
        ua_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_sum){
        usum_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux1){
        uaux1_.insert2(*insertResult.first);
        uaux1_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2(*insertResult.first);
        uaggr_id1_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2(*insertResult.first);
        uaggr_id0_1_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_b){
        ub_.insert2(*insertResult.first);
        ub_0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_val0){
        uaux_val0_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_f){
        uf_.insert2(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_body0){
        ubody0_.insert2(*insertResult.first);
        ubody0_0_.insert2(*insertResult.first);
        ubody0_1_.insert2(*insertResult.first);
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
    if(tuple->getPredicateName() == &_b){
        {
            const std::vector<int>* aggrIds = &paggr_id0_1_.getValues({tuple->at(0)});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(1);
                possibleSum[itAggrId]-=tuple->at(1);
            }
        }
        {
            const std::vector<int>* aggrIds = &uaggr_id0_1_.getValues({tuple->at(0)});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(1);
                possibleSum[itAggrId]-=tuple->at(1);
            }
        }
        {
            const std::vector<int>* aggrIds = &faggr_id0_1_.getValues({tuple->at(0)});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(1);
                possibleSum[itAggrId]-=tuple->at(1);
            }
        }
    }
    if(tuple->getPredicateName() == &_b){
        {
            const std::vector<int>* aggrIds = &paggr_id1_1_.getValues({tuple->at(0)});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(1);
                possibleSum[itAggrId]-=tuple->at(1);
            }
        }
        {
            const std::vector<int>* aggrIds = &uaggr_id1_1_.getValues({tuple->at(0)});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(1);
                possibleSum[itAggrId]-=tuple->at(1);
            }
        }
        {
            const std::vector<int>* aggrIds = &faggr_id1_1_.getValues({tuple->at(0)});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i);
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(1);
                possibleSum[itAggrId]-=tuple->at(1);
            }
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
        if(tuple->getPredicateName() == &_b){
            {
                const std::vector<int>* aggrIds = &paggr_id0_1_.getValues({tuple->at(0)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(1);
                    possibleSum[itAggrId]+=tuple->at(1);
                }
            }
            {
                const std::vector<int>* aggrIds = &uaggr_id0_1_.getValues({tuple->at(0)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(1);
                    possibleSum[itAggrId]+=tuple->at(1);
                }
            }
            {
                const std::vector<int>* aggrIds = &faggr_id0_1_.getValues({tuple->at(0)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(1);
                    possibleSum[itAggrId]+=tuple->at(1);
                }
            }
        }
        if(tuple->getPredicateName() == &_b){
            {
                const std::vector<int>* aggrIds = &paggr_id1_1_.getValues({tuple->at(0)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(1);
                    possibleSum[itAggrId]+=tuple->at(1);
                }
            }
            {
                const std::vector<int>* aggrIds = &uaggr_id1_1_.getValues({tuple->at(0)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(1);
                    possibleSum[itAggrId]+=tuple->at(1);
                }
            }
            {
                const std::vector<int>* aggrIds = &faggr_id1_1_.getValues({tuple->at(0)});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i);
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(1);
                    possibleSum[itAggrId]+=tuple->at(1);
                }
            }
        }
    }
    trace_msg(eagerprop, 2, "Exit undef");
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    trace_msg(eagerprop,2,"Computing internalUndefined");
    undefinedLoaded=true;
    std::map<std::vector<int>,std::unordered_set<int>> possibleValuesSetaux_val0;
    std::map<std::vector<int>,std::vector<int>> possibleValuesaux_val0;
    {
        const std::vector<int>* tuplesU = &ub_.getValues({});
        for(unsigned i = 0; i < tuplesU->size(); i++){
            Tuple * tuple = factory.getTupleFromInternalID(tuplesU->at(i));
            if(tuple != NULL){
                {
                    std::vector<int> key({tuple->at(0)});
                    std::vector<int>* possibleSums = &possibleValuesaux_val0[key];
                    std::unordered_set<int>* possibleSumsSet = &possibleValuesSetaux_val0[key];
                    if(possibleSums->empty()){
                        possibleSums->push_back(0);
                        Tuple* aux_val = factory.addNewInternalTuple({0},&_aux_val0);
                        const auto& insertResult = aux_val->setStatus(True);
                        if(insertResult.second){
                            factory.removeFromCollisionsList(aux_val->getId());
                            insertTrue(insertResult);
                        }
                    }
                    unsigned size = possibleSums->size();
                    for(unsigned i = 0; i<size; i++){
                        if(possibleSumsSet->count(possibleSums->at(i)+tuple->at(1))==0){
                            possibleSumsSet->insert(possibleSums->at(i)+tuple->at(1));
                            possibleSums->push_back(possibleSums->at(i)+tuple->at(1));
                            Tuple* aux_val = factory.addNewInternalTuple({possibleSums->back()},&_aux_val0);
                            const auto& insertResult = aux_val->setStatus(True);
                            if(insertResult.second){
                                factory.removeFromCollisionsList(aux_val->getId());
                                insertTrue(insertResult);
                            }
                        }
                    }
                }
            }
        }
    }
    trace_msg(eagerprop,2,"Computing aggr id no shared variables");
    trace_msg(eagerprop,2,"Computing aggr id no shared variables");
    {
        const std::vector<int>* tuples = &pf_.getValues({});
        const std::vector<int>* tuplesU = &uf_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int X = tuple->at(0);
            const std::vector<int>* tuples = &paux_val0_.getValues({});
            const std::vector<int>* tuplesU = &uaux_val0_.getValues({});
            for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                const Tuple* tuple = NULL;
                if(i<tuples->size())
                    tuple=factory.getTupleFromInternalID(tuples->at(i));
                else
                    tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int S = tuple->at(0);
                Tuple* aux = factory.addNewInternalTuple({S,X}, &_body0);
                const auto& insertResult = aux->setStatus(Undef);
                if (insertResult.second) {
                    factory.removeFromCollisionsList(aux->getId());
                    insertUndef(insertResult);
                    {
                        Tuple* head = factory.addNewInternalTuple({S,X},&_aggr_id0);
                        const auto& headInsertResult = head->setStatus(Undef);
                        if (headInsertResult.second) {
                            factory.removeFromCollisionsList(head->getId());
                            insertUndef(headInsertResult);
                        }
                    }
                    {
                        Tuple* head = factory.addNewInternalTuple({S,X},&_aggr_id1);
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
    trace_msg(eagerprop,2,"Computing aggr id no shared variables");
    trace_msg(eagerprop,2,"Computing aggr id no shared variables");
    {
        const std::vector<int>* tuples = &pbody0_.getValues({});
        const std::vector<int>* tuplesU = &ubody0_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=factory.getTupleFromInternalID(tuples->at(i));
            else
                tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int S = tuple->at(0);
            int X = tuple->at(1);
            Tuple* boundTuple = factory.find({S,X}, &_aggr_id0);
            if(boundTuple != NULL  && !boundTuple->isFalse()){
                Tuple* boundTuple = factory.find({S,X}, &_aggr_id1);
                if(boundTuple == NULL || !boundTuple->isTrue()){
                    Tuple* aux = factory.addNewInternalTuple({S,X}, &_aux1);
                    const auto& insertResult = aux->setStatus(Undef);
                    if (insertResult.second) {
                        factory.removeFromCollisionsList(aux->getId());
                        insertUndef(insertResult);
                        {
                            Tuple* head = factory.addNewInternalTuple({S},&_sum);
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
    trace_msg(eagerprop,2,"Computing aggr id no shared variables");
    trace_msg(eagerprop,2,"Computing sums");
    {
        const std::vector<int>* aggregateIds = &uaggr_id0_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
            const std::vector<int>* aggrSetTuples = &ub_0_.getValues({currentTuple->at(1)});
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possibleSum[it]+=factory.getTupleFromInternalID(aggrSetTuples->at(j))->at(1);
        }
    }
    {
        const std::vector<int>* aggregateIds = &uaggr_id1_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i);
            const Tuple* currentTuple = factory.getTupleFromInternalID(aggregateIds->at(i));
            const std::vector<int>* aggrSetTuples = &ub_0_.getValues({currentTuple->at(1)});
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possibleSum[it]+=factory.getTupleFromInternalID(aggrSetTuples->at(j))->at(1);
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
    psum_.clear();
    paggr_id1_.clear();
    paggr_id1_1_.clear();
    paggr_id0_.clear();
    paggr_id0_1_.clear();
    fsum_.clear();
    faggr_id1_.clear();
    faggr_id1_1_.clear();
    faggr_id0_.clear();
    faggr_id0_1_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["a"] = &_a;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    stringToUniqueStringPointer["aux_val0"] = &_aux_val0;
    stringToUniqueStringPointer["body0"] = &_body0;
    stringToUniqueStringPointer["f"] = &_f;
    stringToUniqueStringPointer["sum"] = &_sum;
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
                    if(tupleU->getPredicateName() == &_b){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(1);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(1);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(1);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_b){
                        {
                            const std::vector<int>* aggrIds = &paggr_id1_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(1);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id1_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(1);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id1_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(1);
                                possibleSum[itAggrId]-=tupleU->at(1);
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
                    if(tupleU->getPredicateName() == &_b){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_b){
                        {
                            const std::vector<int>* aggrIds = &paggr_id1_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id1_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(1);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id1_1_.getValues({tupleU->at(0)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(1);
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
            if(tuple->getPredicateName() == &_b){
                {
                    const std::vector<int>* aggrIds = &paggr_id0_1_.getValues({tuple->at(0)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(1);
                        possibleSum[itAggrId]+=tuple->at(1);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id0_1_.getValues({tuple->at(0)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(1);
                        possibleSum[itAggrId]+=tuple->at(1);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id0_1_.getValues({tuple->at(0)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(1);
                        possibleSum[itAggrId]+=tuple->at(1);
                    }
                }
            }
            if(tuple->getPredicateName() == &_b){
                {
                    const std::vector<int>* aggrIds = &paggr_id1_1_.getValues({tuple->at(0)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(1);
                        possibleSum[itAggrId]+=tuple->at(1);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id1_1_.getValues({tuple->at(0)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(1);
                        possibleSum[itAggrId]+=tuple->at(1);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id1_1_.getValues({tuple->at(0)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(1);
                        possibleSum[itAggrId]+=tuple->at(1);
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
        remainingPropagatingLiterals.erase(-facts[i]);
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
                const std::vector<int>* tuples = &psum_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usum_.getValues({});
                else if(tupleU->getPredicateName() == &_sum && !tupleUNegated)
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
                        int S = tuple0->at(0);
                        const std::vector<int>* tuples = &pa_.getValues({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                                int X = tuple1->at(0);
                                int Y = tuple1->at(1);
                                if(S < X){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                                    }else{
                                        std::cout<<"Conflict On Constraint 10"<<std::endl;
                                        propagatedLiterals.push_back(-1);
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
                const std::vector<int>* tuples = &pbody0_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        int S = tuple0->at(0);
                        int X = tuple0->at(1);
                        const Tuple* tuple1 = factory.find({S,X},&_aggr_id0);
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
                            Tuple negativeTuple({S,X},&_aggr_id1);
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
                                Tuple negativeTuple({S,X},&_aux1);
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
                                            if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple3))
                                            tuple3=NULL;
                                        }
                                    }
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                                    }else{
                                        std::cout<<"Conflict On Constraint 9"<<std::endl;
                                        propagatedLiterals.push_back(-1);
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
                const std::vector<int>* tuples = &paux1_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int S = tuple0->at(0);
                        int X = tuple0->at(1);
                        const Tuple* tuple1 = factory.find({S,X},&_aggr_id1);
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
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 8"<<std::endl;
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
                const std::vector<int>* tuples = &paux1_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int S = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple negativeTuple({S,X},&_aggr_id0);
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
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 7"<<std::endl;
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
                const std::vector<int>* tuples = &paux1_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        tuple0 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple0 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        tuple0 = tupleU;
                    }
                    if(tuple0!=NULL){
                        int S = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple negativeTuple({S,X},&_body0);
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
                                    if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 6"<<std::endl;
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
                const std::vector<int>* tuples = &pf_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uf_.getValues({});
                else if(tupleU->getPredicateName() == &_f && !tupleUNegated)
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
                        int X = tuple0->at(0);
                        const std::vector<int>* tuples = &paux_val0_.getValues({});
                        const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux_val0_.getValues({});
                        else if(tupleU->getPredicateName() == &_aux_val0 && !tupleUNegated)
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
                                int S = tuple1->at(0);
                                Tuple negativeTuple({S,X},&_body0);
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
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                                    }else{
                                        std::cout<<"Conflict On Constraint 2"<<std::endl;
                                        propagatedLiterals.push_back(-1);
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
                const std::vector<int>* tuples = &pbody0_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        int S = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple negativeTuple({S},&_aux_val0);
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
                                    if(tupleU->getPredicateName() != &_aux_val0 || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 1"<<std::endl;
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
                const std::vector<int>* tuples = &pbody0_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        int S = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple negativeTuple({X},&_f);
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
                                    if(tupleU->getPredicateName() != &_f || !tupleUNegated || !(*tupleU == *tuple1))
                                    tuple1=NULL;
                                }
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 0"<<std::endl;
                                propagatedLiterals.push_back(-1);
                            }
                        }
                    }
                }
            }
        }
        {
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < S){
                    propagatedLiterals.push_back(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(1) >= S) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
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
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= S){
                    propagatedLiterals.push_back(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(1) >= S){
                            int itProp = joinTuplesU->at(index);
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
                        }
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= S){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < S){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
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
            const std::vector<int>* tuples = &paggr_id1_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < S+1){
                    propagatedLiterals.push_back(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(1) >= S+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
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
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= S+1){
                    propagatedLiterals.push_back(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(1) >= S+1){
                            int itProp = joinTuplesU->at(index);
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
                        }
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= S+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < S+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
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
            const std::vector<int>* trueHeads = &psum_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(trueHeads->at(i));
                int S = head->at(0);
                const std::vector<int>* tuples = &paux1_0_.getValues({S});
                const std::vector<int>* tuplesU = &uaux1_0_.getValues({S});
                if(tuples->size() == 0){
                    if(tuplesU->size() == 0){
                        propagatedLiterals.push_back(-1);
                    }else if(tuplesU->size() == 1){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }else{
                }
            }
            const std::vector<int>* undefHeads = &usum_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(undefHeads->at(i));
                int S = head->at(0);
                const std::vector<int>* tuples = &paux1_0_.getValues({S});
                if(tuples->size() == 0){
                    const std::vector<int>* tuplesU = &uaux1_0_.getValues({S});
                    if(tuplesU->size() == 0){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }
            }
            const std::vector<int>* falseHeads = &fsum_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = factory.getTupleFromInternalID(falseHeads->at(i));
                int S = head->at(0);
                const std::vector<int>* tuples = &paux1_0_.getValues({S});
                if(tuples->size() == 0){
                    const std::vector<int>* tuplesU = &uaux1_0_.getValues({S});
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
        {
            if(starter.getPredicateName() == &_f && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 0");
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &pbody0_1_.getValues({X});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(1) == X)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int S = tuple1->at(0);
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
                            std::cout<<"Conflict On Constraint 0"<<std::endl;
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                std::cout<<it<<" ";tuple1->print();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 0");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X},&_f);
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
                            if(tupleU->getPredicateName() != &_f || !tupleUNegated || !(*tupleU == *tuple1))
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
                        std::cout<<"Conflict On Constraint 0"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aux_val0 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 1");
                int S = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &pbody0_0_.getValues({S});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_0_.getValues({S});
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
                        tuple1 = factory.getTupleFromInternalID(tuples->at(i));
                    else if(i<tuples->size()+tuplesU->size()){
                        tupleU = tuple1 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        tupleUNegated=false;
                    }else if(!undeRepeated.empty()){
                        if(tupleU->at(0) == S)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int X = tuple1->at(1);
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
                            std::cout<<"Conflict On Constraint 1"<<std::endl;
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                std::cout<<it<<" ";tuple1->print();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 1");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({S},&_aux_val0);
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
                            if(tupleU->getPredicateName() != &_aux_val0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        std::cout<<"Conflict On Constraint 1"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_body0 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 2");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({X},&_f);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_f || tupleUNegated || !(*tupleU == *tuple1))
                            tuple1=NULL;
                        }
                    }
                }
                if(tuple1!=NULL){
                    const Tuple* tuple2 = factory.find({S},&_aux_val0);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_aux_val0 || tupleUNegated || !(*tupleU == *tuple2))
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
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                        }else{
                            std::cout<<"Conflict On Constraint 2"<<std::endl;
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                std::cout<<it<<" ";tuple1->print();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                std::cout<<it<<" ";tuple2->print();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aux_val0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 2");
                int S = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &pf_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uf_.getValues({});
                else if(tupleU->getPredicateName() == &_f && !tupleUNegated)
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
                        int X = tuple1->at(0);
                        Tuple negativeTuple({S,X},&_body0);
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
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 2"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    std::cout<<it<<" ";tuple2->print();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_f && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 2");
                int X = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &paux_val0_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_val0_.getValues({});
                else if(tupleU->getPredicateName() == &_aux_val0 && !tupleUNegated)
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
                        int S = tuple1->at(0);
                        Tuple negativeTuple({S,X},&_body0);
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
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 2"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    std::cout<<it<<" ";tuple2->print();
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
            int S = starter[0];
            int X = starter[1];
            std::vector<int> sharedVar({starter[1]});
            const std::vector<int>* tuples = &pb_0_.getValues(sharedVar);
            const std::vector<int>* tuplesU = &ub_0_.getValues(sharedVar);
            if(startVar < 0){
                if(actualSum[uStartVar]>=S){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index =0; index<tuplesU->size(); index++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+currentTuple->at(1) >= S){
                            int itProp = currentTuple->getId();
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
                        }
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < S){
                    const std::vector<int>* tuplesF = &fb_0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();index++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-currentTuple->at(1) < S){
                            int itProp = tuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                                const std::vector<int>* tuplesF = &fb_0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                        }
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_b){
            const std::vector<int>* tuples = &paggr_id0_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < S){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(1) >= S) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
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
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= S){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(1) >= S){
                            int itProp = joinTuplesU->at(index);
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
                        }
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= S){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < S){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
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
            int S = starter[0];
            int X = starter[1];
            std::vector<int> sharedVar({starter[1]});
            const std::vector<int>* tuples = &pb_0_.getValues(sharedVar);
            const std::vector<int>* tuplesU = &ub_0_.getValues(sharedVar);
            if(startVar < 0){
                if(actualSum[uStartVar]>=S+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i);
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index =0; index<tuplesU->size(); index++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+currentTuple->at(1) >= S+1){
                            int itProp = currentTuple->getId();
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
                        }
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < S+1){
                    const std::vector<int>* tuplesF = &fb_0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i);
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();index++){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(index));
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-currentTuple->at(1) < S+1){
                            int itProp = tuplesU->at(index);
                            if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                                const std::vector<int>* tuplesF = &fb_0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i);
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                        }
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_b){
            const std::vector<int>* tuples = &paggr_id1_.getValues({});
            const std::vector<int>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<int>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i);
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < S+1){
                    int itProp = tuples->at(i);
                    const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j);
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-currentJoinTuple->at(1) >= S+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i);
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
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                if(actualSum[aggrIdIt] >= S+1){
                    int itProp = tuplesF->at(i);
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j);
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));
                        if(actualSum[aggrIdIt]+currentJoinTuple->at(1) >= S+1){
                            int itProp = joinTuplesU->at(index);
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
                        }
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));
                int S = currentTuple->at(0);
                int X = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(1)});
                const std::vector<int>* joinTuples = &pb_0_.getValues(sharedVar);
                const std::vector<int>* joinTuplesU = &ub_0_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                if(actualSum[aggrIdIt] >= S+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j);
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < S+1){
                    int itProp = tuplesU->at(i);
                    if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].empty()){
                        const std::vector<int>* joinTuplesF = &fb_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_sum){
            trace_msg(eagerprop,5,"Evaluating rule: 5");
            int S = starter[0];
            const std::vector<int>* tuples = &paux1_0_.getValues({S});
            const std::vector<int>* tuplesU = &uaux1_0_.getValues({S});
            if(startVar > 0){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
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
                        const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
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
        if(starter.getPredicateName() == &_aux1){
            trace_msg(eagerprop,5,"Evaluating rule: 5");
            int S = starter[0];
            int X = starter[1];
            if(startVar > 0){
                Tuple* head = factory.find({S}, &_sum);
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
                Tuple* head = factory.find({S}, &_sum);
                const std::vector<int>* tuples = &paux1_0_.getValues({S});
                const std::vector<int>* tuplesU = &uaux1_0_.getValues({S});
                if(head != NULL && head->isTrue()){
                    if(tuples->size()==0 && tuplesU->size()==0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            reasonForLiteral[-itHead].insert(-it);
                        }
                        handleConflict(-itHead);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].empty()){
                            const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
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
                            const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
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
        if(starter.getPredicateName() == &_sum){
            trace_msg(eagerprop,5,"Evaluating rule: 5");
            int S = starter[0];
            const std::vector<int>* tuples = &paux1_0_.getValues({S});
            const std::vector<int>* tuplesU = &uaux1_0_.getValues({S});
            if(startVar > 0){
                if(tuples->size() == 0 && tuplesU->size() == 0){
                    const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
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
                        const std::vector<int>* tuplesF = &faux1_0_.getValues({S});
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
            if(starter.getPredicateName() == &_body0 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 6");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_aux1);
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
                        std::cout<<"Conflict On Constraint 6"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_aux1 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 6");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({S,X},&_body0);
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
                            if(tupleU->getPredicateName() != &_body0 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        std::cout<<"Conflict On Constraint 6"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aggr_id0 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 7");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_aux1);
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
                        std::cout<<"Conflict On Constraint 7"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_aux1 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 7");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({S,X},&_aggr_id0);
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
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }else{
                        std::cout<<"Conflict On Constraint 7"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aggr_id1 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 8");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_aux1);
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
                        std::cout<<"Conflict On Constraint 8"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_aux1 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 8");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_aggr_id1);
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
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                    }else{
                        std::cout<<"Conflict On Constraint 8"<<std::endl;
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            std::cout<<it<<" ";tuple1->print();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aux1 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 9");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_body0);
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
                    const Tuple* tuple2 = factory.find({S,X},&_aggr_id0);
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
                        Tuple negativeTuple({S,X},&_aggr_id1);
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
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 9"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    std::cout<<it<<" ";tuple2->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    std::cout<<it<<" ";tuple3->print();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aggr_id1 && startVar < 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 9");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_body0);
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
                    const Tuple* tuple2 = factory.find({S,X},&_aggr_id0);
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
                        Tuple negativeTuple({S,X},&_aux1);
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
                                    if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple3))
                                    tuple3=NULL;
                                }
                            }
                        }
                        if(tuple3!=NULL){
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
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 9"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    std::cout<<it<<" ";tuple2->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    std::cout<<it<<" ";tuple3->print();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aggr_id0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 9");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_body0);
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
                    Tuple negativeTuple({S,X},&_aggr_id1);
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
                        Tuple negativeTuple({S,X},&_aux1);
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
                                    if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple3))
                                    tuple3=NULL;
                                }
                            }
                        }
                        if(tuple3!=NULL){
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
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 9"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    std::cout<<it<<" ";tuple2->print();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    std::cout<<it<<" ";tuple3->print();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body0 && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 9");
                int S = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const Tuple* tuple1 = factory.find({S,X},&_aggr_id0);
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
                    Tuple negativeTuple({S,X},&_aggr_id1);
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
                        Tuple negativeTuple({S,X},&_aux1);
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
                                    if(tupleU->getPredicateName() != &_aux1 || !tupleUNegated || !(*tupleU == *tuple3))
                                    tuple3=NULL;
                                }
                            }
                        }
                        if(tuple3!=NULL){
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
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals);
                            }else{
                                std::cout<<"Conflict On Constraint 9"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    std::cout<<it<<" ";tuple2->print();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    std::cout<<it<<" ";tuple3->print();
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
        {
            if(starter.getPredicateName() == &_a && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 10");
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &psum_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &usum_.getValues({});
                else if(tupleU->getPredicateName() == &_sum && !tupleUNegated)
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
                        int S = tuple1->at(0);
                        if(S < X){
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
                                std::cout<<"Conflict On Constraint 10"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_sum && startVar > 0){
                trace_msg(eagerprop,5,"Evaluating constraint: 10");
                int S = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<int>* tuples = &pa_.getValues({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES;
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
                        int X = tuple1->at(0);
                        int Y = tuple1->at(1);
                        if(S < X){
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
                                std::cout<<"Conflict On Constraint 10"<<std::endl;
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    std::cout<<it<<" ";tuple1->print();
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
    }
    trace_msg(eagerprop,2,"Propagations computed");
}
}
