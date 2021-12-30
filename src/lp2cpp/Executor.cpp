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
const std::string _aggr_id0 = "aggr_id0";
const std::string _aggr_id1 = "aggr_id1";
const std::string _aggr_set0 = "aggr_set0";
const std::string _aux0 = "aux0";
const std::string _domBody = "domBody";
const std::string _l0 = "l0";
const std::string _l1 = "l1";
const std::string _l2 = "l2";
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
AuxMap<0> pl0_({});
AuxMap<0> ul0_({});
AuxMap<0> fl0_({});
AuxMap<0> pdomBody_({});
AuxMap<0> udomBody_({});
AuxMap<0> fdomBody_({});
AuxMap<96> paux0_0_1_2_({0,1,2});
AuxMap<96> uaux0_0_1_2_({0,1,2});
AuxMap<96> faux0_0_1_2_({0,1,2});
AuxMap<0> paux0_({});
AuxMap<0> uaux0_({});
AuxMap<0> faux0_({});
AuxMap<0> paggr_set0_({});
AuxMap<0> uaggr_set0_({});
AuxMap<0> faggr_set0_({});
AuxMap<32> paux0_0_({0});
AuxMap<32> uaux0_0_({0});
AuxMap<32> faux0_0_({0});
AuxMap<64> paux0_1_3_({1,3});
AuxMap<64> uaux0_1_3_({1,3});
AuxMap<64> faux0_1_3_({1,3});
AuxMap<0> pl2_({});
AuxMap<0> ul2_({});
AuxMap<0> fl2_({});
AuxMap<64> paux0_0_2_({0,2});
AuxMap<64> uaux0_0_2_({0,2});
AuxMap<64> faux0_0_2_({0,2});
AuxMap<0> paggr_id0_({});
AuxMap<0> uaggr_id0_({});
AuxMap<0> faggr_id0_({});
AuxMap<64> paggr_id0_0_1_({0,1});
AuxMap<64> uaggr_id0_0_1_({0,1});
AuxMap<64> faggr_id0_0_1_({0,1});
AuxMap<64> paggr_set0_2_1_({2,1});
AuxMap<64> uaggr_set0_2_1_({2,1});
AuxMap<64> faggr_set0_2_1_({2,1});
AuxMap<0> paggr_id1_({});
AuxMap<0> uaggr_id1_({});
AuxMap<0> faggr_id1_({});
AuxMap<64> paggr_id1_0_1_({0,1});
AuxMap<64> uaggr_id1_0_1_({0,1});
AuxMap<64> faggr_id1_0_1_({0,1});
void Executor::handleConflict(int literal,std::vector<int>& propagatedLiterals){
    if(currentDecisionLevel == -1){
        propagatedLiterals.push_back(1);
        return;
    }

    std::unordered_set<int> visitedLiterals;
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    std::cout<<"Handle Internal conflict: ";
    l->print();
    explainExternalLiteral(literal,conflictReason,visitedLiterals,true);
    explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);
    propagatedLiterals.push_back(1);
    reasonForLiteral[literal].get()->clear();
}
int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,std::unordered_set<int>& visitedLiteral,bool propagatorCall){
    std::cout<<"Explain "<<var<<std::endl;
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        int internalVar = factory.getTupleFromWASPID(uVar)->getId();
        var = var>0 ? internalVar : -internalVar;
        std::cout<<"Explain from wasp ";
        factory.getTupleFromWASPID(uVar)->print();
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
                literal->print();
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
    std::cout<<"Reason for: "<<var<<std::endl;
    for(unsigned i=0; i<reas.size(); i++){
        Tuple* t = reas[i]>0 ? factory.getTupleFromWASPID(reas[i]) : factory.getTupleFromWASPID(-reas[i]);
        std::cout<<reas[i]<<" ";t->print();
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
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        faggr_id1_.insert2Vec(*insertResult.first);
        faggr_id1_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        faggr_id0_.insert2Vec(*insertResult.first);
        faggr_id0_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l2){
        fl2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        faggr_set0_.insert2Set(*insertResult.first);
        faggr_set0_2_1_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        faux0_.insert2Vec(*insertResult.first);
        faux0_0_.insert2Vec(*insertResult.first);
        faux0_0_1_2_.insert2Vec(*insertResult.first);
        faux0_0_2_.insert2Vec(*insertResult.first);
        faux0_1_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_domBody){
        fdomBody_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        fl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        fl1_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        paggr_id1_.insert2Vec(*insertResult.first);
        paggr_id1_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        paggr_id0_.insert2Vec(*insertResult.first);
        paggr_id0_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l2){
        pl2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        paggr_set0_.insert2Set(*insertResult.first);
        paggr_set0_2_1_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        paux0_.insert2Vec(*insertResult.first);
        paux0_0_.insert2Vec(*insertResult.first);
        paux0_0_1_2_.insert2Vec(*insertResult.first);
        paux0_0_2_.insert2Vec(*insertResult.first);
        paux0_1_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_domBody){
        pdomBody_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        pl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        pl1_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_aggr_id1){
        uaggr_id1_.insert2Vec(*insertResult.first);
        uaggr_id1_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_id0){
        uaggr_id0_.insert2Vec(*insertResult.first);
        uaggr_id0_0_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l2){
        ul2_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aggr_set0){
        uaggr_set0_.insert2Set(*insertResult.first);
        uaggr_set0_2_1_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux0){
        uaux0_.insert2Vec(*insertResult.first);
        uaux0_0_.insert2Vec(*insertResult.first);
        uaux0_0_1_2_.insert2Vec(*insertResult.first);
        uaux0_0_2_.insert2Vec(*insertResult.first);
        uaux0_1_3_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_domBody){
        udomBody_.insert2Vec(*insertResult.first);
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
    std::cout<<"True " << minus << tuple->toString()<<std::endl;
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
    if(tuple == NULL)
        std::cout<<"Unable to find tuple "<<var<<std::endl;
    else
        std::cout<<"Undef " << minus << tuple->toString()<<std::endl;
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
void checkFoundness(int id){
    if(id > 0) return;
    std::cout<<"propagating unfounded "<<-id<<std::endl;
    std::vector<int> unfounded({-id});
    while(!unfounded.empty()){
        const Tuple* tuple = factory.getTupleFromInternalID(unfounded.back());
        unfounded.pop_back();
        if(tuple != NULL){
            std::cout << "propagating "<<tuple->getId()<<std::endl;
        }
    }
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    std::cout<<"Undef received"<<std::endl;
    undefinedLoaded=true;
    {
        const std::vector<int>* tuples = &pl0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = tuple->at(0);
            int T1 = tuple->at(1);
            Tuple* domPred = factory.addNewInternalTuple({T0},&_domBody);
            const auto& insertResult = domPred->setStatus(True);
            if(insertResult.second){
                factory.removeFromCollisionsList(domPred->getId());
                insertTrue(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pl1_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul1_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T2 = tuple0->at(0);
            if(tuple0->at(1) == T2){
                const std::vector<int>* tuples = &pl0_.getValuesVec({});
                const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple1 = NULL;
                    if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int T1 = tuple1->at(0);
                    int T3 = tuple1->at(1);
                    const std::vector<int>* tuples = &pdomBody_.getValuesVec({});
                    const std::vector<int>* tuplesU = &udomBody_.getValuesVec({});
                    for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                        Tuple* tuple2 = NULL;
                        if(i<tuples->size()) tuple2=factory.getTupleFromInternalID(tuples->at(i));
                        else tuple2=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                        int T0 = tuple2->at(0);
                        Tuple* tuple3 = factory.find({T2,T0,T2},&_l2);
                        if(tuple3==NULL || !tuple3->isTrue()){
                            Tuple* saving2 = factory.addNewInternalTuple({T2,T1,T0,T3},&_aux0);
                            const auto& insertResult = saving2->setStatus(Undef);
                            if(insertResult.second){
                                factory.removeFromCollisionsList(saving2->getId());
                                insertUndef(insertResult);
                                Tuple* saving0 = factory.addNewInternalTuple({T2,T1,T0},&_aggr_set0);
                                const auto& insertResult = saving0->setStatus(Undef);
                                if(insertResult.second){
                                    factory.removeFromCollisionsList(saving0->getId());
                                    insertUndef(insertResult);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &pl0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = tuple->at(0);
            int T1 = tuple->at(1);
            Tuple* aggr_id = factory.addNewInternalTuple({T0,T1},&_aggr_id1);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &pl0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple = NULL;
            if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));
            else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = tuple->at(0);
            int T1 = tuple->at(1);
            Tuple* aggr_id = factory.addNewInternalTuple({T0,T1},&_aggr_id0);
            const auto& insertResult = aggr_id->setStatus(Undef);
            if(insertResult.second){
                factory.removeFromCollisionsList(aggr_id->getId());
                insertUndef(insertResult);
            }
        }
    }
    {
        const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* aggr_id = NULL;
            if(i<tuples->size()) aggr_id=factory.getTupleFromInternalID(tuples->at(i));
            else aggr_id=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = aggr_id->at(0);
            int T1 = aggr_id->at(1);
            const IndexedSet* aggrSet = &paggr_set0_2_1_.getValuesSet({T0,T1});
            const IndexedSet* aggrSetU = &uaggr_set0_2_1_.getValuesSet({T0,T1});
            auto itTrue = aggrSet->begin();
            auto itUndef = aggrSetU->begin();
            while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){
                Tuple* tuple = NULL;
                bool undefTuple = false;
                if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
                else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}
                int T2 = tuple->at(0);
                if(tuple->at(1) == T1){
                    if(tuple->at(2) == T0){
                        int& sum = undefTuple ? possibleSum[aggr_id->getId()] : actualSum[aggr_id->getId()];
                        sum+=T2;
                    }
                }
            }
        }
    }
    {
        const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
        const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* aggr_id = NULL;
            if(i<tuples->size()) aggr_id=factory.getTupleFromInternalID(tuples->at(i));
            else aggr_id=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = aggr_id->at(0);
            int T1 = aggr_id->at(1);
            const IndexedSet* aggrSet = &paggr_set0_2_1_.getValuesSet({T0,T1});
            const IndexedSet* aggrSetU = &uaggr_set0_2_1_.getValuesSet({T0,T1});
            auto itTrue = aggrSet->begin();
            auto itUndef = aggrSetU->begin();
            while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){
                Tuple* tuple = NULL;
                bool undefTuple = false;
                if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
                else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}
                int T2 = tuple->at(0);
                if(tuple->at(1) == T1){
                    if(tuple->at(2) == T0){
                        int& sum = undefTuple ? possibleSum[aggr_id->getId()] : actualSum[aggr_id->getId()];
                        sum+=T2;
                    }
                }
            }
        }
    }
    for(auto pair : actualSum){
        factory.getTupleFromInternalID(pair.first)->print();
        std::cout<<" ActualSum "<<pair.second<<std::endl;
    }
    for(auto pair : possibleSum){
        factory.getTupleFromInternalID(pair.first)->print();
        std::cout<<"PossibleSum "<<pair.second<<std::endl;
    }
    std::cout<<"Generated"<<std::endl;
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
    paggr_id1_0_1_.clear();
    paggr_id0_.clear();
    paggr_id0_0_1_.clear();
    paggr_set0_.clear();
    paggr_set0_2_1_.clear();
    faggr_id1_.clear();
    faggr_id1_0_1_.clear();
    faggr_id0_.clear();
    faggr_id0_0_1_.clear();
    faggr_set0_.clear();
    faggr_set0_2_1_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    stringToUniqueStringPointer["domBody"] = &_domBody;
    stringToUniqueStringPointer["l0"] = &_l0;
    stringToUniqueStringPointer["l1"] = &_l1;
    stringToUniqueStringPointer["l2"] = &_l2;
    factory.setIndexForAggregateSet(0,&_aggr_set0);
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
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id0_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id1_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id1_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id1_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(currentDecisionLevel <= 0){
                        std::cout<<" Literal propagated as True";                        tupleU->print();
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
                            const std::vector<int>* aggrIds = &paggr_id0_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id0_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id0_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<int>* aggrIds = &paggr_id1_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &uaggr_id1_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<int>* aggrIds = &faggr_id1_0_1_.getValuesVec({tupleU->at(2),tupleU->at(1)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                    }
                    if(currentDecisionLevel <= 0){
                        std::cout<<currentDecisionLevel<<" Literal propagated as False";                        tupleU->print();
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
        int sign = isNegated == asNegative ? 1 : -1;
        if(remainingPropagatingLiterals.count(it*sign)==0){
            if(currentDecisionLevel <= 0){
                std::cout<<currentDecisionLevel<<" Propagating external literal: ";
                tupleU->print();
            }
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
    std::cout<<"exit propundef"<<std::endl;
    return false;
}
void Executor::printInternalLiterals(){
    for(int internalId : paggr_id1_.getValuesVec({})){
        factory.getTupleFromInternalID(internalId)->print();
    }
    for(int internalId : paggr_id0_.getValuesVec({})){
        factory.getTupleFromInternalID(internalId)->print();
    }
    for(int internalId : paggr_set0_.getValuesSet({})){
        factory.getTupleFromInternalID(internalId)->print();
    }
}
void Executor::unRollToLevel(int decisionLevel){
    std::cout<<"Unrolling to level: "<<decisionLevel << " " <<currentDecisionLevel<<std::endl;
    conflictCount++;
    std::cout<<"Unfolding incomplete propagation"<<std::endl;
    for(int literealToProp : remainingPropagatingLiterals){
        int var = literealToProp > 0 ? literealToProp : -literealToProp;
        Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
        std::cout<<"Literal not propagate: "<<literealToProp;
        literalNotPropagated->print();
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
            if(tuple->getPredicateName() == &_aggr_set0){
                {
                    const std::vector<int>* aggrIds = &paggr_id0_0_1_.getValuesVec({tuple->at(2),tuple->at(1)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id0_0_1_.getValuesVec({tuple->at(2),tuple->at(1)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id0_0_1_.getValuesVec({tuple->at(2),tuple->at(1)});
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
                    const std::vector<int>* aggrIds = &paggr_id1_0_1_.getValuesVec({tuple->at(2),tuple->at(1)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &uaggr_id1_0_1_.getValuesVec({tuple->at(2),tuple->at(1)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i);
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<int>* aggrIds = &faggr_id1_0_1_.getValuesVec({tuple->at(2),tuple->at(1)});
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
            propagationStack.push_back(facts[i]);
        }
    }
    if(decisionLevel>-1) {
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            const std::vector<int>* tuples = &paggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uaggr_id0_.getValuesVec({});
            const std::vector<int>* tuplesF = &faggr_id0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                int T0 = currentTuple->at(0);
                int T1 = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < 6-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= 6-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int T0 = currentTuple->at(0);
                int T1 = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= 6){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < 6-currentJoinTuple->at(0))break;
                            if(shared_reason.get()->empty()){
                                for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                    int it = *i;
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
                    int T0 = currentTuple->at(0);
                    int T1 = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                    const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                    const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesU->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum >= 6){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else if(actSum < 6 - posSum){
                        int itProp = tuplesU->at(i);
                        const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
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
                const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int T0 = currentTuple->at(0);
                    int T1 = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                    const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                    const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                    int aggrIdIt=tuples->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum < 6+1-posSum){
                        propagatedLiterals.push_back(1);
                    }else{
                        while(!joinTuplesU->empty()){
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                            if(actSum >= 6+1-posSum+currentJoinTuple->at(0)) {break;}
                            int itProp = *joinTuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                                for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(-it);
                                }
                                int itAggrId = tuples->at(i);
                                shared_reason.get()->insert(itAggrId);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                    int T0 = currentTuple->at(0);
                    int T1 = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                    const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                    const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesF->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    if(actSum >= 6+1){
                        propagatedLiterals.push_back(1);
                    }else{
                        while(!joinTuplesU->empty()){
                            int itProp = *joinTuplesU->begin();
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                            if(actSum < 6+1-currentJoinTuple->at(0))break;
                                if(shared_reason.get()->empty()){
                                    for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                        int it = *i;
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
                        int T0 = currentTuple->at(0);
                        int T1 = currentTuple->at(1);
                        std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                        const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                        const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                        int aggrIdIt=tuplesU->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        int& posSum = possibleSum[aggrIdIt];
                        if(actSum >= 6+1){
                            int itProp = tuplesU->at(i);
                            for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                int it = *j;
                                shared_reason.get()->insert(it);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else if(actSum < 6+1 - posSum){
                            int itProp = tuplesU->at(i);
                            const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                            for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                                int it = *j;
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
                                int T0 = tuple0->at(0);
                                int T1 = tuple0->at(1);
                                const Tuple* tuple1 = factory.find({T0,T1},&_aggr_id0);
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
                                    Tuple negativeTuple({T0,T1},&_aggr_id1);
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
                                        if(tupleU != NULL){
                                            std::cout<<"Constraint propagation 7"<<std::endl;
                                            if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                            else internalProps.push_back({tupleU,tupleUNegated});
                                        }else{
                                            std::cout<<"Conflict On Constraint 7"<<std::endl;
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
                                if(tuple0->at(0)==tuple0->at(1)){
                                    int T2 = tuple0->at(0);
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
                                            int T1 = tuple1->at(0);
                                            int T3 = tuple1->at(1);
                                            const std::vector<int>* tuples = &pdomBody_.getValuesVec({});
                                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                                            std::vector<const Tuple*> undeRepeated;
                                            if(tupleU == NULL)
                                                tuplesU = &udomBody_.getValuesVec({});
                                            else if(tupleU->getPredicateName() == &_domBody && !tupleUNegated)
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
                                                    int T0 = tuple2->at(0);
                                                    Tuple negativeTuple({T2,T0,T2},&_l2);
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
                                                                if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple3))
                                                                tuple3=NULL;
                                                            }
                                                        }
                                                    }
                                                    if(tuple3!=NULL){
                                                        Tuple negativeTuple({T2,T1,T0,T3},&_aux0);
                                                        const Tuple* tuple4 = factory.find(negativeTuple);
                                                        if(tuple4 == NULL)
                                                            tuple4 = &negativeTuple;
                                                        else{
                                                            if(tuple4->isTrue())
                                                                tuple4 = NULL;
                                                            else if(tuple4->isUndef()){
                                                                if(tupleU == NULL){
                                                                    tupleU = tuple4;
                                                                    tupleUNegated=true;
                                                                }else{
                                                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple4))
                                                                    tuple4=NULL;
                                                                }
                                                            }
                                                        }
                                                        if(tuple4!=NULL){
                                                            if(tupleU != NULL){
                                                                std::cout<<"Constraint propagation 4"<<std::endl;
                                                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                                else internalProps.push_back({tupleU,tupleUNegated});
                                                            }else{
                                                                std::cout<<"Conflict On Constraint 4"<<std::endl;
                                                                propagatedLiterals.push_back(1);
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
                                int T2 = tuple0->at(0);
                                int T1 = tuple0->at(1);
                                int T0 = tuple0->at(2);
                                int T3 = tuple0->at(3);
                                const Tuple* tuple1 = factory.find({T2,T0,T2},&_l2);
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
                                        std::cout<<"Constraint propagation 3"<<std::endl;
                                        if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                        else internalProps.push_back({tupleU,tupleUNegated});
                                    }else{
                                        std::cout<<"Conflict On Constraint 3"<<std::endl;
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
                                int T2 = tuple0->at(0);
                                int T1 = tuple0->at(1);
                                int T0 = tuple0->at(2);
                                int T3 = tuple0->at(3);
                                Tuple negativeTuple({T1,T3},&_l0);
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
                                        std::cout<<"Constraint propagation 2"<<std::endl;
                                        if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                        else internalProps.push_back({tupleU,tupleUNegated});
                                    }else{
                                        std::cout<<"Conflict On Constraint 2"<<std::endl;
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
                                int T2 = tuple0->at(0);
                                int T1 = tuple0->at(1);
                                int T0 = tuple0->at(2);
                                int T3 = tuple0->at(3);
                                Tuple negativeTuple({T2,T2},&_l1);
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
                                        std::cout<<"Constraint propagation 1"<<std::endl;
                                        if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                        else internalProps.push_back({tupleU,tupleUNegated});
                                    }else{
                                        std::cout<<"Conflict On Constraint 1"<<std::endl;
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
                    const IndexedSet* trueHeads = &paggr_set0_.getValuesSet({});
                    for(auto itTrueHead = trueHeads->begin();itTrueHead != trueHeads->end(); itTrueHead++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(*itTrueHead);
                        int T2 = currentHead->at(0);
                        int T1 = currentHead->at(1);
                        int T0 = currentHead->at(2);
                        const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({T2, T1, T0});
                        const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({T2, T1, T0});
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
                    const IndexedSet* falseHeads = &faggr_set0_.getValuesSet({});
                    for(auto itFalseHead = falseHeads->begin();itFalseHead != falseHeads->end(); itFalseHead++){
                        const Tuple* currentHead = factory.getTupleFromInternalID(*itFalseHead);
                        int T2 = currentHead->at(0);
                        int T1 = currentHead->at(1);
                        int T0 = currentHead->at(2);
                        const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({T2, T1, T0});
                        const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({T2, T1, T0});
                        if(tuples->size()>0){
                            propagatedLiterals.push_back(1);
                            return;
                        }else{
                        while(!tuplesU->empty()){
                            propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }
                const IndexedSet* undefHeads = &uaggr_set0_.getValuesSet({});
                std::vector<std::pair<const Tuple*,bool>> props0;
                for(auto itUndefHead = undefHeads->begin(); itUndefHead != undefHeads->end(); itUndefHead++){
                    const Tuple* currentHead = factory.getTupleFromInternalID(*itUndefHead);
                    int T2 = currentHead->at(0);
                    int T1 = currentHead->at(1);
                    int T0 = currentHead->at(2);
                    const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({T2, T1, T0});
                    const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({T2, T1, T0});
                    if(tuples->size() > 0)
                        props0.push_back({currentHead,false});
                    else if(tuplesU->size()==0)
                        props0.push_back({currentHead,true});
                }
                for(auto pair : props0)
                    propUndefined(pair.first,false,propagationStack,pair.second,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }//close decision level == -1
        std::vector<int> propagated;
        while(!propagationStack.empty()){
            int startVar = propagationStack.back();
            propagated.push_back(startVar);
            int uStartVar = startVar<0 ? -startVar : startVar;
            Tuple starter (*factory.getTupleFromInternalID(uStartVar));
            std::string minus = startVar < 0 ? "not " : "";
            std::cout<<"Starter "<<minus;starter.print();
            propagationStack.pop_back();
            if(starter.getPredicateName() == &_aux0){
                int T2 = starter.at(0);
                int T1 = starter.at(1);
                int T0 = starter.at(2);
                int T3 = starter.at(3);
                Tuple* head = factory.find({T2,T1,T0}, &_aggr_set0);
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
                    std::cout<<"Propagation starting from false body"<<std::endl;
                    const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({T2, T1, T0});
                    const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({T2, T1, T0});
                    std::cout<<"Evaluating"<<std::endl;
                    if(head == NULL) std::cout << "Null head "<<std::endl;
                    else if(head->isFalse()) std::cout << "False head "<<std::endl;
                    if(head != NULL && head->isTrue()){
                        std::cout<<"head is true"<<std::endl;
                        if(tuples->size() == 0 && tuplesU->size() == 0){
                            std::cout<<"Conflict: unable to find support for true head 0"<<std::endl;
                            int itHead = head->getId();
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({T2, T1, T0});
                            for(unsigned i=0;i<tuplesF->size();i++){
                                int it = tuplesF->at(i);
                                shared_reason.get()->insert(-it);
                            }
                            reasonForLiteral[-itHead]=shared_reason;
                            handleConflict(-itHead, propagatedLiterals);
                            return;
                        }else if(tuples->size() == 0 && tuplesU->size() == 1){
                            std::cout<<"Propagation: prop support for head 0"<<std::endl;
                            int itProp = tuplesU->at(0);
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({T2, T1, T0});
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
                        std::cout<<"head is undef"<<std::endl;
                        if(tuples->size() == 0 && tuplesU->size() == 0){
                            std::cout<<"Propagation: head without support 0"<<std::endl;
                            int itHead = head->getId();
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({T2, T1, T0});
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
            }else if(starter.getPredicateName() == &_aggr_set0){
                int T2 = starter.at(0);
                int T1 = starter.at(1);
                int T0 = starter.at(2);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                const std::vector<int>* tuples = &paux0_0_1_2_.getValuesVec({T2,T1,T0});
                const std::vector<int>* tuplesU = &uaux0_0_1_2_.getValuesVec({T2,T1,T0});
                if(startVar > 0){
                    if(tuples->size()==0){
                        if(tuplesU->size() == 0){
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({T2,T1,T0});
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
                            const std::vector<int>* tuplesF = &faux0_0_1_2_.getValuesVec({T2,T1,T0});
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
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                if(T2 == starter[1]){
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &paux0_0_.getValuesVec({T2});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_0_.getValuesVec({T2});
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
                            if(tupleU->at(0) == T2)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int T1 = tuple1->at(1);
                            int T0 = tuple1->at(2);
                            int T3 = tuple1->at(3);
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                std::cout<<"compute reason for "<<var<<std::endl;
                                if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                std::cout<<"Constraint propagation 1"<<std::endl;
                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::cout<<"Conflict On Constraint 1"<<std::endl;
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
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                int T1 = starter[1];
                int T0 = starter[2];
                int T3 = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({T2,T2},&_l1);
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
                        std::cout<<"compute reason for "<<var<<std::endl;
                        if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                        std::cout<<"Constraint propagation 1"<<std::endl;
                        if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::cout<<"Conflict On Constraint 1"<<std::endl;
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
            if(starter.getPredicateName() == &_l0 && startVar < 0){
                std::cout<<"Constraint propagation"<<std::endl;
                int T1 = starter[0];
                int T3 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux0_1_3_.getValuesVec({T1,T3});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux0_1_3_.getValuesVec({T1,T3});
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
                        if(tupleU->at(1) == T1 && tupleU->at(3) == T3)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T2 = tuple1->at(0);
                        int T0 = tuple1->at(2);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            std::cout<<"compute reason for "<<var<<std::endl;
                            if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                            std::cout<<"Constraint propagation 2"<<std::endl;
                            if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            else internalProps.push_back({tupleU,tupleUNegated});
                        }else{
                            std::cout<<"Conflict On Constraint 2"<<std::endl;
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
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                int T1 = starter[1];
                int T0 = starter[2];
                int T3 = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({T1,T3},&_l0);
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
                        std::cout<<"compute reason for "<<var<<std::endl;
                        if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                        std::cout<<"Constraint propagation 2"<<std::endl;
                        if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::cout<<"Conflict On Constraint 2"<<std::endl;
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
            if(starter.getPredicateName() == &_l2 && startVar > 0){
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                int T0 = starter[1];
                if(T2 == starter[2]){
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const std::vector<int>* tuples = &paux0_0_2_.getValuesVec({T2,T0});
                    const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_0_2_.getValuesVec({T2,T0});
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
                            if(tupleU->at(0) == T2 && tupleU->at(2) == T0)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int T1 = tuple1->at(1);
                            int T3 = tuple1->at(3);
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                std::cout<<"compute reason for "<<var<<std::endl;
                                if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                std::cout<<"Constraint propagation 3"<<std::endl;
                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                else internalProps.push_back({tupleU,tupleUNegated});
                            }else{
                                std::cout<<"Conflict On Constraint 3"<<std::endl;
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
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                int T1 = starter[1];
                int T0 = starter[2];
                int T3 = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({T2,T0,T2},&_l2);
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
                        std::cout<<"compute reason for "<<var<<std::endl;
                        if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                        std::cout<<"Constraint propagation 3"<<std::endl;
                        if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        else internalProps.push_back({tupleU,tupleUNegated});
                    }else{
                        std::cout<<"Conflict On Constraint 3"<<std::endl;
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
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                int T1 = starter[1];
                int T0 = starter[2];
                int T3 = starter[3];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({T2,T2},&_l1);
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
                    const Tuple* tuple2 = factory.find({T1,T3},&_l0);
                    if(tuple2!=NULL){
                        if(tuple2->isFalse())
                        tuple2=NULL;
                        else if(tuple2->isUndef()){
                            if(tupleU == NULL){
                                tupleU = tuple2;
                                tupleUNegated=false;
                            }else{
                                if(tupleU->getPredicateName() != &_l0 || tupleUNegated || !(*tupleU == *tuple2))
                                tuple2=NULL;
                            }
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple negativeTuple({T2,T0,T2},&_l2);
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
                                    if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple3))
                                    tuple3=NULL;
                                }
                            }
                        }
                        if(tuple3!=NULL){
                            const Tuple* tuple4 = factory.find({T0},&_domBody);
                            if(tuple4!=NULL){
                                if(tuple4->isFalse())
                                tuple4=NULL;
                                else if(tuple4->isUndef()){
                                    if(tupleU == NULL){
                                        tupleU = tuple4;
                                        tupleUNegated=false;
                                    }else{
                                        if(tupleU->getPredicateName() != &_domBody || tupleUNegated || !(*tupleU == *tuple4))
                                        tuple4=NULL;
                                    }
                                }
                            }
                            if(tuple4!=NULL){
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    std::cout<<"compute reason for "<<var<<std::endl;
                                    if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                    if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                        int it = tuple4->getId();
                                        shared_reason.get()->insert(it*1);
                                    }
                                    auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                    if(!itReason.second && itReason.first->second.get()->empty())
                                        itReason.first->second=shared_reason;
                                    std::cout<<"Constraint propagation 4"<<std::endl;
                                    if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                    else internalProps.push_back({tupleU,tupleUNegated});
                                }else{
                                    std::cout<<"Conflict On Constraint 4"<<std::endl;
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
                                    if(tuple4!=NULL){
                                        int it = tuple4->getId();
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
            if(starter.getPredicateName() == &_domBody && startVar > 0){
                std::cout<<"Constraint propagation"<<std::endl;
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
                        if(tuple1->at(0)==tuple1->at(1)){
                            int T2 = tuple1->at(0);
                            Tuple negativeTuple({T2,T0,T2},&_l2);
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
                                        if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple2))
                                        tuple2=NULL;
                                    }
                                }
                            }
                            if(tuple2!=NULL){
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
                                    const Tuple* tuple3 = NULL;
                                    if(i<tuples->size())
                                        tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int T1 = tuple3->at(0);
                                        int T3 = tuple3->at(1);
                                        Tuple negativeTuple({T2,T1,T0,T3},&_aux0);
                                        const Tuple* tuple4 = factory.find(negativeTuple);
                                        if(tuple4 == NULL)
                                            tuple4 = &negativeTuple;
                                        else{
                                            if(tuple4->isTrue())
                                                tuple4 = NULL;
                                            else if(tuple4->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple4;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple4))
                                                    tuple4=NULL;
                                                }
                                            }
                                        }
                                        if(tuple4!=NULL){
                                            if(tupleU != NULL){
                                                int itUndef = tupleU->getId();
                                                int var = tupleUNegated ? 1 : -1;
                                                var*=itUndef;
                                                std::cout<<"compute reason for "<<var<<std::endl;
                                                if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                                    shared_reason.get()->insert(it*1);
                                                }
                                                if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                    int it = tuple4->getId();
                                                    shared_reason.get()->insert(it*-1);
                                                }
                                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                if(!itReason.second && itReason.first->second.get()->empty())
                                                    itReason.first->second=shared_reason;
                                                std::cout<<"Constraint propagation 4"<<std::endl;
                                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::cout<<"Conflict On Constraint 4"<<std::endl;
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
                                                if(tuple4!=NULL){
                                                    int it = tuple4->getId();
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
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_l2 && startVar < 0){
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                int T0 = starter[1];
                if(T2 == starter[2]){
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    std::vector<std::pair<const Tuple*,bool>> internalProps;
                    const Tuple* tuple1 = factory.find({T2,T2},&_l1);
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
                        const Tuple* tuple2 = factory.find({T0},&_domBody);
                        if(tuple2!=NULL){
                            if(tuple2->isFalse())
                            tuple2=NULL;
                            else if(tuple2->isUndef()){
                                if(tupleU == NULL){
                                    tupleU = tuple2;
                                    tupleUNegated=false;
                                }else{
                                    if(tupleU->getPredicateName() != &_domBody || tupleUNegated || !(*tupleU == *tuple2))
                                    tuple2=NULL;
                                }
                            }
                        }
                        if(tuple2!=NULL){
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
                                const Tuple* tuple3 = NULL;
                                if(i<tuples->size())
                                    tuple3 = factory.getTupleFromInternalID(tuples->at(i));
                                else if(i<tuples->size()+tuplesU->size()){
                                    tupleU = tuple3 = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                                    tupleUNegated=false;
                                }else if(!undeRepeated.empty()){
                                    tuple3 = tupleU;
                                }
                                if(tuple3!=NULL){
                                    int T1 = tuple3->at(0);
                                    int T3 = tuple3->at(1);
                                    Tuple negativeTuple({T2,T1,T0,T3},&_aux0);
                                    const Tuple* tuple4 = factory.find(negativeTuple);
                                    if(tuple4 == NULL)
                                        tuple4 = &negativeTuple;
                                    else{
                                        if(tuple4->isTrue())
                                            tuple4 = NULL;
                                        else if(tuple4->isUndef()){
                                            if(tupleU == NULL){
                                                tupleU = tuple4;
                                                tupleUNegated=true;
                                            }else{
                                                if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple4))
                                                tuple4=NULL;
                                            }
                                        }
                                    }
                                    if(tuple4!=NULL){
                                        if(tupleU != NULL){
                                            int itUndef = tupleU->getId();
                                            int var = tupleUNegated ? 1 : -1;
                                            var*=itUndef;
                                            std::cout<<"compute reason for "<<var<<std::endl;
                                            if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                            if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                int it = tuple4->getId();
                                                shared_reason.get()->insert(it*-1);
                                            }
                                            auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                            if(!itReason.second && itReason.first->second.get()->empty())
                                                itReason.first->second=shared_reason;
                                            std::cout<<"Constraint propagation 4"<<std::endl;
                                            if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                            else internalProps.push_back({tupleU,tupleUNegated});
                                        }else{
                                            std::cout<<"Conflict On Constraint 4"<<std::endl;
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
                                            if(tuple4!=NULL){
                                                int it = tuple4->getId();
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
                    }
                    for(auto pair : internalProps)
                        propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
            if(starter.getPredicateName() == &_l0 && startVar > 0){
                std::cout<<"Constraint propagation"<<std::endl;
                int T1 = starter[0];
                int T3 = starter[1];
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
                        if(tuple1->at(0)==tuple1->at(1)){
                            int T2 = tuple1->at(0);
                            const std::vector<int>* tuples = &pdomBody_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &udomBody_.getValuesVec({});
                            else if(tupleU->getPredicateName() == &_domBody && !tupleUNegated)
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
                                    int T0 = tuple2->at(0);
                                    Tuple negativeTuple({T2,T0,T2},&_l2);
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
                                                if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
                                        Tuple negativeTuple({T2,T1,T0,T3},&_aux0);
                                        const Tuple* tuple4 = factory.find(negativeTuple);
                                        if(tuple4 == NULL)
                                            tuple4 = &negativeTuple;
                                        else{
                                            if(tuple4->isTrue())
                                                tuple4 = NULL;
                                            else if(tuple4->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple4;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple4))
                                                    tuple4=NULL;
                                                }
                                            }
                                        }
                                        if(tuple4!=NULL){
                                            if(tupleU != NULL){
                                                int itUndef = tupleU->getId();
                                                int var = tupleUNegated ? 1 : -1;
                                                var*=itUndef;
                                                std::cout<<"compute reason for "<<var<<std::endl;
                                                if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                                if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                    int it = tuple4->getId();
                                                    shared_reason.get()->insert(it*-1);
                                                }
                                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                if(!itReason.second && itReason.first->second.get()->empty())
                                                    itReason.first->second=shared_reason;
                                                std::cout<<"Constraint propagation 4"<<std::endl;
                                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::cout<<"Conflict On Constraint 4"<<std::endl;
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
                                                if(tuple4!=NULL){
                                                    int it = tuple4->getId();
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
                        }
                    }
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_l1 && startVar > 0){
                std::cout<<"Constraint propagation"<<std::endl;
                int T2 = starter[0];
                if(T2 == starter[1]){
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
                            int T1 = tuple1->at(0);
                            int T3 = tuple1->at(1);
                            const std::vector<int>* tuples = &pdomBody_.getValuesVec({});
                            const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &udomBody_.getValuesVec({});
                            else if(tupleU->getPredicateName() == &_domBody && !tupleUNegated)
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
                                    int T0 = tuple2->at(0);
                                    Tuple negativeTuple({T2,T0,T2},&_l2);
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
                                                if(tupleU->getPredicateName() != &_l2 || !tupleUNegated || !(*tupleU == *tuple3))
                                                tuple3=NULL;
                                            }
                                        }
                                    }
                                    if(tuple3!=NULL){
                                        Tuple negativeTuple({T2,T1,T0,T3},&_aux0);
                                        const Tuple* tuple4 = factory.find(negativeTuple);
                                        if(tuple4 == NULL)
                                            tuple4 = &negativeTuple;
                                        else{
                                            if(tuple4->isTrue())
                                                tuple4 = NULL;
                                            else if(tuple4->isUndef()){
                                                if(tupleU == NULL){
                                                    tupleU = tuple4;
                                                    tupleUNegated=true;
                                                }else{
                                                    if(tupleU->getPredicateName() != &_aux0 || !tupleUNegated || !(*tupleU == *tuple4))
                                                    tuple4=NULL;
                                                }
                                            }
                                        }
                                        if(tuple4!=NULL){
                                            if(tupleU != NULL){
                                                int itUndef = tupleU->getId();
                                                int var = tupleUNegated ? 1 : -1;
                                                var*=itUndef;
                                                std::cout<<"compute reason for "<<var<<std::endl;
                                                if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                                if(factory.find(*tuple4) != NULL && tuple4!=tupleU){
                                                    int it = tuple4->getId();
                                                    shared_reason.get()->insert(it*-1);
                                                }
                                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                                if(!itReason.second && itReason.first->second.get()->empty())
                                                    itReason.first->second=shared_reason;
                                                std::cout<<"Constraint propagation 4"<<std::endl;
                                                if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                                else internalProps.push_back({tupleU,tupleUNegated});
                                            }else{
                                                std::cout<<"Conflict On Constraint 4"<<std::endl;
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
                                                if(tuple4!=NULL){
                                                    int it = tuple4->getId();
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
                        }
                    }
                    for(auto pair : internalProps)
                        propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            int T0 = starter[0];
            int T1 = starter[1];
            std::vector<int> sharedVar({starter[0],starter[1]});
            const IndexedSet* tuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
            const IndexedSet* tuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=6){
                    for(auto i =tuples->begin(); i != tuples->end(); i++){
                        int it = *i;
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else{
                    if(!tuplesU->empty()){
                        for(auto i = tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        shared_reason.get()->insert(startVar);
                    }
                    while(!tuplesU->empty()){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                        if(actSum >= 6-currentTuple->at(0)){
                            int itProp =currentTuple->getId();
                            auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else break;
                    }
                }
            }else{
                int& actSum = actualSum[uStartVar];
                int& posSum = possibleSum[uStartVar];
                if(actSum+posSum < 6){
                    const IndexedSet* tuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                    for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                        int it = *i;
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-startVar]=shared_reason;
                    handleConflict(-startVar, propagatedLiterals);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                        if(actSum < 6-posSum+currentTuple->at(0)){
                            int itProp = *tuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const IndexedSet* tuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                                for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(-it);
                                }
                                shared_reason.get()->insert(startVar);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else break;
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
                int T0 = currentTuple->at(0);
                int T1 = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < 6-posSum){
                    int itProp = tuples->at(i);
                    const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                    for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(-it);
                    }
                    reasonForLiteral[-itProp]=shared_reason;
                    handleConflict(-itProp, propagatedLiterals);
                    return;
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= 6-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                            for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(-it);
                            }
                            int itAggrId = tuples->at(i);
                            shared_reason.get()->insert(itAggrId);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                int T0 = currentTuple->at(0);
                int T1 = currentTuple->at(1);
                std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= 6){
                    int itProp = tuplesF->at(i);
                    for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(it);
                    }
                    reasonForLiteral[itProp]=shared_reason;
                    handleConflict(itProp, propagatedLiterals);
                    return;
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < 6-currentJoinTuple->at(0))break;
                            if(shared_reason.get()->empty()){
                                for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                    int it = *i;
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
                    int T0 = currentTuple->at(0);
                    int T1 = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                    const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                    const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesU->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum >= 6){
                        int itProp = tuplesU->at(i);
                        for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                        if(!itReason.second && itReason.first->second.get()->empty())
                            itReason.first->second=shared_reason;
                        propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }else if(actSum < 6 - posSum){
                        int itProp = tuplesU->at(i);
                        const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
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
            if(starter.getPredicateName() == &_aggr_id1){
                int T0 = starter[0];
                int T1 = starter[1];
                std::vector<int> sharedVar({starter[0],starter[1]});
                const IndexedSet* tuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                const IndexedSet* tuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                if(startVar < 0){
                    int& actSum = actualSum[uStartVar];
                    if(actSum>=6+1){
                        for(auto i =tuples->begin(); i != tuples->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }else{
                        if(!tuplesU->empty()){
                            for(auto i = tuples->begin(); i != tuples->end(); i++){
                                int it = *i;
                                shared_reason.get()->insert(it);
                            }
                            shared_reason.get()->insert(startVar);
                        }
                        while(!tuplesU->empty()){
                            const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                            if(actSum >= 6+1-currentTuple->at(0)){
                                int itProp =currentTuple->getId();
                                auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else break;
                        }
                    }
                }else{
                    int& actSum = actualSum[uStartVar];
                    int& posSum = possibleSum[uStartVar];
                    if(actSum+posSum < 6+1){
                        const IndexedSet* tuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                        for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                            int it = *i;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-startVar]=shared_reason;
                        handleConflict(-startVar, propagatedLiterals);
                        return;
                    }else{
                        while(!tuplesU->empty()){
                            const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());
                            if(actSum < 6+1-posSum+currentTuple->at(0)){
                                int itProp = *tuplesU->begin();
                                if(shared_reason.get()->empty()){
                                    const IndexedSet* tuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                                    for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){
                                        int it = *i;
                                        shared_reason.get()->insert(-it);
                                    }
                                    shared_reason.get()->insert(startVar);
                                }
                                auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                            }else break;
                        }
                    }
                }
            }//close aggr id starter
            if(starter.getPredicateName() == &_aggr_set0){
                const std::vector<int>* tuples = &paggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesU = &uaggr_id1_.getValuesVec({});
                const std::vector<int>* tuplesF = &faggr_id1_.getValuesVec({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                    int T0 = currentTuple->at(0);
                    int T1 = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                    const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                    const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                    int aggrIdIt=tuples->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    int& posSum = possibleSum[aggrIdIt];
                    if(actSum < 6+1-posSum){
                        int itProp = tuples->at(i);
                        const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                        for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itProp]=shared_reason;
                        handleConflict(-itProp, propagatedLiterals);
                        return;
                    }else{
                        while(!joinTuplesU->empty()){
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                            if(actSum >= 6+1-posSum+currentJoinTuple->at(0)) {break;}
                            int itProp = *joinTuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                                for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){
                                    int it = *i;
                                    shared_reason.get()->insert(-it);
                                }
                                int itAggrId = tuples->at(i);
                                shared_reason.get()->insert(itAggrId);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));
                    int T0 = currentTuple->at(0);
                    int T1 = currentTuple->at(1);
                    std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                    const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                    const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                    int aggrIdIt=tuplesF->at(i);
                    std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                    int& actSum = actualSum[aggrIdIt];
                    if(actSum >= 6+1){
                        int itProp = tuplesF->at(i);
                        for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){
                            int it = *j;
                            shared_reason.get()->insert(it);
                        }
                        reasonForLiteral[itProp]=shared_reason;
                        handleConflict(itProp, propagatedLiterals);
                        return;
                    }else{
                        while(!joinTuplesU->empty()){
                            int itProp = *joinTuplesU->begin();
                            const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                            if(actSum < 6+1-currentJoinTuple->at(0))break;
                                if(shared_reason.get()->empty()){
                                    for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){
                                        int it = *i;
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
                        int T0 = currentTuple->at(0);
                        int T1 = currentTuple->at(1);
                        std::vector<int> sharedVar({currentTuple->at(0),currentTuple->at(1)});
                        const IndexedSet* joinTuples = &paggr_set0_2_1_.getValuesSet(sharedVar);
                        const IndexedSet* joinTuplesU = &uaggr_set0_2_1_.getValuesSet(sharedVar);
                        int aggrIdIt=tuplesU->at(i);
                        std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                        int& actSum = actualSum[aggrIdIt];
                        int& posSum = possibleSum[aggrIdIt];
                        if(actSum >= 6+1){
                            int itProp = tuplesU->at(i);
                            for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                                int it = *j;
                                shared_reason.get()->insert(it);
                            }
                            auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                            if(!itReason.second && itReason.first->second.get()->empty())
                                itReason.first->second=shared_reason;
                            propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                        }else if(actSum < 6+1 - posSum){
                            int itProp = tuplesU->at(i);
                            const IndexedSet* joinTuplesF = &faggr_set0_2_1_.getValuesSet(sharedVar);
                            for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){
                                int it = *j;
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
                    if(starter.getPredicateName() == &_aggr_id1 && startVar < 0){
                        std::cout<<"Constraint propagation"<<std::endl;
                        int T0 = starter[0];
                        int T1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({T0,T1},&_l0);
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
                            const Tuple* tuple2 = factory.find({T0,T1},&_aggr_id0);
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
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    std::cout<<"compute reason for "<<var<<std::endl;
                                    if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                    std::cout<<"Constraint propagation 7"<<std::endl;
                                    if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                    else internalProps.push_back({tupleU,tupleUNegated});
                                }else{
                                    std::cout<<"Conflict On Constraint 7"<<std::endl;
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
                    if(starter.getPredicateName() == &_aggr_id0 && startVar > 0){
                        std::cout<<"Constraint propagation"<<std::endl;
                        int T0 = starter[0];
                        int T1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({T0,T1},&_l0);
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
                            Tuple negativeTuple({T0,T1},&_aggr_id1);
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
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    std::cout<<"compute reason for "<<var<<std::endl;
                                    if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                    std::cout<<"Constraint propagation 7"<<std::endl;
                                    if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                    else internalProps.push_back({tupleU,tupleUNegated});
                                }else{
                                    std::cout<<"Conflict On Constraint 7"<<std::endl;
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
                    if(starter.getPredicateName() == &_l0 && startVar > 0){
                        std::cout<<"Constraint propagation"<<std::endl;
                        int T0 = starter[0];
                        int T1 = starter[1];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        std::vector<std::pair<const Tuple*,bool>> internalProps;
                        const Tuple* tuple1 = factory.find({T0,T1},&_aggr_id0);
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
                            Tuple negativeTuple({T0,T1},&_aggr_id1);
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
                                if(tupleU != NULL){
                                    int itUndef = tupleU->getId();
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef;
                                    std::cout<<"compute reason for "<<var<<std::endl;
                                    if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<"InMap But NULL"<<std::endl; else std::cout<<"InMap not null"<<std::endl;
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
                                    std::cout<<"Constraint propagation 7"<<std::endl;
                                    if(tupleU->getPredicateName() != &_aggr_id1 && tupleU->getPredicateName() != &_aggr_id0 && tupleU->getPredicateName() != &_aggr_set0 && tupleU->getPredicateName() != &_aux0)
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                                    else internalProps.push_back({tupleU,tupleUNegated});
                                }else{
                                    std::cout<<"Conflict On Constraint 7"<<std::endl;
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
            }
            if(conflictCount > minConflict && propagatedLiterals.size() > 1){int currentHeapSize = propagatedLiterals.size() < heapSize ? propagatedLiterals.size() : heapSize; /*std::cout<<"sort heap: "<<currentHeapSize<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+currentHeapSize,propComparison);}
        }
        }
