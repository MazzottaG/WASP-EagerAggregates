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
const std::string _agg_id_0 = "agg_id_0";
const std::string _agg_id_1 = "agg_id_1";
const std::string _agg_set_0 = "agg_set_0";
const std::string _aux_0 = "aux_0";
const std::string _l0 = "l0";
const std::string _l1 = "l1";
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
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
AuxMap<64> paux_0_0_1_({0,1});
AuxMap<64> uaux_0_0_1_({0,1});
AuxMap<64> faux_0_0_1_({0,1});
AuxMap<0> paux_0_({});
AuxMap<0> uaux_0_({});
AuxMap<0> faux_0_({});
AuxMap<0> pagg_set_0_({});
AuxMap<0> uagg_set_0_({});
AuxMap<0> fagg_set_0_({});
AuxMap<0> pl0_({});
AuxMap<0> ul0_({});
AuxMap<0> fl0_({});
AuxMap<32> paux_0_1_({1});
AuxMap<32> uaux_0_1_({1});
AuxMap<32> faux_0_1_({1});
AuxMap<32> paux_0_0_({0});
AuxMap<32> uaux_0_0_({0});
AuxMap<32> faux_0_0_({0});
AuxMap<0> pl1_({});
AuxMap<0> ul1_({});
AuxMap<0> fl1_({});
AuxMap<32> paux_0_2_({2});
AuxMap<32> uaux_0_2_({2});
AuxMap<32> faux_0_2_({2});
AuxMap<0> pagg_id_0_({});
AuxMap<0> uagg_id_0_({});
AuxMap<0> fagg_id_0_({});
AuxMap<0> pagg_id_1_({});
AuxMap<0> uagg_id_1_({});
AuxMap<0> fagg_id_1_({});
void Executor::handleConflict(int literal,std::vector<int>& propagatedLiterals){
    if(currentDecisionLevel <= 0){
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
        Tuple* waspTuple = factory.getTupleFromWASPID(uVar);
        if(waspTuple==NULL) std::cout << "WARNING: Unable to find tuple from wasp id in explainExternalLiteral"<<std::endl;
        int internalVar = waspTuple->getId();
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
                if(literal==NULL) std::cout << "WARNING: Unable to find tuple in reason "<<reasonLiteral<<std::endl;
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
    if(insertResult.first->getPredicateName() == &_agg_id_0){
        fagg_id_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_1){
        fagg_id_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        fl1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        fl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_set_0){
        fagg_set_0_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_0){
        faux_0_.insert2Vec(*insertResult.first);
        faux_0_0_.insert2Vec(*insertResult.first);
        faux_0_0_1_.insert2Vec(*insertResult.first);
        faux_0_1_.insert2Vec(*insertResult.first);
        faux_0_2_.insert2Vec(*insertResult.first);
    }
}
inline void insertTrue(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_agg_id_0){
        pagg_id_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_1){
        pagg_id_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        pl1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        pl0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_set_0){
        pagg_set_0_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_0){
        paux_0_.insert2Vec(*insertResult.first);
        paux_0_0_.insert2Vec(*insertResult.first);
        paux_0_0_1_.insert2Vec(*insertResult.first);
        paux_0_1_.insert2Vec(*insertResult.first);
        paux_0_2_.insert2Vec(*insertResult.first);
    }
}
inline void insertUndef(const std::pair<const TupleLight *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == &_agg_id_0){
        uagg_id_0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_id_1){
        uagg_id_1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l1){
        ul1_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_l0){
        ul0_.insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_agg_set_0){
        uagg_set_0_.insert2Set(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == &_aux_0){
        uaux_0_.insert2Vec(*insertResult.first);
        uaux_0_0_.insert2Vec(*insertResult.first);
        uaux_0_0_1_.insert2Vec(*insertResult.first);
        uaux_0_1_.insert2Vec(*insertResult.first);
        uaux_0_2_.insert2Vec(*insertResult.first);
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
void checkFoundness(){
    std::unordered_set<int> visited;
    while(!falseLits.empty()){
        int current = falseLits.back();
        falseLits.pop_back();
        if(current > 0 || visited.count(current)!=0) continue;
        visited.insert(current);
        const Tuple* tuple = factory.getTupleFromInternalID(-current);
        if(tuple != NULL){
            if(!tuple->isFalse()){
                auto it = predsToUnfoundedSet.find(tuple->getPredicateName());
                if(it!=predsToUnfoundedSet.end())
                    it->second->insert(tuple->getId());
            }
        }//close if
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
    {
        Tuple* aggr_id = factory.addNewInternalTuple({},&_agg_id_1);
        const auto& insertResult = aggr_id->setStatus(Undef);
        if(insertResult.second){
            factory.removeFromCollisionsList(aggr_id->getId());
            insertUndef(insertResult);
        }
    }
    {
        Tuple* aggr_id = factory.addNewInternalTuple({},&_agg_id_0);
        const auto& insertResult = aggr_id->setStatus(Undef);
        if(insertResult.second){
            factory.removeFromCollisionsList(aggr_id->getId());
            insertUndef(insertResult);
        }
    }
    {
        const std::vector<int>* tuples = &pl0_.getValuesVec({});
        const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
        for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
            Tuple* tuple0 = NULL;
            if(i<tuples->size()) tuple0=factory.getTupleFromInternalID(tuples->at(i));
            else tuple0=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
            int T0 = tuple0->at(0);
            const std::vector<int>* tuples = &pl0_.getValuesVec({});
            const std::vector<int>* tuplesU = &ul0_.getValuesVec({});
            for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                Tuple* tuple1 = NULL;
                if(i<tuples->size()) tuple1=factory.getTupleFromInternalID(tuples->at(i));
                else tuple1=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                int T1 = tuple1->at(0);
                const std::vector<int>* tuples = &pl1_.getValuesVec({});
                const std::vector<int>* tuplesU = &ul1_.getValuesVec({});
                for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){
                    Tuple* tuple2 = NULL;
                    if(i<tuples->size()) tuple2=factory.getTupleFromInternalID(tuples->at(i));
                    else tuple2=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));
                    int T2 = tuple2->at(0);
                    Tuple* saving2 = factory.addNewInternalTuple({T1,T0,T2},&_aux_0);
                    const auto& insertResult = saving2->setStatus(Undef);
                    if(insertResult.second){
                        factory.removeFromCollisionsList(saving2->getId());
                        insertUndef(insertResult);
                        Tuple* saving0 = factory.addNewInternalTuple({T1,T0},&_agg_set_0);
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
    std::vector<int> ordered_ids;
    std::vector<int> tuplesIdOrdered;
    std::map<int, Tuple*> idToTuples;
    int currentIdIndex=0;
    {
        const IndexedSet tuples = uagg_set_0_.getValuesSet({});
        ordered_ids.reserve(tuples.size());
        tuplesIdOrdered.reserve(tuples.size());
        for(int id :tuples){
            tuplesIdOrdered.push_back(id);
            ordered_ids.push_back(id);
            idToTuples[id]=factory.getTupleFromInternalID(id);
            factory.removeFromCollisionsList(id);
            idToTuples[id]->setStatus(UNKNOWN);
        }
        std::stable_sort(tuplesIdOrdered.begin(),tuplesIdOrdered.end(),compTuple);
        for(int id: tuplesIdOrdered){
            Tuple* t=idToTuples[id];
            factory.setId(t,ordered_ids[currentIdIndex++]);
            const auto& insertResult = t->setStatus(Undef);
            if (insertResult.second) {
                factory.removeFromCollisionsList(t->getId());
                insertUndef(insertResult);
            }
        }
        ordered_ids.clear();
        tuplesIdOrdered.clear();
        idToTuples.clear();
        currentIdIndex=0;
    }
    {
        Tuple* aggr_id = factory.find({},&_agg_id_0);
        const IndexedSet* aggrSet = &pagg_set_0_.getValuesSet({});
        const IndexedSet* aggrSetU = &uagg_set_0_.getValuesSet({});
        auto itTrue = aggrSet->begin();
        auto itUndef = aggrSetU->begin();
        std::cout<<"SUM "<<aggr_id->getId()<<std::endl;
        int& sum = possibleSum[aggr_id->getId()];
        std::cout<<"WHILE"<<std::endl;
        while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){
            Tuple* tuple = NULL;
            bool undefTuple = false;
            if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
            else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}
            int T1 = tuple->at(0);
            int T0 = tuple->at(1);
            sum+=T1;
        }
    }
    {
        Tuple* aggr_id = factory.find({},&_agg_id_1);
        const IndexedSet* aggrSet = &pagg_set_0_.getValuesSet({});
        const IndexedSet* aggrSetU = &uagg_set_0_.getValuesSet({});
        auto itTrue = aggrSet->begin();
        auto itUndef = aggrSetU->begin();
        std::cout<<"SUM "<<aggr_id->getId()<<std::endl;
        int& sum = possibleSum[aggr_id->getId()];
        std::cout<<"WHILE"<<std::endl;
        while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){
            Tuple* tuple = NULL;
            bool undefTuple = false;
            if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}
            else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}
            int T1 = tuple->at(0);
            int T0 = tuple->at(1);
            sum+=T1;
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
    pagg_id_0_.clear();
    pagg_id_1_.clear();
    pagg_set_0_.clear();
    fagg_id_0_.clear();
    fagg_id_1_.clear();
    fagg_set_0_.clear();
}
void Executor::init() {
    stringToUniqueStringPointer["agg_id_0"] = &_agg_id_0;
    stringToUniqueStringPointer["agg_id_1"] = &_agg_id_1;
    stringToUniqueStringPointer["agg_set_0"] = &_agg_set_0;
    stringToUniqueStringPointer["aux_0"] = &_aux_0;
    stringToUniqueStringPointer["l0"] = &_l0;
    stringToUniqueStringPointer["l1"] = &_l1;
    factory.setIndexForAggregateSet(0,&_agg_set_0);
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
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        int itAggrId = factory.find({},&_agg_id_0)->getId();
                        actualSum[itAggrId]+=tupleU->at(0);
                        possibleSum[itAggrId]-=tupleU->at(0);
                    }
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        int itAggrId = factory.find({},&_agg_id_1)->getId();
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
                    falseLits.push_back(-realTupleU->getId());
                    insertFalse(insertResult);
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        int itAggrId = factory.find({},&_agg_id_0)->getId();
                        possibleSum[itAggrId]-=tupleU->at(0);
                    }
                    if(tupleU->getPredicateName() == &_agg_set_0){
                        int itAggrId = factory.find({},&_agg_id_1)->getId();
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
std::string Executor::printInternalLiterals(){
    std::string trueConstraint = "";
    std::cout << std::endl;
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
            if(tuple->getPredicateName() == &_agg_set_0){
                int itAggrId = factory.find({},&_agg_id_0)->getId();
                if(var>0)
                    actualSum[itAggrId]-=tuple->at(0);
                possibleSum[itAggrId]+=tuple->at(0);
            }
            if(tuple->getPredicateName() == &_agg_set_0){
                int itAggrId = factory.find({},&_agg_id_1)->getId();
                if(var>0)
                    actualSum[itAggrId]-=tuple->at(0);
                possibleSum[itAggrId]+=tuple->at(0);
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
            propUndefined(factory.getTupleFromInternalID(factVar),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
        }
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            const std::vector<int>* tuples = &pagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < 9-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= 9-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= 9){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < 9-currentJoinTuple->at(0))break;
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= 9){
                    int itProp = tuplesU->at(i);
                    for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < 9 - posSum){
                    int itProp = tuplesU->at(i);
                    const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
            const std::vector<int>* tuples = &pagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_1_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < 9+1-posSum){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());
                        if(actSum >= 9+1-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= 9+1){
                    propagatedLiterals.push_back(1);
                }else{
                    while(!joinTuplesU->empty()){
                        int itProp = *joinTuplesU->begin();
                        const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);
                        if(actSum < 9+1-currentJoinTuple->at(0))break;
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= 9+1){
                    int itProp = tuplesU->at(i);
                    for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < 9+1 - posSum){
                    int itProp = tuplesU->at(i);
                    const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                const Tuple* tuple0 = factory.find({},&_agg_id_0);
                if(tuple0!=NULL){
                    if(tuple0->isFalse())
                    tuple0=NULL;
                    else if(tuple0->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple0;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_agg_id_0 || tupleUNegated || !(*tupleU == *tuple0))
                            tuple0=NULL;
                        }
                    }
                }
                if(tuple0!=NULL){
                    Tuple negativeTuple({},&_agg_id_1);
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
                                if(tupleU->getPredicateName() != &_agg_id_1 || !tupleUNegated || !(*tupleU == *tuple1))
                                tuple1=NULL;
                            }
                        }
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                                        int T2 = tuple2->at(0);
                                        Tuple negativeTuple({T1,T0,T2},&_aux_0);
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
                                                    if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
                                                    tuple3=NULL;
                                                }
                                            }
                                        }
                                        if(tuple3!=NULL){
                                            if(tupleU != NULL){
                                                if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                const std::vector<int>* tuples = &paux_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        int T2 = tuple0->at(2);
                        Tuple negativeTuple({T2},&_l1);
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
                                if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                const std::vector<int>* tuples = &paux_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        int T2 = tuple0->at(2);
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
                            if(tupleU != NULL){
                                if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                const std::vector<int>* tuples = &paux_0_.getValuesVec({});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_.getValuesVec({});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        int T2 = tuple0->at(2);
                        Tuple negativeTuple({T0},&_l0);
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
                                if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            const IndexedSet* trueHeads = &pagg_set_0_.getValuesSet({});
            for(auto itTrueHead = trueHeads->begin();itTrueHead != trueHeads->end(); itTrueHead++){
                const Tuple* currentHead = factory.getTupleFromInternalID(*itTrueHead);
                int T1 = currentHead->at(0);
                int T0 = currentHead->at(1);
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({T1, T0});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({T1, T0});
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
            const IndexedSet* falseHeads = &fagg_set_0_.getValuesSet({});
            for(auto itFalseHead = falseHeads->begin();itFalseHead != falseHeads->end(); itFalseHead++){
                const Tuple* currentHead = factory.getTupleFromInternalID(*itFalseHead);
                int T1 = currentHead->at(0);
                int T0 = currentHead->at(1);
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({T1, T0});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({T1, T0});
                if(tuples->size()>0){
                    propagatedLiterals.push_back(1);
                    return;
                }else{
                    while(!tuplesU->empty()){
                        propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                    }
                }
            }
            const IndexedSet* undefHeads = &uagg_set_0_.getValuesSet({});
            std::vector<std::pair<const Tuple*,bool>> props3;
            for(auto itUndefHead = undefHeads->begin(); itUndefHead != undefHeads->end(); itUndefHead++){
                const Tuple* currentHead = factory.getTupleFromInternalID(*itUndefHead);
                int T1 = currentHead->at(0);
                int T0 = currentHead->at(1);
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({T1, T0});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({T1, T0});
                if(tuples->size() > 0)
                    props3.push_back({currentHead,false});
                else if(tuplesU->size()==0)
                    props3.push_back({currentHead,true});
            }
            for(auto pair : props3)
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
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aux_0){
            int T1 = starter.at(0);
            int T0 = starter.at(1);
            int T2 = starter.at(2);
            Tuple* head = factory.find({T1,T0}, &_agg_set_0);
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
                const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({T1, T0});
                const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({T1, T0});
                if(head != NULL && head->isTrue()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        int itHead = head->getId();
                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({T1, T0});
                        for(unsigned i=0;i<tuplesF->size();i++){
                            int it = tuplesF->at(i);
                            shared_reason.get()->insert(-it);
                        }
                        reasonForLiteral[-itHead]=shared_reason;
                        handleConflict(-itHead, propagatedLiterals);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size() == 1){
                        int itProp = tuplesU->at(0);
                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({T1, T0});
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
                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({T1, T0});
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
        }else if(starter.getPredicateName() == &_agg_set_0){
            int T1 = starter.at(0);
            int T0 = starter.at(1);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            const std::vector<int>* tuples = &paux_0_0_1_.getValuesVec({T1,T0});
            const std::vector<int>* tuplesU = &uaux_0_0_1_.getValuesVec({T1,T0});
            if(startVar > 0){
                if(tuples->size()==0){
                    if(tuplesU->size() == 0){
                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({T1,T0});
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
                        const std::vector<int>* tuplesF = &faux_0_0_1_.getValuesVec({T1,T0});
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
            if(starter.getPredicateName() == &_l0 && startVar < 0){
                int T0 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux_0_1_.getValuesVec({T0});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_1_.getValuesVec({T0});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        int T2 = tuple1->at(2);
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
                            if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            if(starter.getPredicateName() == &_aux_0 && startVar > 0){
                int T1 = starter[0];
                int T0 = starter[1];
                int T2 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({T0},&_l0);
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
                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            if(starter.getPredicateName() == &_l0 && startVar < 0){
                int T1 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux_0_0_.getValuesVec({T1});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_0_.getValuesVec({T1});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        int T2 = tuple1->at(2);
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
                            if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            if(starter.getPredicateName() == &_aux_0 && startVar > 0){
                int T1 = starter[0];
                int T0 = starter[1];
                int T2 = starter[2];
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
                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                int T2 = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const std::vector<int>* tuples = &paux_0_2_.getValuesVec({T2});
                const std::vector<int>* tuplesU = &EMPTY_TUPLES_VEC;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux_0_2_.getValuesVec({T2});
                else if(tupleU->getPredicateName() == &_aux_0 && !tupleUNegated)
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
                        if(tupleU->at(2) == T2)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T1 = tuple1->at(0);
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
                            if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            if(starter.getPredicateName() == &_aux_0 && startVar > 0){
                int T1 = starter[0];
                int T0 = starter[1];
                int T2 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({T2},&_l1);
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
                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            if(starter.getPredicateName() == &_aux_0 && startVar < 0){
                int T1 = starter[0];
                int T0 = starter[1];
                int T2 = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({T0},&_l0);
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
                    const Tuple* tuple2 = factory.find({T1},&_l0);
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
                        const Tuple* tuple3 = factory.find({T2},&_l1);
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
                                auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                if(!itReason.second && itReason.first->second.get()->empty())
                                    itReason.first->second=shared_reason;
                                if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                int T2 = starter[0];
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
                        int T0 = tuple1->at(0);
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
                                int T1 = tuple2->at(0);
                                Tuple negativeTuple({T1,T0,T2},&_aux_0);
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
                                            if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                            shared_reason.get()->insert(it*1);
                                        }
                                        if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            shared_reason.get()->insert(it*-1);
                                        }
                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                        if(!itReason.second && itReason.first->second.get()->empty())
                                            itReason.first->second=shared_reason;
                                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_l0 && startVar > 0){
                int T1 = starter[0];
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
                        int T0 = tuple1->at(0);
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
                                int T2 = tuple2->at(0);
                                Tuple negativeTuple({T1,T0,T2},&_aux_0);
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
                                            if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                            shared_reason.get()->insert(it*1);
                                        }
                                        if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            shared_reason.get()->insert(it*-1);
                                        }
                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                        if(!itReason.second && itReason.first->second.get()->empty())
                                            itReason.first->second=shared_reason;
                                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
            if(starter.getPredicateName() == &_l0 && startVar > 0){
                int T0 = starter[0];
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
                                int T2 = tuple2->at(0);
                                Tuple negativeTuple({T1,T0,T2},&_aux_0);
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
                                            if(tupleU->getPredicateName() != &_aux_0 || !tupleUNegated || !(*tupleU == *tuple3))
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
                                            shared_reason.get()->insert(it*1);
                                        }
                                        if(factory.find(*tuple3) != NULL && tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            shared_reason.get()->insert(it*-1);
                                        }
                                        auto itReason = reasonForLiteral.emplace(var,shared_reason);
                                        if(!itReason.second && itReason.first->second.get()->empty())
                                            itReason.first->second=shared_reason;
                                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
                }
                for(auto pair : internalProps)
                    propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
            }
        }
        if(starter.getPredicateName() == &_agg_id_0){
            std::vector<int> sharedVar({});
            const IndexedSet* tuples = &pagg_set_0_.getValuesSet(sharedVar);
            const IndexedSet* tuplesU = &uagg_set_0_.getValuesSet(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=9){
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
                        if(actSum >= 9-currentTuple->at(0)){
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
                if(actSum+posSum < 9){
                    const IndexedSet* tuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                        if(actSum < 9-posSum+currentTuple->at(0)){
                            int itProp = *tuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const IndexedSet* tuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
        if(starter.getPredicateName() == &_agg_set_0){
            const std::vector<int>* tuples = &pagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_0_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_0_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < 9-posSum){
                    int itProp = tuples->at(i);
                    const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                        if(actSum >= 9-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= 9){
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
                        if(actSum < 9-currentJoinTuple->at(0))break;
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= 9){
                    int itProp = tuplesU->at(i);
                    for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < 9 - posSum){
                    int itProp = tuplesU->at(i);
                    const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
        if(starter.getPredicateName() == &_agg_id_1){
            std::vector<int> sharedVar({});
            const IndexedSet* tuples = &pagg_set_0_.getValuesSet(sharedVar);
            const IndexedSet* tuplesU = &uagg_set_0_.getValuesSet(sharedVar);
            std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
            if(startVar < 0){
                int& actSum = actualSum[uStartVar];
                if(actSum>=9+1){
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
                        if(actSum >= 9+1-currentTuple->at(0)){
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
                if(actSum+posSum < 9+1){
                    const IndexedSet* tuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                        if(actSum < 9+1-posSum+currentTuple->at(0)){
                            int itProp = *tuplesU->begin();
                            if(shared_reason.get()->empty()){
                                const IndexedSet* tuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
        if(starter.getPredicateName() == &_agg_set_0){
            const std::vector<int>* tuples = &pagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesU = &uagg_id_1_.getValuesVec({});
            const std::vector<int>* tuplesF = &fagg_id_1_.getValuesVec({});
            for(unsigned i = 0; i<tuples->size(); i++){
                const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuples->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum < 9+1-posSum){
                    int itProp = tuples->at(i);
                    const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                        if(actSum >= 9+1-posSum+currentJoinTuple->at(0)) {break;}
                        int itProp = *joinTuplesU->begin();
                        if(shared_reason.get()->empty()){
                            const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesF->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                if(actSum >= 9+1){
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
                        if(actSum < 9+1-currentJoinTuple->at(0))break;
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
                std::vector<int> sharedVar({});
                const IndexedSet* joinTuples = &pagg_set_0_.getValuesSet(sharedVar);
                const IndexedSet* joinTuplesU = &uagg_set_0_.getValuesSet(sharedVar);
                int aggrIdIt=tuplesU->at(i);
                std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();
                int& actSum = actualSum[aggrIdIt];
                int& posSum = possibleSum[aggrIdIt];
                if(actSum >= 9+1){
                    int itProp = tuplesU->at(i);
                    for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){
                        int it = *j;
                        shared_reason.get()->insert(it);
                    }
                    auto itReason = reasonForLiteral.emplace(itProp,shared_reason);
                    if(!itReason.second && itReason.first->second.get()->empty())
                        itReason.first->second=shared_reason;
                    propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);
                }else if(actSum < 9+1 - posSum){
                    int itProp = tuplesU->at(i);
                    const IndexedSet* joinTuplesF = &fagg_set_0_.getValuesSet(sharedVar);
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
            if(starter.getPredicateName() == &_agg_id_1 && startVar < 0){
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                const Tuple* tuple1 = factory.find({},&_agg_id_0);
                if(tuple1!=NULL){
                    if(tuple1->isFalse())
                    tuple1=NULL;
                    else if(tuple1->isUndef()){
                        if(tupleU == NULL){
                            tupleU = tuple1;
                            tupleUNegated=false;
                        }else{
                            if(tupleU->getPredicateName() != &_agg_id_0 || tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
            if(starter.getPredicateName() == &_agg_id_0 && startVar > 0){
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                std::vector<std::pair<const Tuple*,bool>> internalProps;
                Tuple negativeTuple({},&_agg_id_1);
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
                            if(tupleU->getPredicateName() != &_agg_id_1 || !tupleUNegated || !(*tupleU == *tuple1))
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
                        if(tupleU->getPredicateName() != &_agg_set_0 && tupleU->getPredicateName() != &_aux_0 && tupleU->getPredicateName() != &_agg_id_0 && tupleU->getPredicateName() != &_agg_id_1)
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
