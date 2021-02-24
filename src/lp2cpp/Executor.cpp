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
typedef AuxiliaryMap<Tuple> AuxMap;
typedef std::vector<const Tuple* > Tuples;
using PredicateWSet = PredicateSet<Tuple, TuplesHash>;

std::unordered_map<const std::string*, PredicateWSet*> predicateWSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateFSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateUSetMap;
const std::string _b = "b";
PredicateWSet wb(1);
PredicateWSet ub(1);
const std::string _b_W_ = "b_W_";
PredicateWSet wb_W_(1);
PredicateWSet ub_W_(1);
PredicateWSet nwb_W_(1);
PredicateWSet nub_W_(1);
std::unordered_map < unsigned int, std::set < VarsIndex > > trueAggrVars[1];
std::unordered_map < unsigned int, std::set < VarsIndex > > undefAggrVars[1];
std::unordered_map < unsigned int, std::set < VarsIndex > > trueNegativeAggrVars[1];
std::unordered_map < unsigned int, std::set < VarsIndex > > undefNegativeAggrVars[1];
DynamicTrie aggrVariable[1];
DynamicTrie sharedVariable[1];
std::unordered_map < unsigned int, ReasonTable > positiveAggrReason[1];
std::unordered_map < unsigned int, ReasonTable > negativeAggrReason[1];
std::unordered_map < unsigned int, int > actualSum[1];
std::unordered_map < unsigned int, int > possibleSum[1];
std::unordered_map < unsigned int, int > actualNegativeSum[1];
std::unordered_map < unsigned int, int > possibleNegativeSum[1];
std::unordered_map < unsigned int, int > maxPossibleNegativeSum[1];
int currentReasonLevel=0;
PostponedReasons reasonMapping;
bool first=true;
Executor::~Executor() {
}


const std::vector<const Tuple* > EMPTY_TUPLES;
std::unordered_map<std::string, const std::string * > stringToUniqueStringPointer;
typedef void (*ExplainNegative)(const std::vector<int> & lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output);

std::vector<Tuple> atomsTable;

std::unordered_map<Tuple, unsigned, TuplesHash> tupleToVar;

std::unordered_map<const std::string*, ExplainNegative> explainNegativeFunctionsMap;

Tuple parseTuple(const std::string & literalString) {
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
    std::vector<int> terms;
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
    return Tuple(terms, stringToUniqueStringPointer[predicateName]);
}
//only ground lit function calls are not known a priori
void explainNegativeLiteral(const Tuple * lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output) {
    explainNegativeFunctionsMap[lit->getPredicateName()](*lit, open_set, output);
}

std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToAuxiliaryMaps;
std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToUndefAuxiliaryMaps;
std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToNegativeAuxiliaryMaps;
std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToNegativeUndefAuxiliaryMaps;
std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToFalseAuxiliaryMaps;
AuxMap p_b_W_({});
AuxMap u_b_W_({});
AuxMap np_b_W_({});
AuxMap nu_b_W_({});
AuxMap p_b_W_0_({0});
AuxMap u_b_W_0_({0});
AuxMap np_b_W_0_({0});
AuxMap nu_b_W_0_({0});
AuxMap pb_({});
AuxMap ub_({});
//printing aux maps needed for reasons of negative literals;
void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){
    int v = var==-1?var:-var;
    PostponedReasonData* data = reasonMapping.getAt(v);
    if(data == nullptr || data->getPropagationLevel() == -1) return;
    const std::vector<int>* aggregates_id = &data->getAggregateId();
    for(int i=0; i < aggregates_id->size();i++){
        int aggr_index=aggregates_id->at(i);
        std::vector<int> sharedVars(data->getSharedVariables());
        unsigned int  varsIndex=sharedVariable[aggr_index].addElements(sharedVars)->getId();
        if(data->isPositive(i)){
            positiveAggrReason[aggr_index][varsIndex].getLiteralUntil(data->getPropagationLevel(),reas);
        }else{
            negativeAggrReason[aggr_index][varsIndex].getLiteralUntil(data->getPropagationLevel(),reas);
        }
    }
    const UnorderedSet<int>* body = &data->getBodyReason();
    for(unsigned i=0;i<body->size();i++){
        reas.insert(body->at(i));
    }
    return;
}
//printing functions prototypes for reasons of negative literals;
//printing functions for reasons of negative literals;
void createFunctionsMap() {
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

void explainPositiveLiteral(const Tuple * tuple, std::unordered_set<std::string> & open_set, std::vector<const Tuple*> & outputReasons) {
    std::cout << "explainPositiveLiteral" <<std::endl;
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
inline void Executor::onLiteralTrue(const aspc::Literal* l) {
}
inline void Executor::onLiteralUndef(const aspc::Literal* l) {
}
inline void Executor::onLiteralTrue(int var) {
    unsigned uVar = var > 0 ? var : -var;
    const Tuple & tuple = atomsTable[uVar];
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    first=true;
    std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple.getPredicateName());
    if(uSetIt!=predicateUSetMap.end()) {
        uSetIt->second->erase(tuple);
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple.getPredicateName());
    if (it == predicateWSetMap.end()) {
        } else {
        if (var > 0) {
            const auto& insertResult = it->second->insert(Tuple(tuple));
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
    for(auto& reasonMap:positiveAggrReason){
        for(auto& pair :reasonMap){
            pair.second.addLevel();
        }
    }
    for(auto& reasonMap:negativeAggrReason){
        for(auto& pair :reasonMap){
            pair.second.addLevel();
        }
    }
    currentReasonLevel++;
    propagatedLiterals.erase(-var);
    if(tuple.getPredicateName() == &_b){
        int W = tuple[0];
        if(var > 0){
            Tuple t({W},&_b_W_);
            {
                std::vector<int> aggrKey({t[0]});
                unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(wb_W_.find(t)==NULL){
                        if(ub_W_.find(t))
                            ub_W_.erase(t);
                        const auto& insertResult = wb_W_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_W_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                            possibleSum[0][varsIndex]-=firstVar;
                        }
                        if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                            trueSet.insert(aggrVarsIndex);
                            actualSum[0][varsIndex]+=firstVar;
                            auto& reas = positiveAggrReason[0][varsIndex];
                            while(reas.getCurrentLevel()<currentReasonLevel)
                                reas.addLevel();
                            reas.insert(var);
                        }
                    }
                }else{
                    if(nwb_W_.find(t)==NULL){
                        if(nub_W_.find(t))
                            nub_W_.erase(t);
                        const auto& insertResult = nwb_W_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_W_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({});
                    unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                        undefSet.erase(aggrVarsIndex);
                        auto& reas = negativeAggrReason[0][varsIndex];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                        possibleNegativeSum[0][varsIndex]+=firstVar;
                    }
                }
            }
            {
                std::vector<int> aggrKey({t[0]});
                unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(wb_W_.find(t)==NULL){
                        if(ub_W_.find(t))
                            ub_W_.erase(t);
                        const auto& insertResult = wb_W_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_W_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                            possibleSum[0][varsIndex]-=firstVar;
                        }
                        if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                            trueSet.insert(aggrVarsIndex);
                            actualSum[0][varsIndex]+=firstVar;
                            auto& reas = positiveAggrReason[0][varsIndex];
                            while(reas.getCurrentLevel()<currentReasonLevel)
                                reas.addLevel();
                            reas.insert(var);
                        }
                    }
                }else{
                    if(nwb_W_.find(t)==NULL){
                        if(nub_W_.find(t))
                            nub_W_.erase(t);
                        const auto& insertResult = nwb_W_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_W_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({});
                    unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                        undefSet.erase(aggrVarsIndex);
                        auto& reas = negativeAggrReason[0][varsIndex];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                        possibleNegativeSum[0][varsIndex]+=firstVar;
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_W_0_.getValues({W});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_W_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_b_W_0_.getValues({t[0]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                            possibleSum[0][varsIndex]-=firstVar;
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_b_W_0_.getValues({t[0]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                            possibleSum[0][varsIndex]-=firstVar;
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_b_W_0_.getValues({W});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_W_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_b_W_0_.getValues({t[0]}).size()<=0){
                        if(np_b_W_0_.getValues({t[0]}).size()<=0){
                            if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                                undefSet.erase(aggrVarsIndex);
                                possibleNegativeSum[0][varsIndex]+=firstVar;
                            }
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                trueSet.insert(aggrVarsIndex);
                                actualNegativeSum[0][varsIndex]-=firstVar;
                            }
                        }
                    }
                    auto& reas = positiveAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_b_W_0_.getValues({t[0]}).size()<=0){
                        if(np_b_W_0_.getValues({t[0]}).size()<=0){
                            if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                                undefSet.erase(aggrVarsIndex);
                                possibleNegativeSum[0][varsIndex]+=firstVar;
                            }
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                trueSet.insert(aggrVarsIndex);
                                actualNegativeSum[0][varsIndex]-=firstVar;
                            }
                        }
                    }
                    auto& reas = positiveAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
        }
    }
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    const Tuple & tuple = atomsTable[uVar];
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    reasonMapping.erase(-var);
    reasonMapping.erase(-1);
    while(!propagatedLiterals.empty()){
        reasonMapping.erase(propagatedLiterals[0]);
        propagatedLiterals.erase(propagatedLiterals[0]);
    }
    if(first){
    }
    if (var > 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple.getPredicateName());
        if (wSetIt != predicateWSetMap.end()) {
            wSetIt->second->erase(tuple);
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple.getPredicateName());
    if (it == predicateUSetMap.end()) {
        } else {
        const auto& insertResult = it->second->insert(Tuple(tuple));
        if (insertResult.second) {
            for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[it->first]) {
                auxMap -> insert2(*insertResult.first);
            }
        }
    }
    for(auto& reasonMap:positiveAggrReason){
        for(auto& pair :reasonMap){
            pair.second.eraseCurrentLevel();
        }
    }
    for(auto& reasonMap:negativeAggrReason){
        for(auto& pair :reasonMap){
            pair.second.eraseCurrentLevel();
        }
    }
    if(currentReasonLevel>0)
        currentReasonLevel--;
    if(tuple.getPredicateName() == &_b && tuple.size()==1){
        int W = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_W_0_.getValues({W});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_W_.erase(*tuples.back());
                if(ub_W_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_W_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_W_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_b_W_0_.getValues({t[0]}).size()<=0){
                            if(trueSet.find(aggrVarsIndex)!=trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                                actualSum[0][varsIndex]-=firstVar;
                            }
                        }
                        if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                undefSet.insert(aggrVarsIndex);
                                possibleSum[0][varsIndex]+=firstVar;
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_b_W_0_.getValues({t[0]}).size()<=0){
                            if(trueSet.find(aggrVarsIndex)!=trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                                actualSum[0][varsIndex]-=firstVar;
                            }
                        }
                        if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                undefSet.insert(aggrVarsIndex);
                                possibleSum[0][varsIndex]+=firstVar;
                            }
                        }
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesN = np_b_W_0_.getValues({W});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_W_.erase(*tuplesN.back());
                if(nub_W_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_W_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_W_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_b_W_0_.getValues({t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                            auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                            if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                                if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                    undefSet.insert(aggrVarsIndex);
                                    possibleNegativeSum[0][varsIndex]-=firstVar;
                                }
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_b_W_0_.getValues({t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                            auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                            if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                                if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                    undefSet.insert(aggrVarsIndex);
                                    possibleNegativeSum[0][varsIndex]-=firstVar;
                                }
                            }
                        }
                    }
                }
            }
        }
        Tuple t({W},&_b_W_);
        {
            std::vector<int> aggrKey({t[0]});
            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
            int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
            VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
            if(firstVar>=0){
                if(ub_W_.find(Tuple(t))==NULL){
                    if(wb_W_.find(t))
                        wb_W_.erase(t);
                    const auto& insertResult = ub_W_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_W_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueAggrVars[0][varsIndex];
                auto& undefSet = undefAggrVars[0][varsIndex];
                if(p_b_W_0_.getValues({t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                        actualSum[0][varsIndex]-=firstVar;
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                            possibleSum[0][varsIndex]+=firstVar;
                        }
                    }
                }
            }else{
                if(nub_W_.find(Tuple(t))==NULL){
                    if(nwb_W_.find(t))
                        nwb_W_.erase(t);
                    const auto& insertResult = nub_W_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_W_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                if(np_b_W_0_.getValues({t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                        actualNegativeSum[0][varsIndex]+=firstVar;
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                            possibleNegativeSum[0][varsIndex]-=firstVar;
                            int possSum = possibleNegativeSum[0][varsIndex];
                            if(maxPossibleNegativeSum[0][varsIndex]<possSum)
                                maxPossibleNegativeSum[0][varsIndex]=possSum;
                        }
                    }
                }
            }
        }
        {
            std::vector<int> aggrKey({t[0]});
            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
            int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
            VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
            if(firstVar>=0){
                if(ub_W_.find(Tuple(t))==NULL){
                    if(wb_W_.find(t))
                        wb_W_.erase(t);
                    const auto& insertResult = ub_W_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_W_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueAggrVars[0][varsIndex];
                auto& undefSet = undefAggrVars[0][varsIndex];
                if(p_b_W_0_.getValues({t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                        actualSum[0][varsIndex]-=firstVar;
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                            possibleSum[0][varsIndex]+=firstVar;
                        }
                    }
                }
            }else{
                if(nub_W_.find(Tuple(t))==NULL){
                    if(nwb_W_.find(t))
                        nwb_W_.erase(t);
                    const auto& insertResult = nub_W_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_W_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                if(np_b_W_0_.getValues({t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                        actualNegativeSum[0][varsIndex]+=firstVar;
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                            possibleNegativeSum[0][varsIndex]-=firstVar;
                            int possSum = possibleNegativeSum[0][varsIndex];
                            if(maxPossibleNegativeSum[0][varsIndex]<possSum)
                                maxPossibleNegativeSum[0][varsIndex]=possSum;
                        }
                    }
                }
            }
        }
    }
}
inline void Executor::addedVarName(int var, const std::string & atom) {
    atomsTable.resize(var+1);
    atomsTable.insert(atomsTable.begin()+var, parseTuple(atom));
    tupleToVar[atomsTable[var]]= var;
}
void Executor::clearPropagations() {
    propagatedLiteralsAndReasons.clear();
}
void Executor::clear() {
    failedConstraints.clear();
    predicateToAuxiliaryMaps.clear();
}
void Executor::init() {
    std::cout<<"Init"<<std::endl;
    createFunctionsMap();
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b_W_].push_back(&p_b_W_);
    predicateToAuxiliaryMaps[&_b_W_].push_back(&p_b_W_0_);
    predicateToNegativeAuxiliaryMaps[&_b_W_].push_back(&np_b_W_);
    predicateToNegativeAuxiliaryMaps[&_b_W_].push_back(&np_b_W_0_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b_W_].push_back(&u_b_W_);
    predicateToUndefAuxiliaryMaps[&_b_W_].push_back(&u_b_W_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_W_].push_back(&nu_b_W_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_W_].push_back(&nu_b_W_0_);
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts) {
    int decisionLevel = facts[0];
    clearPropagations();
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
    }
    if(decisionLevel==-1) {
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &pb_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &ub_.getValues({});
            }
            for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){
                const Tuple * tuple0 = NULL;
                if(i<tuples->size()){
                    tuple0 = tuples->at(i);
                    if(tuplesU != &EMPTY_TUPLES) {
                        tupleU = NULL;
                    }
                }
                else {
                    tuple0 = tuplesU->at(i-tuples->size());
                    tupleU = tuple0;
                    tupleUNegated = false;
                }
                int U = (*tuple0)[0];
                const Tuple * tuple1 = NULL;
                if(tupleU && tupleU->getPredicateName() == &_b){
                    const Tuple * undefRepeatingTuple = (ub.find(Tuple({U},&_b)));
                    if(tupleU == undefRepeatingTuple && !tupleUNegated){
                        tuple1 = undefRepeatingTuple;
                    }
                }
                if(!tuple1){
                    tuple1 = (wb.find(Tuple({U},&_b)));
                }
                if(!tuple1 && !tupleU){
                    tupleU = (ub.find(Tuple({U},&_b)));
                    tuple1 = tupleU;
                    tupleUNegated = false;
                }
                if(tuple1){
                    std::vector<int>sharedBodyV({});
                    unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                    if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                        std::vector<int>sharedBodyV({});
                        unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                        int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                        //U
                        if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiterals.insert(-1);
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                                    propagatedLiterals.insert(it->second*sign);
                                }
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            std::vector<int>sharedBodyV({});
                            unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                            if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                                std::vector<int>bodyV({});
                                unsigned int  bodyVarsIndex = sharedVariable[0].addElements(bodyV)->getId();
                                int undefPlusTrue = actualSum[0][bodyVarsIndex]+possibleSum[0][bodyVarsIndex]+actualNegativeSum[0][bodyVarsIndex]+possibleNegativeSum[0][bodyVarsIndex];
                                bool propagated=false;
                                {
                                    std::vector<int>sharedVars({});
                                    unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        if(undefPlusTrue-undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                            if(undefinedTuples->size()==1){

                                                const Tuple* aggrTuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0)},&_b));
                                                if(aggrTuple0!=NULL){
                                                    const auto & it0 = tupleToVar.find(*aggrTuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.insert(it0->second*sign);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        if(undefPlusTrue+undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                            for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                                bool negativeJoinPropagated=false;
                                                const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                    std::vector<int> reas;
                                                    const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                    if(it0 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = 1;
                                                        propagatedLiterals.insert(it0->second*sign);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if(!propagated){
                                }
                            }
                        }
                        {
                            std::vector<int>sharedBodyV({});
                            unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                            int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                            //U
                            if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                bool propagated=false;
                                {
                                    std::vector<int>sharedVars({});
                                    unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]+undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                            for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                                bool found=false;
                                                if(!found){
                                                    const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                    if(aggrTupleU0!=NULL ){
                                                        const auto & it = tupleToVar.find(*aggrTupleU0);
                                                        if(it != tupleToVar.end()) {
                                                            propagated=true;
                                                            int sign = 1;
                                                            found=true;
                                                            propagatedLiterals.insert(it->second*sign);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]-undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                            if(undefinedTuples->size()==1){
                                                {
                                                    Tuple aggrTuple0 ({undefinedTuples->at(0)->at(0)},&_b);
                                                    if(ub.find(aggrTuple0)!=NULL){
                                                        const auto & it = tupleToVar.find(aggrTuple0);
                                                        if(it != tupleToVar.end()) {
                                                            propagated=true;
                                                            int sign = -1;
                                                            propagatedLiterals.insert(it->second*sign);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if(!propagated){
                                }
                            }
                        }
                    }
                }
            }
        }//close local scope
    }//close decision level == -1
    for(unsigned i=1;i<facts.size();i++) {
        unsigned factVar = facts[i] > 0 ? facts[i] : -facts[i];
        Tuple starter = atomsTable[factVar];
        starter.setNegated(facts[i]<0);
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_b){
                {
                    tupleU=NULL;
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pb_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &ub_.getValues({});
                    }
                    for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){
                        const Tuple * tuple1 = NULL;
                        if(i<tuples->size()){
                            tuple1 = tuples->at(i);
                            if(tuplesU != &EMPTY_TUPLES) {
                                tupleU = NULL;
                            }
                        }
                        else {
                            tuple1 = tuplesU->at(i-tuples->size());
                            tupleU = tuple1;
                            tupleUNegated = false;
                        }
                        int U = (*tuple1)[0];
                        const Tuple * tuple2 = NULL;
                        if(tupleU && tupleU->getPredicateName() == &_b){
                            const Tuple * undefRepeatingTuple = (ub.find(Tuple({U},&_b)));
                            if(tupleU == undefRepeatingTuple && !tupleUNegated){
                                tuple2 = undefRepeatingTuple;
                            }
                        }
                        if(!tuple2){
;                            tuple2 = (wb.find(Tuple({U},&_b)));
                        }
                        if(!tuple2 && !tupleU){
;                            tuple2 = tupleU = (ub.find(Tuple({U},&_b)));
                            tupleUNegated = false;
                        }
                        if(tuple2){
                            std::vector<int>sharedBodyV({});
                            unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                            int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                            //U
                            if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                std::vector<int>sharedBodyV({});
                                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                                if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                                    if(tupleU == NULL){
                                        std::cout<<"propagation started from Aggr"<<std::endl;
                                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                        propagatedLiterals.insert(-1);
                                        bool added = reasonMapping.addPropagation(-1);
                                        if(added){
                                            reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                            reasonMapping.addAggrToLit(-1,0,true);
                                            reasonMapping.addAggrToLit(-1,0,false);
                                            const auto & it = tupleToVar.find(Tuple(starter));
                                            if(it!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,it->second * (starter.isNegated() ? -1:1));
                                            }
                                            if(tuple1!=tupleU){
                                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                                if(it!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(-1,it->second);
                                                }
                                            }
                                            if(tuple2!=tupleU){
                                                const auto & it = tupleToVar.find(Tuple(*tuple2));
                                                if(it!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(-1,it->second);
                                                }
                                            }
                                        }
                                    }else{
                                        const auto & it = tupleToVar.find(*tupleU);
                                        if(it != tupleToVar.end()) {
                                            int sign = tupleUNegated ? -1 : 1;
                                            std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                                            propagatedLiterals.insert(it->second*sign);
                                            bool added = reasonMapping.addPropagation(it->second*sign);
                                            if(added){
                                                reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                {
                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                    if(itr!=tupleToVar.end()){
                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                    }
                                                }
                                                if(tuple1!=tupleU){
                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                    if(itr!=tupleToVar.end()){
                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                    }
                                                }
                                                if(tuple2!=tupleU){
                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                    if(itr!=tupleToVar.end()){
                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    bool propagated=false;
                                    {
                                        if(tupleU == NULL){
                                            std::vector<int>sharedVars({});
                                            unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                            for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                                if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]+undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                                    break;
                                                else{
                                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                                        bool found=false;
                                                        if(!found){
                                                            const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                            if(aggrTupleU0!=NULL ){
                                                                std::vector<int> reas;
                                                                const auto & it = tupleToVar.find(*aggrTupleU0);
                                                                if(it != tupleToVar.end()) {
                                                                    propagated=true;
                                                                    int sign = 1;
                                                                    found=true;
                                                                    propagatedLiterals.insert(it->second*sign);
                                                                    bool added = reasonMapping.addPropagation(it->second*sign);
                                                                    if(added){
                                                                        reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                                        reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                                        reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                                        {
                                                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                                                            if(itr!=tupleToVar.end()){
                                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                            }
                                                                        }
                                                                        if(tuple1!=tupleU){
                                                                            const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                            if(itr!=tupleToVar.end()){
                                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                            }
                                                                        }
                                                                        if(tuple2!=tupleU){
                                                                            const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                            if(itr!=tupleToVar.end()){
                                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                            }
                                                                        }
                                                                        for(int v : reas){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                                if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]-undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                                    break;
                                                else{
                                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                                    if(undefinedTuples->size()==1){
                                                        {
                                                            Tuple aggrTuple0 ({undefinedTuples->at(0)->at(0)},&_b);
                                                            if(ub.find(aggrTuple0)!=NULL){
                                                                const auto & it = tupleToVar.find(aggrTuple0);
                                                                if(it != tupleToVar.end()) {
                                                                    propagated=true;
                                                                    int sign = -1;
                                                                    propagatedLiterals.insert(it->second*sign);
                                                                    bool added = reasonMapping.addPropagation(it->second*sign);
                                                                    if(added){
                                                                        reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                                        reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                                        reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                                        {
                                                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                                                            if(itr!=tupleToVar.end()){
                                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                            }
                                                                        }
                                                                        if(tuple1!=tupleU){
                                                                            const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                            if(itr!=tupleToVar.end()){
                                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                            }
                                                                        }
                                                                        if(tuple2!=tupleU){
                                                                            const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                            if(itr!=tupleToVar.end()){
                                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
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
                                    if(tupleU == NULL && !propagated){
                                    }
                                }
                            }
                        }
                    }
                    //nested join closed
                }
            }
        }//local scope
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_b){
                {
                    tupleU=NULL;
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pb_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &ub_.getValues({});
                    }
                    for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){
                        const Tuple * tuple1 = NULL;
                        if(i<tuples->size()){
                            tuple1 = tuples->at(i);
                            if(tuplesU != &EMPTY_TUPLES) {
                                tupleU = NULL;
                            }
                        }
                        else {
                            tuple1 = tuplesU->at(i-tuples->size());
                            tupleU = tuple1;
                            tupleUNegated = false;
                        }
                        int U = (*tuple1)[0];
                        const Tuple * tuple2 = NULL;
                        if(tupleU && tupleU->getPredicateName() == &_b){
                            const Tuple * undefRepeatingTuple = (ub.find(Tuple({U},&_b)));
                            if(tupleU == undefRepeatingTuple && !tupleUNegated){
                                tuple2 = undefRepeatingTuple;
                            }
                        }
                        if(!tuple2){
;                            tuple2 = (wb.find(Tuple({U},&_b)));
                        }
                        if(!tuple2 && !tupleU){
;                            tuple2 = tupleU = (ub.find(Tuple({U},&_b)));
                            tupleUNegated = false;
                        }
                        if(tuple2){
                            std::vector<int>sharedBodyV({});
                            unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                            if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                                std::vector<int>sharedBodyV({});
                                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                                int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                                //U
                                if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                    if(tupleU == NULL){
                                        std::cout<<"propagation started from Aggr"<<std::endl;
                                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                        propagatedLiterals.insert(-1);
                                        bool added = reasonMapping.addPropagation(-1);
                                        if(added){
                                            reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                            reasonMapping.addAggrToLit(-1,0,true);
                                            reasonMapping.addAggrToLit(-1,0,false);
                                            const auto & it = tupleToVar.find(Tuple(starter));
                                            if(it!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,it->second * (starter.isNegated() ? -1:1));
                                            }
                                            if(tuple1!=tupleU){
                                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                                if(it!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(-1,it->second);
                                                }
                                            }
                                            if(tuple2!=tupleU){
                                                const auto & it = tupleToVar.find(Tuple(*tuple2));
                                                if(it!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(-1,it->second);
                                                }
                                            }
                                        }
                                    }else{
                                        const auto & it = tupleToVar.find(*tupleU);
                                        if(it != tupleToVar.end()) {
                                            int sign = tupleUNegated ? -1 : 1;
                                            std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                                            propagatedLiterals.insert(it->second*sign);
                                            bool added = reasonMapping.addPropagation(it->second*sign);
                                            if(added){
                                                reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                {
                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                    if(itr!=tupleToVar.end()){
                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                    }
                                                }
                                                if(tuple1!=tupleU){
                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                    if(itr!=tupleToVar.end()){
                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                    }
                                                }
                                                if(tuple2!=tupleU){
                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                    if(itr!=tupleToVar.end()){
                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    bool propagated=false;
                                    {
                                        if(tupleU == NULL){
                                            std::vector<int>sharedVars({});
                                            unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                            for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                                if(undefPlusTrue-undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                                    break;
                                                else{
                                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                                    if(undefinedTuples->size()==1){

                                                        const Tuple* aggrTuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0)},&_b));
                                                        if(aggrTuple0!=NULL){
                                                            const auto & it0 = tupleToVar.find(*aggrTuple0);
                                                            if(it0 != tupleToVar.end()) {
                                                                propagated=true;
                                                                int sign = -1;
                                                                propagatedLiterals.insert(it0->second*sign);
                                                                bool added = reasonMapping.addPropagation(it0->second*sign);
                                                                if(added){
                                                                    reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                                    reasonMapping.addAggrToLit(it0->second*sign,0,true);
                                                                    reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                                    {
                                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                        }
                                                                    }
                                                                    if(tuple1!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                        }
                                                                    }
                                                                    if(tuple2!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                                if(undefPlusTrue+undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                                    break;
                                                else{
                                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                                        bool negativeJoinPropagated=false;
                                                        const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                        if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                            std::vector<int> reas;
                                                            const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                            if(it0 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                int sign = 1;
                                                                propagatedLiterals.insert(it0->second*sign);
                                                                bool added = reasonMapping.addPropagation(it0->second*sign);
                                                                if(added){
                                                                    reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                                    reasonMapping.addAggrToLit(it0->second*sign,0,true);
                                                                    reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                                    {
                                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                        }
                                                                    }
                                                                    if(tuple1!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                        }
                                                                    }
                                                                    if(tuple2!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                        }
                                                                    }
                                                                    for(int v: reas){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    if(tupleU == NULL && !propagated){
                                    }
                                }
                            }
                        }
                    }
                    //nested join closed
                }
            }
        }//local scope
        if(starter.getPredicateName() == &_b) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int U = (*tuple0)[0];
                    const Tuple * tuple1 = NULL;
                    if(tupleU && tupleU->getPredicateName() == &_b){
                        const Tuple * undefRepeatingTuple = (ub.find(Tuple({U},&_b)));
                        if(tupleU == undefRepeatingTuple && !tupleUNegated){
                            tuple1 = undefRepeatingTuple;
                        }
                    }
                    if(!tuple1){
                        tuple1 = (wb.find(Tuple({U},&_b)));
                    }
                    if(!tuple1 && !tupleU){
                        tupleU = (ub.find(Tuple({U},&_b)));
                        tuple1 = tupleU;
                        tupleUNegated = false;
                    }
                    if(tuple1){
                        std::vector<int>sharedBodyV({});
                        unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                        if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                            std::vector<int>sharedBodyV({});
                            unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                            int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                            //U
                            if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                if(tupleU == NULL){
                                    std::cout<<"propagation started from literal"<<std::endl;
                                    std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                    propagatedLiterals.insert(-1);
                                    bool added = reasonMapping.addPropagation(-1);
                                    if(added){
                                        reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                        reasonMapping.addAggrToLit(-1,0,true);
                                        reasonMapping.addAggrToLit(-1,0,false);
                                        {
                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                            if(itr!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,itr->second * (starter.isNegated() ? -1:1));
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                            if(itr!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,itr->second);
                                            }
                                        }
                                    }
                                }else{
                                    const auto & it = tupleToVar.find(*tupleU);
                                    if(it != tupleToVar.end()) {
                                        int sign = tupleUNegated ? -1 : 1;
                                        std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                                        propagatedLiterals.insert(it->second*sign);
                                        bool added = reasonMapping.addPropagation(it->second*sign);
                                        if(added){
                                            reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                            reasonMapping.addAggrToLit(it->second*sign,0,true);
                                            reasonMapping.addAggrToLit(it->second*sign,0,false);
                                            {
                                                const auto & itr = tupleToVar.find(Tuple(starter));
                                                if(itr!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                }
                                            }
                                            if(tuple1!=tupleU){
                                                const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                if(itr!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                std::vector<int>sharedBodyV({});
                                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                                if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                                    std::vector<int>bodyV({});
                                    unsigned int  bodyVarsIndex = sharedVariable[0].addElements(bodyV)->getId();
                                    int undefPlusTrue = actualSum[0][bodyVarsIndex]+possibleSum[0][bodyVarsIndex]+actualNegativeSum[0][bodyVarsIndex]+possibleNegativeSum[0][bodyVarsIndex];
                                    bool propagated=false;
                                    {
                                        std::vector<int>sharedVars({});
                                        unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                        for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(undefPlusTrue-undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                                if(undefinedTuples->size()==1){

                                                    const Tuple* aggrTuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0)},&_b));
                                                    if(aggrTuple0!=NULL){
                                                        const auto & it0 = tupleToVar.find(*aggrTuple0);
                                                        if(it0 != tupleToVar.end()) {
                                                            propagated=true;
                                                            int sign = -1;
                                                            propagatedLiterals.insert(it0->second*sign);
                                                            bool added = reasonMapping.addPropagation(it0->second*sign);
                                                            if(added){
                                                                reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,true);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                                {
                                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                    }
                                                                }
                                                                if(tuple1!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(undefPlusTrue+undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                                    bool negativeJoinPropagated=false;
                                                    const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                    if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                        std::vector<int> reas;
                                                        const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                        if(it0 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = 1;
                                                            propagatedLiterals.insert(it0->second*sign);
                                                            bool added = reasonMapping.addPropagation(it0->second*sign);
                                                            if(added){
                                                                reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,true);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                                {
                                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                    }
                                                                }
                                                                if(tuple1!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                    }
                                                                }
                                                                for(int v: reas){
                                                                    reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    if(!propagated){
                                    }
                                }
                            }
                            {
                                std::vector<int>sharedBodyV({});
                                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                                int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                                //U
                                if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                    bool propagated=false;
                                    {
                                        std::vector<int>sharedVars({});
                                        unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                        for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]+undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                                    bool found=false;
                                                    if(!found){
                                                        const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                        if(aggrTupleU0!=NULL ){
                                                            std::vector<int> reas;
                                                            const auto & it = tupleToVar.find(*aggrTupleU0);
                                                            if(it != tupleToVar.end()) {
                                                                propagated=true;
                                                                int sign = 1;
                                                                found=true;
                                                                propagatedLiterals.insert(it->second*sign);
                                                                bool added = reasonMapping.addPropagation(it->second*sign);
                                                                if(added){
                                                                    reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                                    {
                                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                        }
                                                                    }
                                                                    if(tuple1!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                        }
                                                                    }
                                                                    for(int v : reas){
                                                                        reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]-undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                                if(undefinedTuples->size()==1){
                                                    {
                                                        Tuple aggrTuple0 ({undefinedTuples->at(0)->at(0)},&_b);
                                                        if(ub.find(aggrTuple0)!=NULL){
                                                            const auto & it = tupleToVar.find(aggrTuple0);
                                                            if(it != tupleToVar.end()) {
                                                                propagated=true;
                                                                int sign = -1;
                                                                propagatedLiterals.insert(it->second*sign);
                                                                bool added = reasonMapping.addPropagation(it->second*sign);
                                                                if(added){
                                                                    reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                                    {
                                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                        }
                                                                    }
                                                                    if(tuple1!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
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
                                    if(!propagated){
                                    }
                                }
                            }
                        }
                    }
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int U = (*tuple0)[0];
                    const Tuple * tuple1 = NULL;
                    if(tupleU && tupleU->getPredicateName() == &_b){
                        const Tuple * undefRepeatingTuple = (ub.find(Tuple({U},&_b)));
                        if(tupleU == undefRepeatingTuple && !tupleUNegated){
                            tuple1 = undefRepeatingTuple;
                        }
                    }
                    if(!tuple1){
                        tuple1 = (wb.find(Tuple({U},&_b)));
                    }
                    if(!tuple1 && !tupleU){
                        tupleU = (ub.find(Tuple({U},&_b)));
                        tuple1 = tupleU;
                        tupleUNegated = false;
                    }
                    if(tuple1){
                        std::vector<int>sharedBodyV({});
                        unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                        if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                            std::vector<int>sharedBodyV({});
                            unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                            int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                            //U
                            if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                if(tupleU == NULL){
                                    std::cout<<"propagation started from literal"<<std::endl;
                                    std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                    propagatedLiterals.insert(-1);
                                    bool added = reasonMapping.addPropagation(-1);
                                    if(added){
                                        reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                        reasonMapping.addAggrToLit(-1,0,true);
                                        reasonMapping.addAggrToLit(-1,0,false);
                                        {
                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                            if(itr!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,itr->second * (starter.isNegated() ? -1:1));
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                            if(itr!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,itr->second);
                                            }
                                        }
                                    }
                                }else{
                                    const auto & it = tupleToVar.find(*tupleU);
                                    if(it != tupleToVar.end()) {
                                        int sign = tupleUNegated ? -1 : 1;
                                        std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                                        propagatedLiterals.insert(it->second*sign);
                                        bool added = reasonMapping.addPropagation(it->second*sign);
                                        if(added){
                                            reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                            reasonMapping.addAggrToLit(it->second*sign,0,true);
                                            reasonMapping.addAggrToLit(it->second*sign,0,false);
                                            {
                                                const auto & itr = tupleToVar.find(Tuple(starter));
                                                if(itr!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                }
                                            }
                                            if(tuple1!=tupleU){
                                                const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                if(itr!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                std::vector<int>sharedBodyV({});
                                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                                if(actualSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]>=U+maxPossibleNegativeSum[0][sharedVarsIndex]){
                                    std::vector<int>bodyV({});
                                    unsigned int  bodyVarsIndex = sharedVariable[0].addElements(bodyV)->getId();
                                    int undefPlusTrue = actualSum[0][bodyVarsIndex]+possibleSum[0][bodyVarsIndex]+actualNegativeSum[0][bodyVarsIndex]+possibleNegativeSum[0][bodyVarsIndex];
                                    bool propagated=false;
                                    {
                                        std::vector<int>sharedVars({});
                                        unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                        for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(undefPlusTrue-undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                                if(undefinedTuples->size()==1){

                                                    const Tuple* aggrTuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0)},&_b));
                                                    if(aggrTuple0!=NULL){
                                                        const auto & it0 = tupleToVar.find(*aggrTuple0);
                                                        if(it0 != tupleToVar.end()) {
                                                            propagated=true;
                                                            int sign = -1;
                                                            propagatedLiterals.insert(it0->second*sign);
                                                            bool added = reasonMapping.addPropagation(it0->second*sign);
                                                            if(added){
                                                                reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,true);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                                {
                                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                    }
                                                                }
                                                                if(tuple1!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(undefPlusTrue+undefKey->at(0)>=U+1+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                                    bool negativeJoinPropagated=false;
                                                    const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                    if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                        std::vector<int> reas;
                                                        const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                        if(it0 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = 1;
                                                            propagatedLiterals.insert(it0->second*sign);
                                                            bool added = reasonMapping.addPropagation(it0->second*sign);
                                                            if(added){
                                                                reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,true);
                                                                reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                                {
                                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                    }
                                                                }
                                                                if(tuple1!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                    }
                                                                }
                                                                for(int v: reas){
                                                                    reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    if(!propagated){
                                    }
                                }
                            }
                            {
                                std::vector<int>sharedBodyV({});
                                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                                int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                                //U
                                if(!(undefPlusTrue>=U+1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                                    bool propagated=false;
                                    {
                                        std::vector<int>sharedVars({});
                                        unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                        for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]+undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &u_b_W_0_.getValues({undefKey->at(0)});
                                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                                    bool found=false;
                                                    if(!found){
                                                        const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                                        if(aggrTupleU0!=NULL ){
                                                            std::vector<int> reas;
                                                            const auto & it = tupleToVar.find(*aggrTupleU0);
                                                            if(it != tupleToVar.end()) {
                                                                propagated=true;
                                                                int sign = 1;
                                                                found=true;
                                                                propagatedLiterals.insert(it->second*sign);
                                                                bool added = reasonMapping.addPropagation(it->second*sign);
                                                                if(added){
                                                                    reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                                    {
                                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                        }
                                                                    }
                                                                    if(tuple1!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                        }
                                                                    }
                                                                    for(int v : reas){
                                                                        reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                            if(actualSum[0][vIndex]+actualNegativeSum[0][vIndex]-undefKey->at(0) < U+maxPossibleNegativeSum[0][vIndex])
                                                break;
                                            else{
                                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_W_0_.getValues({undefKey->at(0)});
                                                if(undefinedTuples->size()==1){
                                                    {
                                                        Tuple aggrTuple0 ({undefinedTuples->at(0)->at(0)},&_b);
                                                        if(ub.find(aggrTuple0)!=NULL){
                                                            const auto & it = tupleToVar.find(aggrTuple0);
                                                            if(it != tupleToVar.end()) {
                                                                propagated=true;
                                                                int sign = -1;
                                                                propagatedLiterals.insert(it->second*sign);
                                                                bool added = reasonMapping.addPropagation(it->second*sign);
                                                                if(added){
                                                                    reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,true);
                                                                    reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                                    {
                                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                        }
                                                                    }
                                                                    if(tuple1!=tupleU){
                                                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                        if(itr!=tupleToVar.end()){
                                                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
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
                                    if(!propagated){
                                    }
                                }
                            }
                        }
                    }
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
    }
}
}
