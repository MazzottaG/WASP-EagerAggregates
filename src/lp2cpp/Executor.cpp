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
const std::string _xvalue = "xvalue";
PredicateWSet wxvalue(2);
PredicateWSet uxvalue(2);
const std::string _yvalue = "yvalue";
PredicateWSet wyvalue(2);
PredicateWSet uyvalue(2);
const std::string _filled = "filled";
PredicateWSet wfilled(2);
PredicateWSet ufilled(2);
const std::string _filled_X_Y_ = "filled_X_Y_";
PredicateWSet wfilled_X_Y_(2);
PredicateWSet ufilled_X_Y_(2);
PredicateWSet nwfilled_X_Y_(2);
PredicateWSet nufilled_X_Y_(2);
std::unordered_map < unsigned int, std::set < VarsIndex > > trueAggrVars[2];
std::unordered_map < unsigned int, std::set < VarsIndex > > undefAggrVars[2];
std::unordered_map < unsigned int, std::set < VarsIndex > > trueNegativeAggrVars[2];
std::unordered_map < unsigned int, std::set < VarsIndex > > undefNegativeAggrVars[2];
DynamicTrie aggrVariable[2];
DynamicTrie sharedVariable[2];
std::unordered_map < unsigned int, ReasonTable > positiveAggrReason[2];
std::unordered_map < unsigned int, ReasonTable > negativeAggrReason[2];
std::unordered_map < unsigned int, int > actualSum[2];
std::unordered_map < unsigned int, int > possibleSum[2];
std::unordered_map < unsigned int, int > actualNegativeSum[2];
std::unordered_map < unsigned int, int > possibleNegativeSum[2];
std::unordered_map < unsigned int, int > maxPossibleNegativeSum[2];
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
AuxMap p_filled_X_Y_1_({1});
AuxMap u_filled_X_Y_1_({1});
AuxMap np_filled_X_Y_1_({1});
AuxMap nu_filled_X_Y_1_({1});
AuxMap p_filled_X_Y_0_({0});
AuxMap u_filled_X_Y_0_({0});
AuxMap np_filled_X_Y_0_({0});
AuxMap nu_filled_X_Y_0_({0});
AuxMap p_filled_X_Y_1_0_({1,0});
AuxMap u_filled_X_Y_1_0_({1,0});
AuxMap np_filled_X_Y_1_0_({1,0});
AuxMap nu_filled_X_Y_1_0_({1,0});
AuxMap p_filled_X_Y_0_1_({0,1});
AuxMap u_filled_X_Y_0_1_({0,1});
AuxMap np_filled_X_Y_0_1_({0,1});
AuxMap nu_filled_X_Y_0_1_({0,1});
AuxMap pxvalue_0_({0});
AuxMap uxvalue_0_({0});
AuxMap pxvalue_({});
AuxMap uxvalue_({});
AuxMap pyvalue_0_({0});
AuxMap uyvalue_0_({0});
AuxMap pyvalue_({});
AuxMap uyvalue_({});
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
    std::cout<<"True "<<minus;tuple.print();std::cout<<std::endl;
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
    if(tuple.getPredicateName() == &_filled){
        int X = tuple[0];
        int Y = tuple[1];
        if(var > 0){
            Tuple t({X,Y},&_filled_X_Y_);
            {
                std::vector<int> aggrKey({t[0]});
                unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(wfilled_X_Y_.find(t)==NULL){
                        if(ufilled_X_Y_.find(t))
                            ufilled_X_Y_.erase(t);
                        const auto& insertResult = wfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        std::vector<int>sharedBodyVars({Y});
                        unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                        if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                            trueSet.insert(aggrVarsIndex);
                            auto& reas = positiveAggrReason[0][varsIndex];
                            while(reas.getCurrentLevel()<currentReasonLevel)
                                reas.addLevel();
                            reas.insert(var);
                        }
                    }
                }else{
                    if(nwfilled_X_Y_.find(t)==NULL){
                        if(nufilled_X_Y_.find(t))
                            nufilled_X_Y_.erase(t);
                        const auto& insertResult = nwfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({Y});
                    unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                        undefSet.erase(aggrVarsIndex);
                    }
                    if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                        trueSet.insert(aggrVarsIndex);
                        auto& reas = positiveAggrReason[0][varsIndex];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                    }
                }
            }
            {
                std::vector<int> aggrKey({t[0]});
                unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(wfilled_X_Y_.find(t)==NULL){
                        if(ufilled_X_Y_.find(t))
                            ufilled_X_Y_.erase(t);
                        const auto& insertResult = wfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        std::vector<int>sharedBodyVars({Y});
                        unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                        if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                            trueSet.insert(aggrVarsIndex);
                            auto& reas = positiveAggrReason[0][varsIndex];
                            while(reas.getCurrentLevel()<currentReasonLevel)
                                reas.addLevel();
                            reas.insert(var);
                        }
                    }
                }else{
                    if(nwfilled_X_Y_.find(t)==NULL){
                        if(nufilled_X_Y_.find(t))
                            nufilled_X_Y_.erase(t);
                        const auto& insertResult = nwfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({Y});
                    unsigned int  varsIndex=sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                        undefSet.erase(aggrVarsIndex);
                    }
                    if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                        trueSet.insert(aggrVarsIndex);
                        auto& reas = positiveAggrReason[0][varsIndex];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                    }
                }
            }
            {
                std::vector<int> aggrKey({t[1]});
                unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(wfilled_X_Y_.find(t)==NULL){
                        if(ufilled_X_Y_.find(t))
                            ufilled_X_Y_.erase(t);
                        const auto& insertResult = wfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        std::vector<int>sharedBodyVars({X});
                        unsigned int  varsIndex=sharedVariable[1].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[1][varsIndex];
                        auto& undefSet = undefAggrVars[1][varsIndex];
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                        if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                            trueSet.insert(aggrVarsIndex);
                            auto& reas = positiveAggrReason[1][varsIndex];
                            while(reas.getCurrentLevel()<currentReasonLevel)
                                reas.addLevel();
                            reas.insert(var);
                        }
                    }
                }else{
                    if(nwfilled_X_Y_.find(t)==NULL){
                        if(nufilled_X_Y_.find(t))
                            nufilled_X_Y_.erase(t);
                        const auto& insertResult = nwfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X});
                    unsigned int  varsIndex=sharedVariable[1].addElements(sharedBodyVars)->getId();
                    auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                    if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                        undefSet.erase(aggrVarsIndex);
                    }
                    if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                        trueSet.insert(aggrVarsIndex);
                        auto& reas = positiveAggrReason[1][varsIndex];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                    }
                }
            }
            {
                std::vector<int> aggrKey({t[1]});
                unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(wfilled_X_Y_.find(t)==NULL){
                        if(ufilled_X_Y_.find(t))
                            ufilled_X_Y_.erase(t);
                        const auto& insertResult = wfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        std::vector<int>sharedBodyVars({X});
                        unsigned int  varsIndex=sharedVariable[1].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[1][varsIndex];
                        auto& undefSet = undefAggrVars[1][varsIndex];
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                        if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                            trueSet.insert(aggrVarsIndex);
                            auto& reas = positiveAggrReason[1][varsIndex];
                            while(reas.getCurrentLevel()<currentReasonLevel)
                                reas.addLevel();
                            reas.insert(var);
                        }
                    }
                }else{
                    if(nwfilled_X_Y_.find(t)==NULL){
                        if(nufilled_X_Y_.find(t))
                            nufilled_X_Y_.erase(t);
                        const auto& insertResult = nwfilled_X_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_filled_X_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X});
                    unsigned int  varsIndex=sharedVariable[1].addElements(sharedBodyVars)->getId();
                    auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                    if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                        undefSet.erase(aggrVarsIndex);
                    }
                    if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                        trueSet.insert(aggrVarsIndex);
                        auto& reas = positiveAggrReason[1][varsIndex];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_filled_X_Y_0_1_.getValues({X,Y});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ufilled_X_Y_.erase(*tuplesU.back());
                {
                    //bound var1
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({Y});
                    unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    //bound var1
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({Y});
                    unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    //bound var0
                    std::vector<int> aggrKey({t[1]});
                    unsigned int aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X});
                    unsigned int varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[1][varsIndex];
                    if(u_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                    }
                    auto& reas = negativeAggrReason[1][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    //bound var0
                    std::vector<int> aggrKey({t[1]});
                    unsigned int aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X});
                    unsigned int varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[1][varsIndex];
                    if(u_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                    }
                    auto& reas = negativeAggrReason[1][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_filled_X_Y_0_1_.getValues({X,Y});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nufilled_X_Y_.erase(*tuplesNU.back());
                {
                    //bound var1
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({Y});
                    unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                        if(np_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                            if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                                undefSet.erase(aggrVarsIndex);
                                possibleNegativeSum[0][varsIndex]+=firstVar;
                            }
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    //bound var1
                    std::vector<int> aggrKey({t[0]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({Y});
                    unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                        if(np_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                            if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                                undefSet.erase(aggrVarsIndex);
                                possibleNegativeSum[0][varsIndex]+=firstVar;
                            }
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    //bound var0
                    std::vector<int> aggrKey({t[1]});
                    unsigned int aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X});
                    unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                    if(nu_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                        if(np_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                            if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                                undefSet.erase(aggrVarsIndex);
                                possibleNegativeSum[1][varsIndex]+=firstVar;
                            }
                        }
                    }
                    auto& reas = negativeAggrReason[1][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
                {
                    //bound var0
                    std::vector<int> aggrKey({t[1]});
                    unsigned int aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X});
                    unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                    if(nu_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                        if(np_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                            if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                                undefSet.erase(aggrVarsIndex);
                                possibleNegativeSum[1][varsIndex]+=firstVar;
                            }
                        }
                    }
                    auto& reas = negativeAggrReason[1][varsIndex];
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
        reasonMapping.erase(*propagatedLiterals.begin());
        propagatedLiterals.erase(*propagatedLiterals.begin());
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
    if(tuple.getPredicateName() == &_filled && tuple.size()==2){
        int X = tuple[0];
        int Y = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_filled_X_Y_0_1_.getValues({X,Y});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wfilled_X_Y_.erase(*tuples.back());
                if(ufilled_X_Y_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({Y});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                            if(trueSet.find(aggrVarsIndex)!=trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                        }
                        if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                undefSet.insert(aggrVarsIndex);
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({Y});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                            if(trueSet.find(aggrVarsIndex)!=trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                        }
                        if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                undefSet.insert(aggrVarsIndex);
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[1].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({X});
                        unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[1][varsIndex];
                        auto& undefSet = undefAggrVars[1][varsIndex];
                        if(p_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                            if(trueSet.find(aggrVarsIndex)!=trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                        }
                        if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                undefSet.insert(aggrVarsIndex);
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[1].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({X});
                        unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[1][varsIndex];
                        auto& undefSet = undefAggrVars[1][varsIndex];
                        if(p_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                            if(trueSet.find(aggrVarsIndex)!=trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                        }
                        if(undefSet.find(aggrVarsIndex)==undefSet.end()){
                            if(trueSet.find(aggrVarsIndex)==trueSet.end()){
                                undefSet.insert(aggrVarsIndex);
                            }
                        }
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesN = np_filled_X_Y_0_1_.getValues({X,Y});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwfilled_X_Y_.erase(*tuplesN.back());
                if(nufilled_X_Y_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({Y});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                            auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                            if(trueSet.find(aggrVarsIndex) != trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                            if(undefSet.find(aggrVarsIndex) == undefSet.end()){
                                if(trueSet.find(aggrVarsIndex) == trueSet.end()){
                                    undefSet.insert(aggrVarsIndex);
                                }
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({Y});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                            auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                            if(trueSet.find(aggrVarsIndex) != trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                            if(undefSet.find(aggrVarsIndex) == undefSet.end()){
                                if(trueSet.find(aggrVarsIndex) == trueSet.end()){
                                    undefSet.insert(aggrVarsIndex);
                                }
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[1].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                            std::vector<int>sharedBodyVars({X});
                            unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                            auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                            auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                            if(trueSet.find(aggrVarsIndex) != trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                            if(undefSet.find(aggrVarsIndex) == undefSet.end()){
                                if(trueSet.find(aggrVarsIndex) == trueSet.end()){
                                    undefSet.insert(aggrVarsIndex);
                                }
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[1].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                            std::vector<int>sharedBodyVars({X});
                            unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                            auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                            auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                            if(trueSet.find(aggrVarsIndex) != trueSet.end()){
                                trueSet.erase(aggrVarsIndex);
                            }
                            if(undefSet.find(aggrVarsIndex) == undefSet.end()){
                                if(trueSet.find(aggrVarsIndex) == trueSet.end()){
                                    undefSet.insert(aggrVarsIndex);
                                }
                            }
                        }
                    }
                }
            }
        }
        Tuple t({X,Y},&_filled_X_Y_);
        {
            std::vector<int> aggrKey({t[0]});
            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
            int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
            VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
            if(firstVar>=0){
                if(ufilled_X_Y_.find(Tuple(t))==NULL){
                    if(wfilled_X_Y_.find(t))
                        wfilled_X_Y_.erase(t);
                    const auto& insertResult = ufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({Y});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueAggrVars[0][varsIndex];
                auto& undefSet = undefAggrVars[0][varsIndex];
                if(p_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                        }
                    }
                }
            }else{
                if(nufilled_X_Y_.find(Tuple(t))==NULL){
                    if(nwfilled_X_Y_.find(t))
                        nwfilled_X_Y_.erase(t);
                    const auto& insertResult = nufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({Y});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                if(np_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
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
                if(ufilled_X_Y_.find(Tuple(t))==NULL){
                    if(wfilled_X_Y_.find(t))
                        wfilled_X_Y_.erase(t);
                    const auto& insertResult = ufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({Y});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueAggrVars[0][varsIndex];
                auto& undefSet = undefAggrVars[0][varsIndex];
                if(p_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                        }
                    }
                }
            }else{
                if(nufilled_X_Y_.find(Tuple(t))==NULL){
                    if(nwfilled_X_Y_.find(t))
                        nwfilled_X_Y_.erase(t);
                    const auto& insertResult = nufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({Y});
                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                if(np_filled_X_Y_1_0_.getValues({Y,t[0]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                        }
                    }
                }
            }
        }
        {
            std::vector<int> aggrKey({t[1]});
            unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
            int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
            VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
            if(firstVar>=0){
                if(ufilled_X_Y_.find(Tuple(t))==NULL){
                    if(wfilled_X_Y_.find(t))
                        wfilled_X_Y_.erase(t);
                    const auto& insertResult = ufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({X});
                unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueAggrVars[1][varsIndex];
                auto& undefSet = undefAggrVars[1][varsIndex];
                if(p_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                        }
                    }
                }
            }else{
                if(nufilled_X_Y_.find(Tuple(t))==NULL){
                    if(nwfilled_X_Y_.find(t))
                        nwfilled_X_Y_.erase(t);
                    const auto& insertResult = nufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({X});
                unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                if(np_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                        }
                    }
                }
            }
        }
        {
            std::vector<int> aggrKey({t[1]});
            unsigned int  aggrKeyIndex = aggrVariable[1].addElements(aggrKey)->getId();
            int firstVar=aggrVariable[1].get(aggrKeyIndex)->at(0);
            VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
            if(firstVar>=0){
                if(ufilled_X_Y_.find(Tuple(t))==NULL){
                    if(wfilled_X_Y_.find(t))
                        wfilled_X_Y_.erase(t);
                    const auto& insertResult = ufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({X});
                unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueAggrVars[1][varsIndex];
                auto& undefSet = undefAggrVars[1][varsIndex];
                if(p_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
                        }
                    }
                }
            }else{
                if(nufilled_X_Y_.find(Tuple(t))==NULL){
                    if(nwfilled_X_Y_.find(t))
                        nwfilled_X_Y_.erase(t);
                    const auto& insertResult = nufilled_X_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
                std::vector<int>sharedBodyVars({X});
                unsigned int  varsIndex = sharedVariable[1].addElements(sharedBodyVars)->getId();
                auto& trueSet = trueNegativeAggrVars[1][varsIndex];
                auto& undefSet = undefNegativeAggrVars[1][varsIndex];
                if(np_filled_X_Y_0_1_.getValues({X,t[1]}).size()<=0){
                    if(trueSet.find(aggVarsIndex)!=trueSet.end()){
                        trueSet.erase(aggVarsIndex);
                    }
                    if(undefSet.find(aggVarsIndex)==undefSet.end()){
                        if(trueSet.find(aggVarsIndex)==trueSet.end()){
                            undefSet.insert(aggVarsIndex);
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
    predicateWSetMap[&_xvalue]=&wxvalue;
    predicateUSetMap[&_xvalue]=&uxvalue;
    stringToUniqueStringPointer["xvalue"] = &_xvalue;
    predicateWSetMap[&_yvalue]=&wyvalue;
    predicateUSetMap[&_yvalue]=&uyvalue;
    stringToUniqueStringPointer["yvalue"] = &_yvalue;
    predicateWSetMap[&_filled]=&wfilled;
    predicateUSetMap[&_filled]=&ufilled;
    stringToUniqueStringPointer["filled"] = &_filled;
    predicateWSetMap[&_filled]=&wfilled;
    predicateUSetMap[&_filled]=&ufilled;
    stringToUniqueStringPointer["filled"] = &_filled;
    predicateWSetMap[&_filled]=&wfilled;
    predicateUSetMap[&_filled]=&ufilled;
    stringToUniqueStringPointer["filled"] = &_filled;
    predicateWSetMap[&_filled]=&wfilled;
    predicateUSetMap[&_filled]=&ufilled;
    stringToUniqueStringPointer["filled"] = &_filled;
    predicateToAuxiliaryMaps[&_yvalue].push_back(&pyvalue_);
    predicateToAuxiliaryMaps[&_yvalue].push_back(&pyvalue_0_);
    predicateToAuxiliaryMaps[&_xvalue].push_back(&pxvalue_);
    predicateToAuxiliaryMaps[&_xvalue].push_back(&pxvalue_0_);
    predicateToAuxiliaryMaps[&_filled_X_Y_].push_back(&p_filled_X_Y_0_);
    predicateToAuxiliaryMaps[&_filled_X_Y_].push_back(&p_filled_X_Y_0_1_);
    predicateToAuxiliaryMaps[&_filled_X_Y_].push_back(&p_filled_X_Y_1_);
    predicateToAuxiliaryMaps[&_filled_X_Y_].push_back(&p_filled_X_Y_1_0_);
    predicateToNegativeAuxiliaryMaps[&_filled_X_Y_].push_back(&np_filled_X_Y_0_);
    predicateToNegativeAuxiliaryMaps[&_filled_X_Y_].push_back(&np_filled_X_Y_0_1_);
    predicateToNegativeAuxiliaryMaps[&_filled_X_Y_].push_back(&np_filled_X_Y_1_);
    predicateToNegativeAuxiliaryMaps[&_filled_X_Y_].push_back(&np_filled_X_Y_1_0_);
    predicateToUndefAuxiliaryMaps[&_yvalue].push_back(&uyvalue_);
    predicateToUndefAuxiliaryMaps[&_yvalue].push_back(&uyvalue_0_);
    predicateToUndefAuxiliaryMaps[&_xvalue].push_back(&uxvalue_);
    predicateToUndefAuxiliaryMaps[&_xvalue].push_back(&uxvalue_0_);
    predicateToUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&u_filled_X_Y_0_);
    predicateToUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&u_filled_X_Y_0_1_);
    predicateToUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&u_filled_X_Y_1_);
    predicateToUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&u_filled_X_Y_1_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&nu_filled_X_Y_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&nu_filled_X_Y_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&nu_filled_X_Y_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_filled_X_Y_].push_back(&nu_filled_X_Y_1_0_);
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
            tuples = &pxvalue_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &uxvalue_.getValues({});
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
                int Y = (*tuple0)[0];
                int V = (*tuple0)[1];
                std::vector<int>sharedBodyV({Y});
                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                //V
                if(!(undefPlusTrue>=V)){
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
                if(tupleU == NULL){
                    {
                        std::vector<int>bodyV({Y});
                        unsigned int  bodyVarsIndex = sharedVariable[0].addElements(bodyV)->getId();
                        int undefPlusTrue = trueAggrVars[0][bodyVarsIndex].size()+undefAggrVars[0][bodyVarsIndex].size()+trueNegativeAggrVars[0][bodyVarsIndex].size()+undefNegativeAggrVars[0][bodyVarsIndex].size();
                        bool propagated=false;
                        if(undefPlusTrue == V){
                            std::vector<int>sharedVars({Y});
                            unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                            for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                if(undefinedTuples->size()==1){

                                    const Tuple* aggrTuple0 = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
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
                            for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                if(undefinedTuples->size()==1){

                                    {
                                        const Tuple* aggrTupleU = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                        if(aggrTupleU!=NULL){
                                            const auto & it = tupleToVar.find(*aggrTupleU);
                                            if(it != tupleToVar.end()) {
                                                int sign = -1;
                                                propagatedLiterals.insert(it->second*sign);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        else{
                        }
                    }
                }
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &pxvalue_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &uxvalue_.getValues({});
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
                int Y = (*tuple0)[0];
                int V = (*tuple0)[1];
                std::vector<int>sharedBodyV({Y});
                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=V+1){
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
                if(tupleU == NULL){
                    {
                        bool propagated=false;
                        std::vector<int>sharedV({Y});
                        unsigned int  sharedIndex = sharedVariable[0].addElements(sharedV)->getId();
                        if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == V){
                            std::vector<int>sharedVars({Y});
                            unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                            for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                    bool found=false;
                                    if(!found){
                                        const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                            for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                    bool negativeJoinPropagated=false;
                                    const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_filled));
                                    if(aggrTupleU0!=NULL && !negativeJoinPropagated){
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
                        else{
                        }
                    }
                }
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &pyvalue_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &uyvalue_.getValues({});
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
                int X = (*tuple0)[0];
                int V = (*tuple0)[1];
                std::vector<int>sharedBodyV({X});
                unsigned int  sharedVarsIndex=sharedVariable[1].addElements(sharedBodyV)->getId();
                int undefPlusTrue = trueAggrVars[1][sharedVarsIndex].size()+undefAggrVars[1][sharedVarsIndex].size()+trueNegativeAggrVars[1][sharedVarsIndex].size()+undefNegativeAggrVars[1][sharedVarsIndex].size();
                //V
                if(!(undefPlusTrue>=V)){
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
                if(tupleU == NULL){
                    {
                        std::vector<int>bodyV({X});
                        unsigned int  bodyVarsIndex = sharedVariable[1].addElements(bodyV)->getId();
                        int undefPlusTrue = trueAggrVars[1][bodyVarsIndex].size()+undefAggrVars[1][bodyVarsIndex].size()+trueNegativeAggrVars[1][bodyVarsIndex].size()+undefNegativeAggrVars[1][bodyVarsIndex].size();
                        bool propagated=false;
                        if(undefPlusTrue == V){
                            std::vector<int>sharedVars({X});
                            unsigned int  vIndex = sharedVariable[1].addElements(sharedVars)->getId();
                            for(auto undefKeyIt = undefAggrVars[1][vIndex].begin();undefKeyIt!=undefAggrVars[1][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                if(undefinedTuples->size()==1){

                                    const Tuple* aggrTuple0 = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
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
                            for(auto undefKeyIt = undefNegativeAggrVars[1][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[1][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                if(undefinedTuples->size()==1){

                                    {
                                        const Tuple* aggrTupleU = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                        if(aggrTupleU!=NULL){
                                            const auto & it = tupleToVar.find(*aggrTupleU);
                                            if(it != tupleToVar.end()) {
                                                int sign = -1;
                                                propagatedLiterals.insert(it->second*sign);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        else{
                        }
                    }
                }
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &pyvalue_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &uyvalue_.getValues({});
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
                int X = (*tuple0)[0];
                int V = (*tuple0)[1];
                std::vector<int>sharedBodyV({X});
                unsigned int  sharedVarsIndex=sharedVariable[1].addElements(sharedBodyV)->getId();
                if((int)(trueAggrVars[1][sharedVarsIndex].size()+trueNegativeAggrVars[1][sharedVarsIndex].size())>=V+1){
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
                if(tupleU == NULL){
                    {
                        bool propagated=false;
                        std::vector<int>sharedV({X});
                        unsigned int  sharedIndex = sharedVariable[1].addElements(sharedV)->getId();
                        if((int)(trueAggrVars[1][sharedIndex].size()+trueNegativeAggrVars[1][sharedIndex].size()) == V){
                            std::vector<int>sharedVars({X});
                            unsigned int  vIndex = sharedVariable[1].addElements(sharedVars)->getId();
                            for(auto undefKeyIt = undefAggrVars[1][vIndex].begin();undefKeyIt!=undefAggrVars[1][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                    bool found=false;
                                    if(!found){
                                        const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                            for(auto undefKeyIt = undefNegativeAggrVars[1][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[1][vIndex].end();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                    bool negativeJoinPropagated=false;
                                    const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_filled));
                                    if(aggrTupleU0!=NULL && !negativeJoinPropagated){
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
                        else{
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
            if(starter.getPredicateName()== &_filled){
                for(auto sharedVarsIt = undefAggrVars[1].begin();sharedVarsIt != undefAggrVars[1].end();sharedVarsIt++){
                    const DynamicCompilationVector* sharedVars=sharedVariable[1].get(sharedVarsIt->first);
                    int X = sharedVars->at(0);
                    tupleU=NULL;
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pyvalue_0_.getValues({X});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &uyvalue_0_.getValues({X});
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
                        int V = (*tuple1)[1];
                        std::vector<int>sharedBodyV({X});
                        unsigned int  sharedVarsIndex=sharedVariable[1].addElements(sharedBodyV)->getId();
                        if((int)(trueAggrVars[1][sharedVarsIndex].size()+trueNegativeAggrVars[1][sharedVarsIndex].size())>=V+1){
                            if(tupleU == NULL){
                                std::cout<<"propagation started from Aggr"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiterals.insert(-1);
                                bool added = reasonMapping.addPropagation(-1);
                                if(added){
                                    reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                    reasonMapping.addAggrToLit(-1,1,true);
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
                                    reasonMapping.addSharedVarToLit(-1,X);
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
                                        reasonMapping.addAggrToLit(it->second*sign,1,true);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                    }
                                }
                            }
                        }else{
                            bool propagated=false;
                            std::vector<int>sharedV({X});
                            unsigned int  sharedIndex = sharedVariable[1].addElements(sharedV)->getId();
                            if((int)(trueAggrVars[1][sharedIndex].size()+trueNegativeAggrVars[1][sharedIndex].size()) == V){
                                if(tupleU == NULL){
                                    std::vector<int>sharedVars({X});
                                    unsigned int  vIndex = sharedVariable[1].addElements(sharedVars)->getId();
                                    for(auto undefKeyIt = undefAggrVars[1][vIndex].begin();undefKeyIt!=undefAggrVars[1][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                            reasonMapping.addAggrToLit(it->second*sign,1,true);
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[1][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[1][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                            bool negativeJoinPropagated=false;
                                            const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                        reasonMapping.addAggrToLit(it0->second*sign,1,true);
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
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                        for(int v : reas){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,v);
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
                    //nested join closed
                }
            }
        }//local scope
        if(starter.getPredicateName() == &_yvalue) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int X = (*tuple0)[0];
                    int V = (*tuple0)[1];
                    std::vector<int>sharedBodyV({X});
                    unsigned int  sharedVarsIndex=sharedVariable[1].addElements(sharedBodyV)->getId();
                    int undefPlusTrue = trueAggrVars[1][sharedVarsIndex].size()+undefAggrVars[1][sharedVarsIndex].size()+trueNegativeAggrVars[1][sharedVarsIndex].size()+undefNegativeAggrVars[1][sharedVarsIndex].size();
                    //V
                    if(!(undefPlusTrue>=V)){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiterals.insert(-1);
                            bool added = reasonMapping.addPropagation(-1);
                            if(added){
                                reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                reasonMapping.addAggrToLit(-1,1,false);
                                {
                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                    if(itr!=tupleToVar.end()){
                                        reasonMapping.addBodyLitToLit(-1,itr->second * (starter.isNegated() ? -1:1));
                                    }
                                }
                                reasonMapping.addSharedVarToLit(-1,X);
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
                                    reasonMapping.addAggrToLit(it->second*sign,1,false);
                                    {
                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(it->second*sign,X);
                                }
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            std::vector<int>bodyV({X});
                            unsigned int  bodyVarsIndex = sharedVariable[1].addElements(bodyV)->getId();
                            int undefPlusTrue = trueAggrVars[1][bodyVarsIndex].size()+undefAggrVars[1][bodyVarsIndex].size()+trueNegativeAggrVars[1][bodyVarsIndex].size()+undefNegativeAggrVars[1][bodyVarsIndex].size();
                            bool propagated=false;
                            if(undefPlusTrue == V){
                                std::vector<int>sharedVars({X});
                                unsigned int  vIndex = sharedVariable[1].addElements(sharedVars)->getId();
                                for(auto undefKeyIt = undefAggrVars[1][vIndex].begin();undefKeyIt!=undefAggrVars[1][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        const Tuple* aggrTuple0 = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                        if(aggrTuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*aggrTuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.insert(it0->second*sign);
                                                bool added = reasonMapping.addPropagation(it0->second*sign);
                                                if(added){
                                                    reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                    reasonMapping.addAggrToLit(it0->second*sign,1,false);
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                        }
                                                    }
                                                    reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKeyIt = undefNegativeAggrVars[1][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[1][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        {
                                            const Tuple* aggrTupleU = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                            if(aggrTupleU!=NULL){
                                                const auto & it = tupleToVar.find(*aggrTupleU);
                                                if(it != tupleToVar.end()) {
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it->second*sign);
                                                    bool added = reasonMapping.addPropagation(it->second*sign);
                                                    if(added){
                                                        reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                        reasonMapping.addAggrToLit(it->second*sign,1,false);
                                                        {
                                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                                            if(itr!=tupleToVar.end()){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                            }
                                                        }
                                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            else{
                            }
                        }
                    }
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int X = (*tuple0)[0];
                    int V = (*tuple0)[1];
                    std::vector<int>sharedBodyV({X});
                    unsigned int  sharedVarsIndex=sharedVariable[1].addElements(sharedBodyV)->getId();
                    if((int)(trueAggrVars[1][sharedVarsIndex].size()+trueNegativeAggrVars[1][sharedVarsIndex].size())>=V+1){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiterals.insert(-1);
                            bool added = reasonMapping.addPropagation(-1);
                            if(added){
                                reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                reasonMapping.addAggrToLit(-1,1,true);
                                {
                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                    if(itr!=tupleToVar.end()){
                                        reasonMapping.addBodyLitToLit(-1,itr->second * (starter.isNegated() ? -1:1));
                                    }
                                }
                                reasonMapping.addSharedVarToLit(-1,X);
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
                                    reasonMapping.addAggrToLit(it->second*sign,1,true);
                                    {
                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(it->second*sign,X);
                                }
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            bool propagated=false;
                            std::vector<int>sharedV({X});
                            unsigned int  sharedIndex = sharedVariable[1].addElements(sharedV)->getId();
                            if((int)(trueAggrVars[1][sharedIndex].size()+trueNegativeAggrVars[1][sharedIndex].size()) == V){
                                std::vector<int>sharedVars({X});
                                unsigned int  vIndex = sharedVariable[1].addElements(sharedVars)->getId();
                                for(auto undefKeyIt = undefAggrVars[1][vIndex].begin();undefKeyIt!=undefAggrVars[1][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                        reasonMapping.addAggrToLit(it->second*sign,1,true);
                                                        {
                                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                                            if(itr!=tupleToVar.end()){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                            }
                                                        }
                                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                        for(int v : reas){
                                                            reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKeyIt = undefNegativeAggrVars[1][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[1][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                    reasonMapping.addAggrToLit(it0->second*sign,1,true);
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                        }
                                                    }
                                                    reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                    for(int v : reas){
                                                        reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            else{
                            }
                        }
                    }
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_filled){
                for(auto sharedVarsIt = undefAggrVars[1].begin();sharedVarsIt != undefAggrVars[1].end();sharedVarsIt++){
                    const DynamicCompilationVector* sharedVars=sharedVariable[1].get(sharedVarsIt->first);
                    int X = sharedVars->at(0);
                    tupleU=NULL;
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pyvalue_0_.getValues({X});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &uyvalue_0_.getValues({X});
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
                        int V = (*tuple1)[1];
                        std::vector<int>sharedBodyV({X});
                        unsigned int  sharedVarsIndex=sharedVariable[1].addElements(sharedBodyV)->getId();
                        int undefPlusTrue = trueAggrVars[1][sharedVarsIndex].size()+undefAggrVars[1][sharedVarsIndex].size()+trueNegativeAggrVars[1][sharedVarsIndex].size()+undefNegativeAggrVars[1][sharedVarsIndex].size();
                        //V
                        if(!(undefPlusTrue>=V)){
                            if(tupleU == NULL){
                                std::cout<<"propagation started from Aggr"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiterals.insert(-1);
                                bool added = reasonMapping.addPropagation(-1);
                                if(added){
                                    reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                    reasonMapping.addAggrToLit(-1,1,false);
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
                                    reasonMapping.addSharedVarToLit(-1,X);
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
                                        reasonMapping.addAggrToLit(it->second*sign,1,false);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                    }
                                }
                            }
                        }else{
                            bool propagated=false;
                            if(undefPlusTrue == V){
                                if(tupleU == NULL){
                                    std::vector<int>sharedVars({X});
                                    unsigned int  vIndex = sharedVariable[1].addElements(sharedVars)->getId();
                                    for(auto undefKeyIt = undefAggrVars[1][vIndex].begin();undefKeyIt!=undefAggrVars[1][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* aggrTuple0 = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                            if(aggrTuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*aggrTuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it0->second*sign);
                                                    bool added = reasonMapping.addPropagation(it0->second*sign);
                                                    if(added){
                                                        reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                        reasonMapping.addAggrToLit(it0->second*sign,1,false);
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
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[1][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[1][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[1].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_0_1_.getValues({X,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            {
                                                const Tuple* aggrTupleU = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                                if(aggrTupleU!=NULL){
                                                    const auto & it = tupleToVar.find(*aggrTupleU);
                                                    if(it != tupleToVar.end()) {
                                                        int sign = -1;
                                                        propagatedLiterals.insert(it->second*sign);
                                                        bool added = reasonMapping.addPropagation(it->second*sign);
                                                        if(added){
                                                            reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                            reasonMapping.addAggrToLit(it->second*sign,1,false);
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                    //nested join closed
                }
            }
        }//local scope
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_filled){
                for(auto sharedVarsIt = undefAggrVars[0].begin();sharedVarsIt != undefAggrVars[0].end();sharedVarsIt++){
                    const DynamicCompilationVector* sharedVars=sharedVariable[0].get(sharedVarsIt->first);
                    int Y = sharedVars->at(0);
                    tupleU=NULL;
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pxvalue_0_.getValues({Y});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &uxvalue_0_.getValues({Y});
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
                        int V = (*tuple1)[1];
                        std::vector<int>sharedBodyV({Y});
                        unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                        if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=V+1){
                            if(tupleU == NULL){
                                std::cout<<"propagation started from Aggr"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiterals.insert(-1);
                                bool added = reasonMapping.addPropagation(-1);
                                if(added){
                                    reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                    reasonMapping.addAggrToLit(-1,0,true);
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
                                    reasonMapping.addSharedVarToLit(-1,Y);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                    }
                                }
                            }
                        }else{
                            bool propagated=false;
                            std::vector<int>sharedV({Y});
                            unsigned int  sharedIndex = sharedVariable[0].addElements(sharedV)->getId();
                            if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == V){
                                if(tupleU == NULL){
                                    std::vector<int>sharedVars({Y});
                                    unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                            bool negativeJoinPropagated=false;
                                            const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,Y);
                                                        for(int v : reas){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,v);
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
                    //nested join closed
                }
            }
        }//local scope
        if(starter.getPredicateName() == &_xvalue) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int Y = (*tuple0)[0];
                    int V = (*tuple0)[1];
                    std::vector<int>sharedBodyV({Y});
                    unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                    int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                    //V
                    if(!(undefPlusTrue>=V)){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiterals.insert(-1);
                            bool added = reasonMapping.addPropagation(-1);
                            if(added){
                                reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                reasonMapping.addAggrToLit(-1,0,false);
                                {
                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                    if(itr!=tupleToVar.end()){
                                        reasonMapping.addBodyLitToLit(-1,itr->second * (starter.isNegated() ? -1:1));
                                    }
                                }
                                reasonMapping.addSharedVarToLit(-1,Y);
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
                                    reasonMapping.addAggrToLit(it->second*sign,0,false);
                                    {
                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                }
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            std::vector<int>bodyV({Y});
                            unsigned int  bodyVarsIndex = sharedVariable[0].addElements(bodyV)->getId();
                            int undefPlusTrue = trueAggrVars[0][bodyVarsIndex].size()+undefAggrVars[0][bodyVarsIndex].size()+trueNegativeAggrVars[0][bodyVarsIndex].size()+undefNegativeAggrVars[0][bodyVarsIndex].size();
                            bool propagated=false;
                            if(undefPlusTrue == V){
                                std::vector<int>sharedVars({Y});
                                unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        const Tuple* aggrTuple0 = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                        if(aggrTuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*aggrTuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.insert(it0->second*sign);
                                                bool added = reasonMapping.addPropagation(it0->second*sign);
                                                if(added){
                                                    reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
                                                    reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                        }
                                                    }
                                                    reasonMapping.addSharedVarToLit(it0->second*sign,Y);
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        {
                                            const Tuple* aggrTupleU = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                            if(aggrTupleU!=NULL){
                                                const auto & it = tupleToVar.find(*aggrTupleU);
                                                if(it != tupleToVar.end()) {
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it->second*sign);
                                                    bool added = reasonMapping.addPropagation(it->second*sign);
                                                    if(added){
                                                        reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
                                                        reasonMapping.addAggrToLit(it->second*sign,0,false);
                                                        {
                                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                                            if(itr!=tupleToVar.end()){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                            }
                                                        }
                                                        reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            else{
                            }
                        }
                    }
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int Y = (*tuple0)[0];
                    int V = (*tuple0)[1];
                    std::vector<int>sharedBodyV({Y});
                    unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                    if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=V+1){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiterals.insert(-1);
                            bool added = reasonMapping.addPropagation(-1);
                            if(added){
                                reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
                                reasonMapping.addAggrToLit(-1,0,true);
                                {
                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                    if(itr!=tupleToVar.end()){
                                        reasonMapping.addBodyLitToLit(-1,itr->second * (starter.isNegated() ? -1:1));
                                    }
                                }
                                reasonMapping.addSharedVarToLit(-1,Y);
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
                                    {
                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                }
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            bool propagated=false;
                            std::vector<int>sharedV({Y});
                            unsigned int  sharedIndex = sharedVariable[0].addElements(sharedV)->getId();
                            if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == V){
                                std::vector<int>sharedVars({Y});
                                unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                        {
                                                            const auto & itr = tupleToVar.find(Tuple(starter));
                                                            if(itr!=tupleToVar.end()){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                            }
                                                        }
                                                        reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                                        for(int v : reas){
                                                            reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                    const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* aggrTupleU0 = ufilled.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_filled));
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
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                        }
                                                    }
                                                    reasonMapping.addSharedVarToLit(it0->second*sign,Y);
                                                    for(int v : reas){
                                                        reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            else{
                            }
                        }
                    }
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_filled){
                for(auto sharedVarsIt = undefAggrVars[0].begin();sharedVarsIt != undefAggrVars[0].end();sharedVarsIt++){
                    const DynamicCompilationVector* sharedVars=sharedVariable[0].get(sharedVarsIt->first);
                    int Y = sharedVars->at(0);
                    tupleU=NULL;
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pxvalue_0_.getValues({Y});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &uxvalue_0_.getValues({Y});
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
                        int V = (*tuple1)[1];
                        std::vector<int>sharedBodyV({Y});
                        unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                        int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                        //V
                        if(!(undefPlusTrue>=V)){
                            if(tupleU == NULL){
                                std::cout<<"propagation started from Aggr"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiterals.insert(-1);
                                bool added = reasonMapping.addPropagation(-1);
                                if(added){
                                    reasonMapping.setPropLevelToLit(-1,currentReasonLevel);
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
                                    reasonMapping.addSharedVarToLit(-1,Y);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,Y);
                                    }
                                }
                            }
                        }else{
                            bool propagated=false;
                            if(undefPlusTrue == V){
                                if(tupleU == NULL){
                                    std::vector<int>sharedVars({Y});
                                    unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &u_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* aggrTuple0 = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                            if(aggrTuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*aggrTuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it0->second*sign);
                                                    bool added = reasonMapping.addPropagation(it0->second*sign);
                                                    if(added){
                                                        reasonMapping.setPropLevelToLit(it0->second*sign,currentReasonLevel);
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
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,Y);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                        const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_filled_X_Y_1_0_.getValues({Y,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            {
                                                const Tuple* aggrTupleU = ufilled.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_filled));
                                                if(aggrTupleU!=NULL){
                                                    const auto & it = tupleToVar.find(*aggrTupleU);
                                                    if(it != tupleToVar.end()) {
                                                        int sign = -1;
                                                        propagatedLiterals.insert(it->second*sign);
                                                        bool added = reasonMapping.addPropagation(it->second*sign);
                                                        if(added){
                                                            reasonMapping.setPropLevelToLit(it->second*sign,currentReasonLevel);
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,Y);
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
                    //nested join closed
                }
            }
        }//local scope
    }
}
}
