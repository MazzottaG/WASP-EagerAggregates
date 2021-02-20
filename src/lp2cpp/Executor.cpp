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
const std::string _a = "a";
PredicateWSet wa(3);
PredicateWSet ua(3);
const std::string _b = "b";
PredicateWSet wb(1);
PredicateWSet ub(1);
const std::string _b_U_a_V_X_Y_not_a_U_V_V_ = "b_U_a_V_X_Y_not_a_U_V_V_";
PredicateWSet wb_U_a_V_X_Y_not_a_U_V_V_(7);
PredicateWSet ub_U_a_V_X_Y_not_a_U_V_V_(7);
PredicateWSet nwb_U_a_V_X_Y_not_a_U_V_V_(7);
PredicateWSet nub_U_a_V_X_Y_not_a_U_V_V_(7);
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
AuxMap pa_({});
AuxMap ua_({});
AuxMap pa_0_1_2_({0,1,2});
AuxMap ua_0_1_2_({0,1,2});
AuxMap pb_({});
AuxMap ub_({});
AuxMap pb_0_({0});
AuxMap ub_0_({0});
AuxMap pa_0_({0});
AuxMap ua_0_({0});
AuxMap p_b_U_a_V_X_Y_not_a_U_V_V_({});
AuxMap u_b_U_a_V_X_Y_not_a_U_V_V_({});
AuxMap np_b_U_a_V_X_Y_not_a_U_V_V_({});
AuxMap nu_b_U_a_V_X_Y_not_a_U_V_V_({});
AuxMap p_b_U_a_V_X_Y_not_a_U_V_V_0_2_({0,2});
AuxMap u_b_U_a_V_X_Y_not_a_U_V_V_0_2_({0,2});
AuxMap np_b_U_a_V_X_Y_not_a_U_V_V_0_2_({0,2});
AuxMap nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_({0,2});
AuxMap p_b_U_a_V_X_Y_not_a_U_V_V_0_({0});
AuxMap u_b_U_a_V_X_Y_not_a_U_V_V_0_({0});
AuxMap np_b_U_a_V_X_Y_not_a_U_V_V_0_({0});
AuxMap nu_b_U_a_V_X_Y_not_a_U_V_V_0_({0});
AuxMap p_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_({1,2,3});
AuxMap u_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_({1,2,3});
AuxMap np_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_({1,2,3});
AuxMap nu_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_({1,2,3});
AuxMap p_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_({4,5,6});
AuxMap u_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_({4,5,6});
AuxMap np_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_({4,5,6});
AuxMap nu_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_({4,5,6});
//printing aux maps needed for reasons of negative literals;
void Executor::explainAggrLiteral(int var,std::unordered_set<int>& reas){
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
    const std::unordered_set<int>* body = &data->getBodyReason();
    for(auto it=body->begin();it != body->end();it++){
        reas.insert(*it);
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
        int U = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
            for(int i_1=0;i_1<tuples1->size();i_1++){
                const Tuple* tuple1=tuples1->at(i_1);
                int V = tuple1->at(0);
                int X = tuple1->at(1);
                int Y = tuple1->at(2);
                const Tuple negativeTuple2({U,V,V},&_a,true);
                const Tuple* tuple2 = ua.find(Tuple({U,V,V},&_a));
                if(wa.find(negativeTuple2)==NULL && tuple2==NULL){
                    tuple2=&negativeTuple2;
                    if((*tuple2)[0]!=(*tuple1)[0] || (*tuple2)[1]!=(*tuple1)[1] || (*tuple2)[2]!=(*tuple1)[2]){
                        Tuple t({U,V,X,Y,U,V,V},&_b_U_a_V_X_Y_not_a_U_V_V_);
                        {
                            std::vector<int> aggrKey({t[0],t[2]});
                            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                            int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                            VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                            if(firstVar>=0){
                                if(wb_U_a_V_X_Y_not_a_U_V_V_.find(t)==NULL){
                                    if(ub_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                        ub_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                    const auto& insertResult = wb_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple2);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                            }else{
                                if(nwb_U_a_V_X_Y_not_a_U_V_V_.find(t)==NULL){
                                    if(nub_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                        nub_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                    const auto& insertResult = nwb_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
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
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            reas.insert(it->second);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple2);
                                        if(it != tupleToVar.end()) {
                                            reas.insert(it->second*-1);
                                        }
                                    }
                                    possibleNegativeSum[0][varsIndex]+=firstVar;
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_U_a_V_X_Y_not_a_U_V_V_0_.getValues({U});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[0],t[2]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_U_a_V_X_Y_not_a_U_V_V_0_.getValues({U});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[0],t[2]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
                        if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
    if(tuple.getPredicateName() == &_a){
        int V = tuple[0];
        int X = tuple[1];
        int Y = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pb_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int U = tuple0->at(0);
                const Tuple negativeTuple2({U,V,V},&_a,true);
                const Tuple* tuple2 = ua.find(Tuple({U,V,V},&_a));
                if(wa.find(negativeTuple2)==NULL && tuple2==NULL){
                    tuple2=&negativeTuple2;
                    if((*tuple2)[0]!=tuple[0] || (*tuple2)[1]!=tuple[1] || (*tuple2)[2]!=tuple[2]){
                        Tuple t({U,V,X,Y,U,V,V},&_b_U_a_V_X_Y_not_a_U_V_V_);
                        {
                            std::vector<int> aggrKey({t[0],t[2]});
                            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                            int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                            VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                            if(firstVar>=0){
                                if(wb_U_a_V_X_Y_not_a_U_V_V_.find(t)==NULL){
                                    if(ub_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                        ub_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                    const auto& insertResult = wb_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple0);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple2);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                            }else{
                                if(nwb_U_a_V_X_Y_not_a_U_V_V_.find(t)==NULL){
                                    if(nub_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                        nub_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                    const auto& insertResult = nwb_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
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
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            reas.insert(it->second);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple2);
                                        if(it != tupleToVar.end()) {
                                            reas.insert(it->second*-1);
                                        }
                                    }
                                    possibleNegativeSum[0][varsIndex]+=firstVar;
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_.getValues({V,X,Y});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[0],t[2]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_.getValues({V,X,Y});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[0],t[2]});
                    unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                    int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({});
                    unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
                        if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
    if(tuple.getPredicateName() == &_a){
        if(tuple.at(1) == tuple.at(2)){
            int U = tuple[0];
            int V = tuple[1];
            if(var < 0){
                const Tuple* tuple0 = wb.find(Tuple({U},&_b));
                if(tuple0!=NULL){
                    const std::vector<const Tuple*>* tuples1 = &pa_0_.getValues({V});
                    for(int i_1=0;i_1<tuples1->size();i_1++){
                        const Tuple* tuple1=tuples1->at(i_1);
                        if((*tuple1)[0]!=tuple[0] || (*tuple1)[1]!=tuple[1] || (*tuple1)[2]!=tuple[2]){
                            int X = tuple1->at(1);
                            int Y = tuple1->at(2);
                            Tuple t({U,V,X,Y,U,V,V},&_b_U_a_V_X_Y_not_a_U_V_V_);
                            {
                                std::vector<int> aggrKey({t[0],t[2]});
                                unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                                int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                                VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                                if(firstVar>=0){
                                    if(wb_U_a_V_X_Y_not_a_U_V_V_.find(t)==NULL){
                                        if(ub_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                            ub_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                        const auto& insertResult = wb_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple0);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second);
                                                }
                                            }
                                            {
                                                const auto & it = tupleToVar.find(*tuple1);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_U_a_V_X_Y_not_a_U_V_V_.find(t)==NULL){
                                        if(nub_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                            nub_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                        const auto& insertResult = nwb_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple0);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second);
                                            }
                                        }
                                        possibleNegativeSum[0][varsIndex]+=firstVar;
                                    }
                                }
                            }
                        }
                    }
                }
            }else{
                const std::vector<const Tuple*>& tuplesU = u_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_.getValues({U,V,V});
                while(!tuplesU.empty()){
                    Tuple t(*tuplesU.back());
                    ub_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesU.back());
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({});
                        unsigned int varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(u_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
                const std::vector<const Tuple*>& tuplesNU = nu_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_.getValues({U,V,V});
                while(!tuplesNU.empty()){
                    Tuple t(*tuplesNU.back());
                    nub_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesNU.back());
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                        auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                        if(nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
                            if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
    if(tuple.getPredicateName() == &_b && tuple.size()==1){
        int U = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_U_a_V_X_Y_not_a_U_V_V_0_.getValues({U});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_U_a_V_X_Y_not_a_U_V_V_.erase(*tuples.back());
                if(ub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_U_a_V_X_Y_not_a_U_V_V_0_.getValues({U});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesN.back());
                if(nub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
        const std::vector<const Tuple*>& tuples1 = pa_.getValues({});
        const std::vector<const Tuple*>& tuplesU1 = ua_.getValues({});
        for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
            const Tuple* tuple1;
            bool undef1=false;
            if(i_1<tuples1.size())                tuple1=tuples1[i_1];
            else{
                tuple1=tuplesU1[i_1-tuples1.size()];
                undef1=true;
            }
            int V = tuple1->at(0);
            int X = tuple1->at(1);
            int Y = tuple1->at(2);
            const Tuple negativeTuple2({U,V,V},&_a,true);
            const Tuple* tuple2 = ua.find(Tuple({U,V,V},&_a));
            bool undef2 = false;
            if(tuple2!=NULL){
                undef2 = true;
            }else if(wa.find(negativeTuple2)==NULL){
                tuple2=&negativeTuple2;
            }
            if(tuple2!=NULL){
                if((*tuple2)[0]!=(*tuple1)[0] || (*tuple2)[1]!=(*tuple1)[1] || (*tuple2)[2]!=(*tuple1)[2]){
                    Tuple t({U,V,X,Y,U,V,V},&_b_U_a_V_X_Y_not_a_U_V_V_);
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                        if(firstVar>=0){
                            if(ub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t))==NULL){
                                if(wb_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                    wb_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                const auto& insertResult = ub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& trueSet = trueAggrVars[0][varsIndex];
                            auto& undefSet = undefAggrVars[0][varsIndex];
                            if(p_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
                            if(nub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t))==NULL){
                                if(nwb_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                    nwb_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                const auto& insertResult = nub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                            auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                            if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
        }
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==3){
        int V = tuple[0];
        int X = tuple[1];
        int Y = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_.getValues({V,X,Y});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_U_a_V_X_Y_not_a_U_V_V_.erase(*tuples.back());
                if(ub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({});
                        unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_.getValues({V,X,Y});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesN.back());
                if(nub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
        const std::vector<const Tuple*>& tuples0 = pb_.getValues({});
        const std::vector<const Tuple*>& tuplesU0 = ub_.getValues({});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int U = tuple0->at(0);
            const Tuple negativeTuple2({U,V,V},&_a,true);
            const Tuple* tuple2 = ua.find(Tuple({U,V,V},&_a));
            bool undef2 = false;
            if(tuple2!=NULL){
                undef2 = true;
            }else if(wa.find(negativeTuple2)==NULL){
                tuple2=&negativeTuple2;
            }
            if(tuple2!=NULL){
                if((*tuple2)[0]!=tuple[0] || (*tuple2)[1]!=tuple[1] || (*tuple2)[2]!=tuple[2]){
                    Tuple t({U,V,X,Y,U,V,V},&_b_U_a_V_X_Y_not_a_U_V_V_);
                    {
                        std::vector<int> aggrKey({t[0],t[2]});
                        unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                        int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                        VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                        if(firstVar>=0){
                            if(ub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t))==NULL){
                                if(wb_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                    wb_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                const auto& insertResult = ub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& trueSet = trueAggrVars[0][varsIndex];
                            auto& undefSet = undefAggrVars[0][varsIndex];
                            if(p_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
                            if(nub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t))==NULL){
                                if(nwb_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                    nwb_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                const auto& insertResult = nub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                            auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                            if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
        }
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==3){
        if(tuple.at(1) == tuple.at(2)){
            int U = tuple[0];
            int V = tuple[1];
            if(var < 0){
                const std::vector<const Tuple*>& tuples = p_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_.getValues({U,V,V});
                while(!tuples.empty()){
                    Tuple t(*tuples.back());
                    wb_U_a_V_X_Y_not_a_U_V_V_.erase(*tuples.back());
                    if(ub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t)) == NULL){
                        const auto& insertResult = ub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[0],t[2]});
                            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                            int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                            VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                            std::vector<int>sharedBodyVars({});
                            unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                            auto& trueSet = trueAggrVars[0][varsIndex];
                            auto& undefSet = undefAggrVars[0][varsIndex];
                            if(p_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
                const std::vector<const Tuple*>& tuplesN = np_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_.getValues({U,V,V});
                while(!tuplesN.empty()){
                    Tuple t(*tuplesN.back());
                    nwb_U_a_V_X_Y_not_a_U_V_V_.erase(*tuplesN.back());
                    if(nub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t)) == NULL){
                        const auto& insertResult = nub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[0],t[2]});
                            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                            int firstVar = aggrVariable[0].get(aggrKeyIndex)->at(0);
                            VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                            if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
            const Tuple* tuple0 = wb.find(Tuple({U},&_b));
            bool undef0 = false;
            if(tuple0==NULL){
                tuple0 = ub.find(Tuple({U},&_b));
                undef0 = true;
            }
            if(tuple0!=NULL){
                const std::vector<const Tuple*>& tuples1 = pa_0_.getValues({V});
                const std::vector<const Tuple*>& tuplesU1 = ua_0_.getValues({V});
                for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
                    const Tuple* tuple1;
                    bool undef1=false;
                    if(i_1<tuples1.size())                        tuple1=tuples1[i_1];
                    else{
                        tuple1=tuplesU1[i_1-tuples1.size()];
                        undef1=true;
                    }
                    if((*tuple1)[0]!=tuple[0] || (*tuple1)[1]!=tuple[1] || (*tuple1)[2]!=tuple[2]){
                        int X = tuple1->at(1);
                        int Y = tuple1->at(2);
                        Tuple t({U,V,X,Y,U,V,V},&_b_U_a_V_X_Y_not_a_U_V_V_);
                        {
                            std::vector<int> aggrKey({t[0],t[2]});
                            unsigned int  aggrKeyIndex = aggrVariable[0].addElements(aggrKey)->getId();
                            int firstVar=aggrVariable[0].get(aggrKeyIndex)->at(0);
                            VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                            if(firstVar>=0){
                                if(ub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t))==NULL){
                                    if(wb_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                        wb_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                    const auto& insertResult = ub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                std::vector<int>sharedBodyVars({});
                                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                                auto& trueSet = trueAggrVars[0][varsIndex];
                                auto& undefSet = undefAggrVars[0][varsIndex];
                                if(p_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
                                if(nub_U_a_V_X_Y_not_a_U_V_V_.find(Tuple(t))==NULL){
                                    if(nwb_U_a_V_X_Y_not_a_U_V_V_.find(t))
                                        nwb_U_a_V_X_Y_not_a_U_V_V_.erase(t);
                                    const auto& insertResult = nub_U_a_V_X_Y_not_a_U_V_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                std::vector<int>sharedBodyVars({});
                                unsigned int  varsIndex = sharedVariable[0].addElements(sharedBodyVars)->getId();
                                auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                                auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                                if(np_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({t[0],t[2]}).size()<=0){
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
    predicateWSetMap[&_a]=&wa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_a]=&wa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&p_b_U_a_V_X_Y_not_a_U_V_V_);
    predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&p_b_U_a_V_X_Y_not_a_U_V_V_0_);
    predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&p_b_U_a_V_X_Y_not_a_U_V_V_0_2_);
    predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&p_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_);
    predicateToAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&p_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_1_2_);
    predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&np_b_U_a_V_X_Y_not_a_U_V_V_);
    predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&np_b_U_a_V_X_Y_not_a_U_V_V_0_);
    predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&np_b_U_a_V_X_Y_not_a_U_V_V_0_2_);
    predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&np_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_);
    predicateToNegativeAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&np_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_);
    predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&u_b_U_a_V_X_Y_not_a_U_V_V_);
    predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&u_b_U_a_V_X_Y_not_a_U_V_V_0_);
    predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&u_b_U_a_V_X_Y_not_a_U_V_V_0_2_);
    predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&u_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&u_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_1_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&nu_b_U_a_V_X_Y_not_a_U_V_V_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&nu_b_U_a_V_X_Y_not_a_U_V_V_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&nu_b_U_a_V_X_Y_not_a_U_V_V_1_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_U_a_V_X_Y_not_a_U_V_V_].push_back(&nu_b_U_a_V_X_Y_not_a_U_V_V_4_5_6_);
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
            {
                std::vector<int>sharedBodyV({});
                unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                //1
                if(!(undefPlusTrue>=1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::cout<<"propagation started from Aggr"<<std::endl;
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
                }//close aggr true if
                else{
                    bool propagated=false;
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::vector<int>sharedVars({});
                        unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                        for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                            if(undefPlusTrue-undefKey->at(0)>=1+maxPossibleNegativeSum[0][vIndex])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &u_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({undefKey->at(0),undefKey->at(1)});
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
                                    const Tuple* aggrTuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                    if(aggrTuple1!=NULL){
                                        const auto & it1 = tupleToVar.find(*aggrTuple1);
                                        if(it1 != tupleToVar.end()) {
                                            propagated=true;
                                            int sign = -1;
                                            propagatedLiterals.insert(it1->second*sign);
                                        }
                                    }
                                    const Tuple* aggrTuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5),undefinedTuples->at(0)->at(6)},&_a));
                                    if(aggrTuple2!=NULL){
                                        const auto & it2 = tupleToVar.find(*aggrTuple2);
                                        if(it2 != tupleToVar.end()) {
                                            propagated=true;
                                            int sign = 1;
                                            propagatedLiterals.insert(it2->second*sign);
                                        }
                                    }
                                }
                            }
                        }
                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].rbegin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].rend();undefKeyIt++){
                            const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                            if(undefPlusTrue+undefKey->at(0)>=1+maxPossibleNegativeSum[0][vIndex])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({undefKey->at(0),undefKey->at(1)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                    bool negativeJoinPropagated=false;
                                    const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                    if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                        if((wa.find(aggrTuple1)!=NULL) ){
                                            const auto & it1 = tupleToVar.find(aggrTuple1);
                                            if(it1 != tupleToVar.end()) {
                                                reas.push_back(it1->second);
                                            }
                                            Tuple aggrTuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_a);
                                            if((wa.find(aggrTuple2)==NULL && ua.find(aggrTuple2)==NULL) ){
                                                const auto & it2 = tupleToVar.find(aggrTuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    reas.push_back(it2->second*-1);
                                                }
                                                const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                if(it0 != tupleToVar.end()) {
                                                    negativeJoinPropagated=true;
                                                    int sign = 1;
                                                    propagatedLiterals.insert(it0->second*sign);
                                                }
                                            }
                                        }
                                    }
                                    const Tuple* aggrTupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                    if(aggrTupleU1!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0)},&_b);
                                        if((wb.find(aggrTuple0)!=NULL) ){
                                            const auto & it0 = tupleToVar.find(aggrTuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple aggrTuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_a);
                                            if((wa.find(aggrTuple2)==NULL && ua.find(aggrTuple2)==NULL) ){
                                                const auto & it2 = tupleToVar.find(aggrTuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    reas.push_back(it2->second*-1);
                                                }
                                                const auto & it1 = tupleToVar.find(*aggrTupleU1);
                                                if(it1 != tupleToVar.end()) {
                                                    negativeJoinPropagated=true;
                                                    int sign = 1;
                                                    propagatedLiterals.insert(it1->second*sign);
                                                }
                                            }
                                        }
                                    }
                                    const Tuple* aggrTupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_a));
                                    if(aggrTupleU2!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0)},&_b);
                                        if((wb.find(aggrTuple0)!=NULL) ){
                                            const auto & it0 = tupleToVar.find(aggrTuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if((wa.find(aggrTuple1)!=NULL) ){
                                                const auto & it1 = tupleToVar.find(aggrTuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                const auto & it2 = tupleToVar.find(*aggrTupleU2);
                                                if(it2 != tupleToVar.end()) {
                                                    negativeJoinPropagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it2->second*sign);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }//close can prop if
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
            if(starter.getPredicateName()== &_b || starter.getPredicateName()== &_a || starter.getPredicateName()== &_a){
                {
                    std::vector<int>sharedBodyV({});
                    unsigned int  sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV)->getId();
                    int undefPlusTrue = actualSum[0][sharedVarsIndex]+possibleSum[0][sharedVarsIndex]+actualNegativeSum[0][sharedVarsIndex]+possibleNegativeSum[0][sharedVarsIndex];
                    //1
                    if(!(undefPlusTrue>=1+maxPossibleNegativeSum[0][sharedVarsIndex])){
                        tupleU=NULL;
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
                                }
                            }
                        }
                    }//close aggr true if
                    else{
                        bool propagated=false;
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int>sharedVars({});
                            unsigned int  vIndex = sharedVariable[0].addElements(sharedVars)->getId();
                            for(auto undefKeyIt = undefAggrVars[0][vIndex].rbegin();undefKeyIt!=undefAggrVars[0][vIndex].rend();undefKeyIt++){
                                const DynamicCompilationVector* undefKey = aggrVariable[0].get(undefKeyIt->getIndex());
                                if(undefPlusTrue-undefKey->at(0)>=1+maxPossibleNegativeSum[0][vIndex])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({undefKey->at(0),undefKey->at(1)});
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
                                                    reasonMapping.addAggrToLit(it0->second*sign,0,false);
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it0->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* aggrTuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                        if(aggrTuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*aggrTuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.insert(it1->second*sign);
                                                bool added = reasonMapping.addPropagation(it1->second*sign);
                                                if(added){
                                                    reasonMapping.setPropLevelToLit(it1->second*sign,currentReasonLevel);
                                                    reasonMapping.addAggrToLit(it1->second*sign,0,false);
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it1->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* aggrTuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5),undefinedTuples->at(0)->at(6)},&_a));
                                        if(aggrTuple2!=NULL){
                                            const auto & it2 = tupleToVar.find(*aggrTuple2);
                                            if(it2 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                propagatedLiterals.insert(it2->second*sign);
                                                bool added = reasonMapping.addPropagation(it2->second*sign);
                                                if(added){
                                                    reasonMapping.setPropLevelToLit(it2->second*sign,currentReasonLevel);
                                                    reasonMapping.addAggrToLit(it2->second*sign,0,false);
                                                    {
                                                        const auto & itr = tupleToVar.find(Tuple(starter));
                                                        if(itr!=tupleToVar.end()){
                                                            reasonMapping.addBodyLitToLit(it2->second*sign,itr->second * (starter.isNegated() ? -1:1));
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
                                if(undefPlusTrue+undefKey->at(0)>=1+maxPossibleNegativeSum[0][vIndex])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_U_a_V_X_Y_not_a_U_V_V_0_2_.getValues({undefKey->at(0),undefKey->at(1)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0)},&_b));
                                        if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if((wa.find(aggrTuple1)!=NULL) ){
                                                const auto & it1 = tupleToVar.find(aggrTuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple aggrTuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_a);
                                                if((wa.find(aggrTuple2)==NULL && ua.find(aggrTuple2)==NULL) ){
                                                    const auto & it2 = tupleToVar.find(aggrTuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second*-1);
                                                    }
                                                    const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                    if(it0 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = 1;
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
                                                            for(int v: reas){
                                                                reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* aggrTupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                        if(aggrTupleU1!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0)},&_b);
                                            if((wb.find(aggrTuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(aggrTuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple aggrTuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_a);
                                                if((wa.find(aggrTuple2)==NULL && ua.find(aggrTuple2)==NULL) ){
                                                    const auto & it2 = tupleToVar.find(aggrTuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second*-1);
                                                    }
                                                    const auto & it1 = tupleToVar.find(*aggrTupleU1);
                                                    if(it1 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = 1;
                                                        propagatedLiterals.insert(it1->second*sign);
                                                        bool added = reasonMapping.addPropagation(it1->second*sign);
                                                        if(added){
                                                            reasonMapping.setPropLevelToLit(it1->second*sign,currentReasonLevel);
                                                            reasonMapping.addAggrToLit(it1->second*sign,0,false);
                                                            {
                                                                const auto & itr = tupleToVar.find(Tuple(starter));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                }
                                                            }
                                                            for(int v: reas){
                                                                reasonMapping.addBodyLitToLit(it1->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* aggrTupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_a));
                                        if(aggrTupleU2!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0)},&_b);
                                            if((wb.find(aggrTuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(aggrTuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if((wa.find(aggrTuple1)!=NULL) ){
                                                    const auto & it1 = tupleToVar.find(aggrTuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second);
                                                    }
                                                    const auto & it2 = tupleToVar.find(*aggrTupleU2);
                                                    if(it2 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.insert(it2->second*sign);
                                                        bool added = reasonMapping.addPropagation(it2->second*sign);
                                                        if(added){
                                                            reasonMapping.setPropLevelToLit(it2->second*sign,currentReasonLevel);
                                                            reasonMapping.addAggrToLit(it2->second*sign,0,false);
                                                            {
                                                                const auto & itr = tupleToVar.find(Tuple(starter));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it2->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                }
                                                            }
                                                            for(int v: reas){
                                                                reasonMapping.addBodyLitToLit(it2->second*sign,v);
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
                    }//close can prop if
                }
            }
        }//local scope
    }
}
}
