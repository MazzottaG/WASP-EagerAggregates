#include "Executor.h"

#include "utils/ConstantsManager.h"

#include "DLV2libs/input/InputDirector.h"

#include "parsing/AspCore2InstanceBuilder.h"

#include "datastructures/PredicateSet.h"

#include "datastructures/ReasonTable.h"

#include "datastructures/PostponedReasons.h"

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
PredicateWSet fb(1);
const std::string _a = "a";
PredicateWSet wa(2);
PredicateWSet ua(2);
PredicateWSet fa(2);
const std::string _c = "c";
PredicateWSet wc(2);
PredicateWSet uc(2);
PredicateWSet fc(2);
const std::string _c_Y_Z_a_X_Z_a_W_X_ = "c_Y_Z_a_X_Z_a_W_X_";
PredicateWSet wc_Y_Z_a_X_Z_a_W_X_(6);
PredicateWSet uc_Y_Z_a_X_Z_a_W_X_(6);
PredicateWSet nwc_Y_Z_a_X_Z_a_W_X_(6);
PredicateWSet nuc_Y_Z_a_X_Z_a_W_X_(6);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_1;
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueNegativeAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefNegativeAggrVars[1];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason[1];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason[1];
std::unordered_map<std::vector<int>, int,TuplesHash> actualSum[1];
std::unordered_map<std::vector<int>, int,TuplesHash> possibleSum[1];
std::unordered_map<std::vector<int>, int,TuplesHash> actualNegativeSum[1];
std::unordered_map<std::vector<int>, int,TuplesHash> possibleNegativeSum[1];
std::unordered_map<std::vector<int>, int,TuplesHash> maxPossibleNegativeSum[1];
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
AuxMap pa_1_({1});
AuxMap ua_1_({1});
AuxMap pc_1_({1});
AuxMap uc_1_({1});
AuxMap pc_({});
AuxMap uc_({});
AuxMap pa_0_1_({0,1});
AuxMap ua_0_1_({0,1});
AuxMap p_c_Y_Z_a_X_Z_a_W_X_({});
AuxMap u_c_Y_Z_a_X_Z_a_W_X_({});
AuxMap np_c_Y_Z_a_X_Z_a_W_X_({});
AuxMap nu_c_Y_Z_a_X_Z_a_W_X_({});
AuxMap p_c_Y_Z_a_X_Z_a_W_X_1_({1});
AuxMap u_c_Y_Z_a_X_Z_a_W_X_1_({1});
AuxMap np_c_Y_Z_a_X_Z_a_W_X_1_({1});
AuxMap nu_c_Y_Z_a_X_Z_a_W_X_1_({1});
AuxMap p_c_Y_Z_a_X_Z_a_W_X_0_1_({0,1});
AuxMap u_c_Y_Z_a_X_Z_a_W_X_0_1_({0,1});
AuxMap np_c_Y_Z_a_X_Z_a_W_X_0_1_({0,1});
AuxMap nu_c_Y_Z_a_X_Z_a_W_X_0_1_({0,1});
AuxMap p_c_Y_Z_a_X_Z_a_W_X_2_3_({2,3});
AuxMap u_c_Y_Z_a_X_Z_a_W_X_2_3_({2,3});
AuxMap np_c_Y_Z_a_X_Z_a_W_X_2_3_({2,3});
AuxMap nu_c_Y_Z_a_X_Z_a_W_X_2_3_({2,3});
AuxMap p_c_Y_Z_a_X_Z_a_W_X_4_5_({4,5});
AuxMap u_c_Y_Z_a_X_Z_a_W_X_4_5_({4,5});
AuxMap np_c_Y_Z_a_X_Z_a_W_X_4_5_({4,5});
AuxMap nu_c_Y_Z_a_X_Z_a_W_X_4_5_({4,5});
AuxMap pb_({});
AuxMap ub_({});
//printing aux maps needed for reasons of negative literals;
void Executor::explainAggrLiteral(int var,std::vector<int>& reas){
    int v = var==-1?var:-var;
    PostponedReasonData* data = &reasonMapping[v];
    if(data->getPropagationLevel() == -1) return;
    std::vector<int> aggregates_id = data->getAggregateId();
    for(int i=0; i < aggregates_id.size();i++){
        int aggr_index=aggregates_id[i];
        if(data->isPositive(i)){
            for(int lit :positiveAggrReason[aggr_index][data->getSharedVariables()].getLiteralUntil(data->getPropagationLevel())){
                reas.push_back(lit);
            }
        }else{
            for(int lit :negativeAggrReason[aggr_index][data->getSharedVariables()].getLiteralUntil(data->getPropagationLevel())){
                reas.push_back(lit);
            }
        }
    }
    for(int l : data->getBodyReason()){
        reas.push_back(l);
    }
    return;
}
//printing functions prototypes for reasons of negative literals;
void explainPositiveLiteral(const Tuple *, std::unordered_set<std::string> &, std::vector<const Tuple*> &);
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
    if(tuple.getPredicateName() == &_c){
        int Y = tuple[0];
        int Z = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>* tuples1 = &pa_1_.getValues({Z});
            for(int i_1=0;i_1<tuples1->size();i_1++){
                const Tuple* tuple1=tuples1->at(i_1);
                int X = tuple1->at(0);
                const std::vector<const Tuple*>* tuples2 = &pa_1_.getValues({X});
                for(int i_2=0;i_2<tuples2->size();i_2++){
                    const Tuple* tuple2=tuples2->at(i_2);
                    int W = tuple2->at(0);
                    Tuple t({Y,Z,X,Z,W,X},&_c_Y_Z_a_X_Z_a_W_X_);
                    {
                        std::vector<int> aggrKey({t[1]});
                        if(aggrKey[0]>=0){
                            if(wc_Y_Z_a_X_Z_a_W_X_.find(t)==NULL){
                                if(uc_Y_Z_a_X_Z_a_W_X_.find(t))
                                    uc_Y_Z_a_X_Z_a_W_X_.erase(t);
                                const auto& insertResult = wc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(undefSet.find(aggrKey)!=undefSet.end()){
                                    undefSet.erase(aggrKey);
                                    possibleSum[0][{}]-=aggrKey[0];
                                }
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    trueSet.insert(aggrKey);
                                    actualSum[0][{}]+=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
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
                                            reas.insert(it->second);
                                        }
                                    }
                                }
                            }
                        }else{
                            if(nwc_Y_Z_a_X_Z_a_W_X_.find(t)==NULL){
                                if(nuc_Y_Z_a_X_Z_a_W_X_.find(t))
                                    nuc_Y_Z_a_X_Z_a_W_X_.erase(t);
                                const auto& insertResult = nwc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                auto& reas = negativeAggrReason[0][{}];
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
                                        reas.insert(it->second);
                                    }
                                }
                                possibleNegativeSum[0][{}]+=aggrKey[0];
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_c_Y_Z_a_X_Z_a_W_X_0_1_.getValues({Y,Z});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[1]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_c_Y_Z_a_X_Z_a_W_X_0_1_.getValues({Y,Z});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nuc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[1]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleNegativeSum[0][{}]+=aggrKey[0];
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                                actualNegativeSum[0][{}]-=aggrKey[0];
                            }
                        }
                    }
                    auto& reas = positiveAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_a){
        int X = tuple[0];
        int Z = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pc_1_.getValues({Z});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int Y = tuple0->at(0);
                const std::vector<const Tuple*>* tuples2 = &pa_1_.getValues({X});
                for(int i_2=0;i_2<tuples2->size();i_2++){
                    const Tuple* tuple2=tuples2->at(i_2);
                    int W = tuple2->at(0);
                    Tuple t({Y,Z,X,Z,W,X},&_c_Y_Z_a_X_Z_a_W_X_);
                    {
                        std::vector<int> aggrKey({t[1]});
                        if(aggrKey[0]>=0){
                            if(wc_Y_Z_a_X_Z_a_W_X_.find(t)==NULL){
                                if(uc_Y_Z_a_X_Z_a_W_X_.find(t))
                                    uc_Y_Z_a_X_Z_a_W_X_.erase(t);
                                const auto& insertResult = wc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(undefSet.find(aggrKey)!=undefSet.end()){
                                    undefSet.erase(aggrKey);
                                    possibleSum[0][{}]-=aggrKey[0];
                                }
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    trueSet.insert(aggrKey);
                                    actualSum[0][{}]+=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
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
                                            reas.insert(it->second);
                                        }
                                    }
                                }
                            }
                        }else{
                            if(nwc_Y_Z_a_X_Z_a_W_X_.find(t)==NULL){
                                if(nuc_Y_Z_a_X_Z_a_W_X_.find(t))
                                    nuc_Y_Z_a_X_Z_a_W_X_.erase(t);
                                const auto& insertResult = nwc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                auto& reas = negativeAggrReason[0][{}];
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
                                        reas.insert(it->second);
                                    }
                                }
                                possibleNegativeSum[0][{}]+=aggrKey[0];
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_c_Y_Z_a_X_Z_a_W_X_2_3_.getValues({X,Z});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[1]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_c_Y_Z_a_X_Z_a_W_X_2_3_.getValues({X,Z});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nuc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[1]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleNegativeSum[0][{}]+=aggrKey[0];
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                                actualNegativeSum[0][{}]-=aggrKey[0];
                            }
                        }
                    }
                    auto& reas = positiveAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_a){
        int W = tuple[0];
        int X = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pc_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int Y = tuple0->at(0);
                int Z = tuple0->at(1);
                const Tuple* tuple1 = wa.find(Tuple({X,Z},&_a));
                if(tuple1!=NULL){
                    Tuple t({Y,Z,X,Z,W,X},&_c_Y_Z_a_X_Z_a_W_X_);
                    {
                        std::vector<int> aggrKey({t[1]});
                        if(aggrKey[0]>=0){
                            if(wc_Y_Z_a_X_Z_a_W_X_.find(t)==NULL){
                                if(uc_Y_Z_a_X_Z_a_W_X_.find(t))
                                    uc_Y_Z_a_X_Z_a_W_X_.erase(t);
                                const auto& insertResult = wc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(undefSet.find(aggrKey)!=undefSet.end()){
                                    undefSet.erase(aggrKey);
                                    possibleSum[0][{}]-=aggrKey[0];
                                }
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    trueSet.insert(aggrKey);
                                    actualSum[0][{}]+=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
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
                            if(nwc_Y_Z_a_X_Z_a_W_X_.find(t)==NULL){
                                if(nuc_Y_Z_a_X_Z_a_W_X_.find(t))
                                    nuc_Y_Z_a_X_Z_a_W_X_.erase(t);
                                const auto& insertResult = nwc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                auto& reas = negativeAggrReason[0][{}];
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
                                possibleNegativeSum[0][{}]+=aggrKey[0];
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_c_Y_Z_a_X_Z_a_W_X_4_5_.getValues({W,X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[1]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_c_Y_Z_a_X_Z_a_W_X_4_5_.getValues({W,X});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nuc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[1]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleNegativeSum[0][{}]+=aggrKey[0];
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                                actualNegativeSum[0][{}]-=aggrKey[0];
                            }
                        }
                    }
                    auto& reas = positiveAggrReason[0][{}];
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
    if(tuple.getPredicateName() == &_c && tuple.size()==2){
        int Y = tuple[0];
        int Z = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_c_Y_Z_a_X_Z_a_W_X_0_1_.getValues({Y,Z});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wc_Y_Z_a_X_Z_a_W_X_.erase(*tuples.back());
                if(uc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{}]-=aggrKey[0];
                            }
                        }
                        if(undefSet.find(aggrKey)==undefSet.end()){
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                undefSet.insert(aggrKey);
                                possibleSum[0][{}]+=aggrKey[0];
                            }
                        }
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesN = np_c_Y_Z_a_X_Z_a_W_X_0_1_.getValues({Y,Z});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesN.back());
                if(nuc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nuc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleNegativeSum[0][{}]-=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }
        }
        const std::vector<const Tuple*>& tuples1 = pa_1_.getValues({Z});
        const std::vector<const Tuple*>& tuplesU1 = ua_1_.getValues({Z});
        for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
            const Tuple* tuple1;
            bool undef1=false;
            if(i_1<tuples1.size())                tuple1=tuples1[i_1];
            else{
                tuple1=tuplesU1[i_1-tuples1.size()];
                undef1=true;
            }
            int X = tuple1->at(0);
            const std::vector<const Tuple*>& tuples2 = pa_1_.getValues({X});
            const std::vector<const Tuple*>& tuplesU2 = ua_1_.getValues({X});
            for(int i_2=0;i_2<tuples2.size()+tuplesU2.size();i_2++){
                const Tuple* tuple2;
                bool undef2=false;
                if(i_2<tuples2.size())                    tuple2=tuples2[i_2];
                else{
                    tuple2=tuplesU2[i_2-tuples2.size()];
                    undef2=true;
                }
                int W = tuple2->at(0);
                Tuple t({Y,Z,X,Z,W,X},&_c_Y_Z_a_X_Z_a_W_X_);
                {
                    std::vector<int> aggrKey({t[1]});
                    if(aggrKey[0]>=0){
                        if(uc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t))==NULL){
                            if(wc_Y_Z_a_X_Z_a_W_X_.find(t))
                                wc_Y_Z_a_X_Z_a_W_X_.erase(t);
                            const auto& insertResult = uc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{}]-=aggrKey[0];
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleSum[0][{}]+=aggrKey[0];
                                }
                            }
                        }
                    }else{
                        if(nuc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t))==NULL){
                            if(nwc_Y_Z_a_X_Z_a_W_X_.find(t))
                                nwc_Y_Z_a_X_Z_a_W_X_.erase(t);
                            const auto& insertResult = nuc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualNegativeSum[0][{}]+=aggrKey[0];
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleNegativeSum[0][{}]-=aggrKey[0];
                                    int possSum = possibleNegativeSum[0][{}];
                                    if(maxPossibleNegativeSum[0][{}]<possSum)
                                        maxPossibleNegativeSum[0][{}]=possSum;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int X = tuple[0];
        int Z = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_c_Y_Z_a_X_Z_a_W_X_2_3_.getValues({X,Z});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wc_Y_Z_a_X_Z_a_W_X_.erase(*tuples.back());
                if(uc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{}]-=aggrKey[0];
                            }
                        }
                        if(undefSet.find(aggrKey)==undefSet.end()){
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                undefSet.insert(aggrKey);
                                possibleSum[0][{}]+=aggrKey[0];
                            }
                        }
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesN = np_c_Y_Z_a_X_Z_a_W_X_2_3_.getValues({X,Z});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesN.back());
                if(nuc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nuc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleNegativeSum[0][{}]-=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }
        }
        const std::vector<const Tuple*>& tuples0 = pc_1_.getValues({Z});
        const std::vector<const Tuple*>& tuplesU0 = uc_1_.getValues({Z});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int Y = tuple0->at(0);
            const std::vector<const Tuple*>& tuples2 = pa_1_.getValues({X});
            const std::vector<const Tuple*>& tuplesU2 = ua_1_.getValues({X});
            for(int i_2=0;i_2<tuples2.size()+tuplesU2.size();i_2++){
                const Tuple* tuple2;
                bool undef2=false;
                if(i_2<tuples2.size())                    tuple2=tuples2[i_2];
                else{
                    tuple2=tuplesU2[i_2-tuples2.size()];
                    undef2=true;
                }
                int W = tuple2->at(0);
                Tuple t({Y,Z,X,Z,W,X},&_c_Y_Z_a_X_Z_a_W_X_);
                {
                    std::vector<int> aggrKey({t[1]});
                    if(aggrKey[0]>=0){
                        if(uc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t))==NULL){
                            if(wc_Y_Z_a_X_Z_a_W_X_.find(t))
                                wc_Y_Z_a_X_Z_a_W_X_.erase(t);
                            const auto& insertResult = uc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{}]-=aggrKey[0];
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleSum[0][{}]+=aggrKey[0];
                                }
                            }
                        }
                    }else{
                        if(nuc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t))==NULL){
                            if(nwc_Y_Z_a_X_Z_a_W_X_.find(t))
                                nwc_Y_Z_a_X_Z_a_W_X_.erase(t);
                            const auto& insertResult = nuc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualNegativeSum[0][{}]+=aggrKey[0];
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleNegativeSum[0][{}]-=aggrKey[0];
                                    int possSum = possibleNegativeSum[0][{}];
                                    if(maxPossibleNegativeSum[0][{}]<possSum)
                                        maxPossibleNegativeSum[0][{}]=possSum;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int W = tuple[0];
        int X = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_c_Y_Z_a_X_Z_a_W_X_4_5_.getValues({W,X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wc_Y_Z_a_X_Z_a_W_X_.erase(*tuples.back());
                if(uc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{}]-=aggrKey[0];
                            }
                        }
                        if(undefSet.find(aggrKey)==undefSet.end()){
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                undefSet.insert(aggrKey);
                                possibleSum[0][{}]+=aggrKey[0];
                            }
                        }
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesN = np_c_Y_Z_a_X_Z_a_W_X_4_5_.getValues({W,X});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwc_Y_Z_a_X_Z_a_W_X_.erase(*tuplesN.back());
                if(nuc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nuc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[1]});
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleNegativeSum[0][{}]-=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }
        }
        const std::vector<const Tuple*>& tuples0 = pc_.getValues({});
        const std::vector<const Tuple*>& tuplesU0 = uc_.getValues({});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int Y = tuple0->at(0);
            int Z = tuple0->at(1);
            const Tuple* tuple1 = wa.find(Tuple({X,Z},&_a));
            bool undef1 = false;
            if(tuple1==NULL){
                tuple1 = ua.find(Tuple({X,Z},&_a));
                undef1 = true;
            }
            if(tuple1!=NULL){
                Tuple t({Y,Z,X,Z,W,X},&_c_Y_Z_a_X_Z_a_W_X_);
                {
                    std::vector<int> aggrKey({t[1]});
                    if(aggrKey[0]>=0){
                        if(uc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t))==NULL){
                            if(wc_Y_Z_a_X_Z_a_W_X_.find(t))
                                wc_Y_Z_a_X_Z_a_W_X_.erase(t);
                            const auto& insertResult = uc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{}]-=aggrKey[0];
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleSum[0][{}]+=aggrKey[0];
                                }
                            }
                        }
                    }else{
                        if(nuc_Y_Z_a_X_Z_a_W_X_.find(Tuple(t))==NULL){
                            if(nwc_Y_Z_a_X_Z_a_W_X_.find(t))
                                nwc_Y_Z_a_X_Z_a_W_X_.erase(t);
                            const auto& insertResult = nuc_Y_Z_a_X_Z_a_W_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        if(np_c_Y_Z_a_X_Z_a_W_X_1_.getValues({aggrKey}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualNegativeSum[0][{}]+=aggrKey[0];
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleNegativeSum[0][{}]-=aggrKey[0];
                                    int possSum = possibleNegativeSum[0][{}];
                                    if(maxPossibleNegativeSum[0][{}]<possSum)
                                        maxPossibleNegativeSum[0][{}]=possSum;
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
    propagatedLiterals.clear();
}
void Executor::clear() {
    failedConstraints.clear();
    predicateToAuxiliaryMaps.clear();
}
void Executor::init() {
    createFunctionsMap();
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_c]=&wc;
    predicateFSetMap[&_c]=&fc;
    predicateUSetMap[&_c]=&uc;
    stringToUniqueStringPointer["c"] = &_c;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&p_c_Y_Z_a_X_Z_a_W_X_);
    predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&p_c_Y_Z_a_X_Z_a_W_X_0_1_);
    predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&p_c_Y_Z_a_X_Z_a_W_X_1_);
    predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&p_c_Y_Z_a_X_Z_a_W_X_2_3_);
    predicateToAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&p_c_Y_Z_a_X_Z_a_W_X_4_5_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_1_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_1_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_1_);
    predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&np_c_Y_Z_a_X_Z_a_W_X_);
    predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&np_c_Y_Z_a_X_Z_a_W_X_0_1_);
    predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&np_c_Y_Z_a_X_Z_a_W_X_1_);
    predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&np_c_Y_Z_a_X_Z_a_W_X_2_3_);
    predicateToNegativeAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&np_c_Y_Z_a_X_Z_a_W_X_4_5_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&u_c_Y_Z_a_X_Z_a_W_X_);
    predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&u_c_Y_Z_a_X_Z_a_W_X_0_1_);
    predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&u_c_Y_Z_a_X_Z_a_W_X_1_);
    predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&u_c_Y_Z_a_X_Z_a_W_X_2_3_);
    predicateToUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&u_c_Y_Z_a_X_Z_a_W_X_4_5_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_1_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_1_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&nu_c_Y_Z_a_X_Z_a_W_X_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&nu_c_Y_Z_a_X_Z_a_W_X_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&nu_c_Y_Z_a_X_Z_a_W_X_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&nu_c_Y_Z_a_X_Z_a_W_X_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_Y_Z_a_X_Z_a_W_X_].push_back(&nu_c_Y_Z_a_X_Z_a_W_X_4_5_);
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
                int V = (*tuple0)[0];
                int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                //V
                if(!(undefPlusTrue>=V+maxPossibleNegativeSum[0][{}])){
                    if(tupleU == NULL){
                        std::cout<<"propagation started from literal"<<std::endl;
                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                        propagatedLiterals.push_back(-1);
                    }else{
                        const auto & it = tupleToVar.find(*tupleU);
                        if(it != tupleToVar.end()) {
                            int sign = tupleUNegated ? -1 : 1;
                            propagatedLiterals.push_back(it->second*sign);
                        }
                    }
                }
                if(tupleU == NULL){
                    {
                        int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                        bool propagated=false;
                        {
                            for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                if(undefPlusTrue-undefKey->at(0)>=V+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_c_Y_Z_a_X_Z_a_W_X_1_.getValues(*undefKey);
                                    if(undefinedTuples->size()==1){

                                        const Tuple* tuple0 = uc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_c));
                                        if(tuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it0->second*sign);
                                            }
                                        }
                                        const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                        if(tuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it1->second*sign);
                                            }
                                        }
                                        const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5)},&_a));
                                        if(tuple2!=NULL){
                                            const auto & it2 = tupleToVar.find(*tuple2);
                                            if(it2 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it2->second*sign);
                                            }
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                if(undefPlusTrue+undefKey->at(0)>=V+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_c_Y_Z_a_X_Z_a_W_X_1_.getValues({undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c));
                                        if(tupleU0!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if((wa.find(tuple1)!=NULL) ){
                                                const auto & it1 = tupleToVar.find(tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a);
                                                if((wa.find(tuple2)!=NULL) ){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                    const auto & it0 = tupleToVar.find(*tupleU0);
                                                    if(it0 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = 1;
                                                        propagatedLiterals.push_back(it0->second*sign);
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                        if(tupleU1!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c);
                                            if((wc.find(tuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a);
                                                if((wa.find(tuple2)!=NULL)  || *tupleU1==tuple2){
                                                    if(*tupleU1!=tuple2){
                                                        const auto & it2 = tupleToVar.find(tuple2);
                                                        if(it2 != tupleToVar.end()) {
                                                            reas.push_back(it2->second);
                                                        }
                                                    }
                                                    const auto & it1 = tupleToVar.find(*tupleU1);
                                                    if(it1 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = 1;
                                                        propagatedLiterals.push_back(it1->second*sign);
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a));
                                        if(tupleU2!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c);
                                            if((wc.find(tuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if((wa.find(tuple1)!=NULL)  || *tupleU2==tuple1){
                                                    if(*tupleU2!=tuple1){
                                                        const auto & it1 = tupleToVar.find(tuple1);
                                                        if(it1 != tupleToVar.end()) {
                                                            reas.push_back(it1->second);
                                                        }
                                                    }
                                                    const auto & it2 = tupleToVar.find(*tupleU2);
                                                    if(it2 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = 1;
                                                        propagatedLiterals.push_back(it2->second*sign);
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
        }//close local scope
    }//close decision level == -1
    for(unsigned i=1;i<facts.size();i++) {
        unsigned factVar = facts[i] > 0 ? facts[i] : -facts[i];
        Tuple starter = atomsTable[factVar];
        starter.setNegated(facts[i]<0);
        if(starter.getPredicateName() == &_b) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int V = (*tuple0)[0];
                    int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                    //V
                    if(!(undefPlusTrue>=V+maxPossibleNegativeSum[0][{}])){
                        std::vector<int> aggregates_id({0});
                        std::vector<bool> aggregates_sign({false});
                        std::vector<int> bodyReason;
                        const auto & it = tupleToVar.find(Tuple(starter));
                        if(it!=tupleToVar.end()){
                            bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
                        }
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiterals.push_back(-1);
                            reasonMapping.addPropagation(-1,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                        }else{
                            const auto & it = tupleToVar.find(*tupleU);
                            if(it != tupleToVar.end()) {
                                int sign = tupleUNegated ? -1 : 1;
                                propagatedLiterals.push_back(it->second*sign);
                                reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                            bool propagated=false;
                            {
                                PostponedReasonData p();

                                std::vector<int> aggregates_id({0});
                                std::vector<bool> aggregates_sign({false});
                                std::vector<int> bodyReason;
                                if(tuple0!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple0));
                                    if(it!=tupleToVar.end()){
                                        bodyReason.push_back(it->second);
                                    }
                                }
                                for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                    if(undefPlusTrue-undefKey->at(0)>=V+maxPossibleNegativeSum[0][{}])
                                        break;
                                    else{
                                        const std::vector<const Tuple*>* undefinedTuples = &u_c_Y_Z_a_X_Z_a_W_X_1_.getValues(*undefKey);
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_c));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.push_back(it0->second*sign);
                                                    reasonMapping.addPropagation(it0->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                }
                                            }
                                            const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.push_back(it1->second*sign);
                                                    reasonMapping.addPropagation(it1->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                }
                                            }
                                            const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5)},&_a));
                                            if(tuple2!=NULL){
                                                const auto & it2 = tupleToVar.find(*tuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.push_back(it2->second*sign);
                                                    reasonMapping.addPropagation(it2->second*sign);
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                    if(undefPlusTrue+undefKey->at(0)>=V+maxPossibleNegativeSum[0][{}])
                                        break;
                                    else{
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_c_Y_Z_a_X_Z_a_W_X_1_.getValues({undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                            bool negativeJoinPropagated=false;
                                            const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c));
                                            if(tupleU0!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if((wa.find(tuple1)!=NULL) ){
                                                    const auto & it1 = tupleToVar.find(tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second);
                                                    }
                                                    Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a);
                                                    if((wa.find(tuple2)!=NULL) ){
                                                        const auto & it2 = tupleToVar.find(tuple2);
                                                        if(it2 != tupleToVar.end()) {
                                                            reas.push_back(it2->second);
                                                        }
                                                        const auto & it0 = tupleToVar.find(*tupleU0);
                                                        if(it0 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = 1;
                                                            propagatedLiterals.push_back(it0->second*sign);
                                                            for(int v: reas){ bodyReason.push_back(v); }
                                                            reasonMapping.addPropagation(it0->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                            while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}
                                                        }
                                                    }
                                                }
                                            }
                                            const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                            if(tupleU1!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c);
                                                if((wc.find(tuple0)!=NULL) ){
                                                    const auto & it0 = tupleToVar.find(tuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        reas.push_back(it0->second);
                                                    }
                                                    Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a);
                                                    if((wa.find(tuple2)!=NULL)  || *tupleU1==tuple2){
                                                        if(*tupleU1!=tuple2){
                                                            const auto & it2 = tupleToVar.find(tuple2);
                                                            if(it2 != tupleToVar.end()) {
                                                                reas.push_back(it2->second);
                                                            }
                                                        }
                                                        const auto & it1 = tupleToVar.find(*tupleU1);
                                                        if(it1 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = 1;
                                                            propagatedLiterals.push_back(it1->second*sign);
                                                            for(int v: reas){ bodyReason.push_back(v); }
                                                            reasonMapping.addPropagation(it1->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                            while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}
                                                        }
                                                    }
                                                }
                                            }
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a));
                                            if(tupleU2!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c);
                                                if((wc.find(tuple0)!=NULL) ){
                                                    const auto & it0 = tupleToVar.find(tuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        reas.push_back(it0->second);
                                                    }
                                                    Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                    if((wa.find(tuple1)!=NULL)  || *tupleU2==tuple1){
                                                        if(*tupleU2!=tuple1){
                                                            const auto & it1 = tupleToVar.find(tuple1);
                                                            if(it1 != tupleToVar.end()) {
                                                                reas.push_back(it1->second);
                                                            }
                                                        }
                                                        const auto & it2 = tupleToVar.find(*tupleU2);
                                                        if(it2 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = 1;
                                                            propagatedLiterals.push_back(it2->second*sign);
                                                            for(int v: reas){ bodyReason.push_back(v); }
                                                            reasonMapping.addPropagation(it2->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                            while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}
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
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_c || starter.getPredicateName()== &_a || starter.getPredicateName()== &_a){
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
                        int V = (*tuple1)[0];
                        int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                        //V
                        if(!(undefPlusTrue>=V+maxPossibleNegativeSum[0][{}])){
                            std::vector<int> aggregates_id({0});
                            std::vector<bool> aggregates_sign({false});
                            std::vector<int> bodyReason;
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    bodyReason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from Aggr"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiterals.push_back(-1);
                                reasonMapping.addPropagation(-1,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiterals.push_back(it->second*sign);
                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                }
                            }
                        }else{
                            bool propagated=false;
                            {
                                if(tupleU == NULL){
                                    std::vector<int> local_reason;
                                    std::vector<int> aggregates_id({0});
                                    std::vector<bool> aggregates_sign({false});
                                    std::vector<int> bodyReason;
                                    const auto & it = tupleToVar.find(Tuple(starter));
                                    if(it!=tupleToVar.end()){
                                        bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            bodyReason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                        if(undefPlusTrue-undefKey->at(0)>=V+maxPossibleNegativeSum[0][{}])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &u_c_Y_Z_a_X_Z_a_W_X_1_.getValues(*undefKey);
                                            if(undefinedTuples->size()==1){

                                                const Tuple* tuple0 = uc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_c));
                                                if(tuple0!=NULL){
                                                    const auto & it0 = tupleToVar.find(*tuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.push_back(it0->second*sign);
                                                        reasonMapping.addPropagation(it0->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                    }
                                                }
                                                const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                                if(tuple1!=NULL){
                                                    const auto & it1 = tupleToVar.find(*tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.push_back(it1->second*sign);
                                                        reasonMapping.addPropagation(it1->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                    }
                                                }
                                                const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5)},&_a));
                                                if(tuple2!=NULL){
                                                    const auto & it2 = tupleToVar.find(*tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.push_back(it2->second*sign);
                                                        reasonMapping.addPropagation(it2->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                        if(undefPlusTrue+undefKey->at(0)>=V+maxPossibleNegativeSum[0][{}])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &nu_c_Y_Z_a_X_Z_a_W_X_1_.getValues({undefKey->at(0)});
                                            for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                                bool negativeJoinPropagated=false;
                                                const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c));
                                                if(tupleU0!=NULL && !negativeJoinPropagated){
                                                    std::vector<int> reas;
                                                    Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                    if((wa.find(tuple1)!=NULL) ){
                                                        const auto & it1 = tupleToVar.find(tuple1);
                                                        if(it1 != tupleToVar.end()) {
                                                            reas.push_back(it1->second);
                                                        }
                                                        Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a);
                                                        if((wa.find(tuple2)!=NULL) ){
                                                            const auto & it2 = tupleToVar.find(tuple2);
                                                            if(it2 != tupleToVar.end()) {
                                                                reas.push_back(it2->second);
                                                            }
                                                            const auto & it0 = tupleToVar.find(*tupleU0);
                                                            if(it0 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                int sign = 1;
                                                                propagatedLiterals.push_back(it0->second*sign);
                                                                for(int v: reas){ bodyReason.push_back(v); }
                                                                reasonMapping.addPropagation(it0->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                                while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}
                                                            }
                                                        }
                                                    }
                                                }
                                                const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                                if(tupleU1!=NULL && !negativeJoinPropagated){
                                                    std::vector<int> reas;
                                                    Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c);
                                                    if((wc.find(tuple0)!=NULL) ){
                                                        const auto & it0 = tupleToVar.find(tuple0);
                                                        if(it0 != tupleToVar.end()) {
                                                            reas.push_back(it0->second);
                                                        }
                                                        Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a);
                                                        if((wa.find(tuple2)!=NULL)  || *tupleU1==tuple2){
                                                            if(*tupleU1!=tuple2){
                                                                const auto & it2 = tupleToVar.find(tuple2);
                                                                if(it2 != tupleToVar.end()) {
                                                                    reas.push_back(it2->second);
                                                                }
                                                            }
                                                            const auto & it1 = tupleToVar.find(*tupleU1);
                                                            if(it1 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                int sign = 1;
                                                                propagatedLiterals.push_back(it1->second*sign);
                                                                for(int v: reas){ bodyReason.push_back(v); }
                                                                reasonMapping.addPropagation(it1->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                                while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}
                                                            }
                                                        }
                                                    }
                                                }
                                                const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5)},&_a));
                                                if(tupleU2!=NULL && !negativeJoinPropagated){
                                                    std::vector<int> reas;
                                                    Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_c);
                                                    if((wc.find(tuple0)!=NULL) ){
                                                        const auto & it0 = tupleToVar.find(tuple0);
                                                        if(it0 != tupleToVar.end()) {
                                                            reas.push_back(it0->second);
                                                        }
                                                        Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                        if((wa.find(tuple1)!=NULL)  || *tupleU2==tuple1){
                                                            if(*tupleU2!=tuple1){
                                                                const auto & it1 = tupleToVar.find(tuple1);
                                                                if(it1 != tupleToVar.end()) {
                                                                    reas.push_back(it1->second);
                                                                }
                                                            }
                                                            const auto & it2 = tupleToVar.find(*tupleU2);
                                                            if(it2 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                int sign = 1;
                                                                propagatedLiterals.push_back(it2->second*sign);
                                                                for(int v: reas){ bodyReason.push_back(v); }
                                                                reasonMapping.addPropagation(it2->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                                while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}
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
                    //nested join closed
                }
            }
        }//local scope
    }
}
}
