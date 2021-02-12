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
const std::string _a = "a";
PredicateWSet wa(1);
PredicateWSet ua(1);
PredicateWSet fa(1);
const std::string _b = "b";
PredicateWSet wb(3);
PredicateWSet ub(3);
PredicateWSet fb(3);
const std::string _b_Z_V_U_a_Y_a_X_not_b_X_Z_V_ = "b_Z_V_U_a_Y_a_X_not_b_X_Z_V_";
PredicateWSet wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_(8);
PredicateWSet ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_(8);
PredicateWSet nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_(8);
PredicateWSet nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_(8);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_0;
std::set<std::vector<int>> sharedVariables_1_ToAggregate_0;
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
AuxMap pb_0_1_2_({0,1,2});
AuxMap ub_0_1_2_({0,1,2});
AuxMap fb_0_1_2_({0,1,2});
AuxMap pb_({});
AuxMap ub_({});
AuxMap fb_({});
AuxMap pa_({});
AuxMap ua_({});
AuxMap fa_({});
AuxMap pa_0_({0});
AuxMap ua_0_({0});
AuxMap fa_0_({0});
AuxMap pb_0_1_({0,1});
AuxMap ub_0_1_({0,1});
AuxMap fb_0_1_({0,1});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_({2});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_({2});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_({2});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_({2});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_({});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_({});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_({});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_({});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_({0,1,2});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_({0,1,2});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_({0,1,2});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_({0,1,2});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_({3});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_({3});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_({3});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_({3});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_({4});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_({4});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_({4});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_({4});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_({5,6,7});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_({5,6,7});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_({5,6,7});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_({5,6,7});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_({0,1,2,2});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_({0,1,2,2});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_({0,1,2,2});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_({0,1,2,2});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_({3,2});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_({3,2});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_({3,2});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_({3,2});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_({4,2});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_({4,2});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_({4,2});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_({4,2});
AuxMap p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_({5,6,7,2});
AuxMap u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_({5,6,7,2});
AuxMap np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_({5,6,7,2});
AuxMap nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_({5,6,7,2});
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
    if(tuple.getPredicateName() == &_b){
        int Z = tuple[0];
        int V = tuple[1];
        int U = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
            for(int i_1=0;i_1<tuples1->size();i_1++){
                const Tuple* tuple1=tuples1->at(i_1);
                int Y = tuple1->at(0);
                const std::vector<const Tuple*>* tuples2 = &pa_.getValues({});
                for(int i_2=0;i_2<tuples2->size();i_2++){
                    const Tuple* tuple2=tuples2->at(i_2);
                    int X = tuple2->at(0);
                    const Tuple negativeTuple3({X,Z,V},&_b,true);
                    const Tuple* tuple3 = ub.find(Tuple({X,Z,V},&_b));
                    if(wb.find(negativeTuple3)==NULL && tuple3==NULL){
                        tuple3=&negativeTuple3;
                        if((*tuple3)[0]!=tuple[0] || (*tuple3)[1]!=tuple[1] || (*tuple3)[2]!=tuple[2]){
                            Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple3);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple3);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_.getValues({Z,V,U});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_.getValues({Z,V,U});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
        int Y = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pb_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int Z = tuple0->at(0);
                int V = tuple0->at(1);
                int U = tuple0->at(2);
                const std::vector<const Tuple*>* tuples2 = &pa_.getValues({});
                for(int i_2=0;i_2<tuples2->size();i_2++){
                    const Tuple* tuple2=tuples2->at(i_2);
                    int X = tuple2->at(0);
                    const Tuple negativeTuple3({X,Z,V},&_b,true);
                    const Tuple* tuple3 = ub.find(Tuple({X,Z,V},&_b));
                    if(wb.find(negativeTuple3)==NULL && tuple3==NULL){
                        tuple3=&negativeTuple3;
                        if((*tuple3)[0]!=(*tuple0)[0] || (*tuple3)[1]!=(*tuple0)[1] || (*tuple3)[2]!=(*tuple0)[2]){
                            Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple3);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple3);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_.getValues({Y});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_.getValues({Y});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pb_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int Z = tuple0->at(0);
                int V = tuple0->at(1);
                int U = tuple0->at(2);
                const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
                for(int i_1=0;i_1<tuples1->size();i_1++){
                    const Tuple* tuple1=tuples1->at(i_1);
                    int Y = tuple1->at(0);
                    const Tuple negativeTuple3({X,Z,V},&_b,true);
                    const Tuple* tuple3 = ub.find(Tuple({X,Z,V},&_b));
                    if(wb.find(negativeTuple3)==NULL && tuple3==NULL){
                        tuple3=&negativeTuple3;
                        if((*tuple3)[0]!=(*tuple0)[0] || (*tuple3)[1]!=(*tuple0)[1] || (*tuple3)[2]!=(*tuple0)[2]){
                            Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple3);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple3);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_.getValues({X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_.getValues({X});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_b){
        int X = tuple[0];
        int Z = tuple[1];
        int V = tuple[2];
        if(var < 0){
            const std::vector<const Tuple*>* tuples0 = &pb_0_1_.getValues({Z,V});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                if((*tuple0)[0]!=tuple[0] || (*tuple0)[1]!=tuple[1] || (*tuple0)[2]!=tuple[2]){
                    int U = tuple0->at(2);
                    const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
                    for(int i_1=0;i_1<tuples1->size();i_1++){
                        const Tuple* tuple1=tuples1->at(i_1);
                        int Y = tuple1->at(0);
                        const Tuple* tuple2 = wa.find(Tuple({X},&_a));
                        if(tuple2!=NULL){
                            Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple2);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                            {
                                std::vector<int> aggrKey({t[2]});
                                if(aggrKey[0]>=0){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                                            {
                                                const auto & it = tupleToVar.find(*tuple2);
                                                if(it != tupleToVar.end()) {
                                                    reas.insert(it->second);
                                                }
                                            }
                                        }
                                    }
                                }else{
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t)==NULL){
                                        if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                            nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                        const auto& insertResult = nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
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
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_.getValues({X,Z,V});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_.getValues({X,Z,V});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                {
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_b && tuple.size()==3){
        int Z = tuple[0];
        int V = tuple[1];
        int U = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_.getValues({Z,V,U});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuples.back());
                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_.getValues({Z,V,U});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesN.back());
                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            int Y = tuple1->at(0);
            const std::vector<const Tuple*>& tuples2 = pa_.getValues({});
            const std::vector<const Tuple*>& tuplesU2 = ua_.getValues({});
            for(int i_2=0;i_2<tuples2.size()+tuplesU2.size();i_2++){
                const Tuple* tuple2;
                bool undef2=false;
                if(i_2<tuples2.size())                    tuple2=tuples2[i_2];
                else{
                    tuple2=tuplesU2[i_2-tuples2.size()];
                    undef2=true;
                }
                int X = tuple2->at(0);
                const Tuple negativeTuple3({X,Z,V},&_b,true);
                const Tuple* tuple3 = ub.find(Tuple({X,Z,V},&_b));
                bool undef3 = false;
                if(tuple3!=NULL){
                    undef3 = true;
                }else if(wb.find(negativeTuple3)==NULL){
                    tuple3=&negativeTuple3;
                }
                if(tuple3!=NULL){
                    if((*tuple3)[0]!=tuple[0] || (*tuple3)[1]!=tuple[1] || (*tuple3)[2]!=tuple[2]){
                        Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==1){
        int Y = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_.getValues({Y});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuples.back());
                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_.getValues({Y});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesN.back());
                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            int Z = tuple0->at(0);
            int V = tuple0->at(1);
            int U = tuple0->at(2);
            const std::vector<const Tuple*>& tuples2 = pa_.getValues({});
            const std::vector<const Tuple*>& tuplesU2 = ua_.getValues({});
            for(int i_2=0;i_2<tuples2.size()+tuplesU2.size();i_2++){
                const Tuple* tuple2;
                bool undef2=false;
                if(i_2<tuples2.size())                    tuple2=tuples2[i_2];
                else{
                    tuple2=tuplesU2[i_2-tuples2.size()];
                    undef2=true;
                }
                int X = tuple2->at(0);
                const Tuple negativeTuple3({X,Z,V},&_b,true);
                const Tuple* tuple3 = ub.find(Tuple({X,Z,V},&_b));
                bool undef3 = false;
                if(tuple3!=NULL){
                    undef3 = true;
                }else if(wb.find(negativeTuple3)==NULL){
                    tuple3=&negativeTuple3;
                }
                if(tuple3!=NULL){
                    if((*tuple3)[0]!=(*tuple0)[0] || (*tuple3)[1]!=(*tuple0)[1] || (*tuple3)[2]!=(*tuple0)[2]){
                        Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==1){
        int X = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_.getValues({X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuples.back());
                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_.getValues({X});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesN.back());
                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            int Z = tuple0->at(0);
            int V = tuple0->at(1);
            int U = tuple0->at(2);
            const std::vector<const Tuple*>& tuples1 = pa_.getValues({});
            const std::vector<const Tuple*>& tuplesU1 = ua_.getValues({});
            for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
                const Tuple* tuple1;
                bool undef1=false;
                if(i_1<tuples1.size())                    tuple1=tuples1[i_1];
                else{
                    tuple1=tuplesU1[i_1-tuples1.size()];
                    undef1=true;
                }
                int Y = tuple1->at(0);
                const Tuple negativeTuple3({X,Z,V},&_b,true);
                const Tuple* tuple3 = ub.find(Tuple({X,Z,V},&_b));
                bool undef3 = false;
                if(tuple3!=NULL){
                    undef3 = true;
                }else if(wb.find(negativeTuple3)==NULL){
                    tuple3=&negativeTuple3;
                }
                if(tuple3!=NULL){
                    if((*tuple3)[0]!=(*tuple0)[0] || (*tuple3)[1]!=(*tuple0)[1] || (*tuple3)[2]!=(*tuple0)[2]){
                        Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
    }
    if(tuple.getPredicateName() == &_b && tuple.size()==3){
        int X = tuple[0];
        int Z = tuple[1];
        int V = tuple[2];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_.getValues({X,Z,V});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuples.back());
                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_.getValues({X,Z,V});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(*tuplesN.back());
                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                    {
                        std::vector<int> aggrKey({t[2]});
                        if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
        const std::vector<const Tuple*>& tuples0 = pb_0_1_.getValues({Z,V});
        const std::vector<const Tuple*>& tuplesU0 = ub_0_1_.getValues({Z,V});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            if((*tuple0)[0]!=tuple[0] || (*tuple0)[1]!=tuple[1] || (*tuple0)[2]!=tuple[2]){
                int U = tuple0->at(2);
                const std::vector<const Tuple*>& tuples1 = pa_.getValues({});
                const std::vector<const Tuple*>& tuplesU1 = ua_.getValues({});
                for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
                    const Tuple* tuple1;
                    bool undef1=false;
                    if(i_1<tuples1.size())                        tuple1=tuples1[i_1];
                    else{
                        tuple1=tuplesU1[i_1-tuples1.size()];
                        undef1=true;
                    }
                    int Y = tuple1->at(0);
                    const Tuple* tuple2 = wa.find(Tuple({X},&_a));
                    bool undef2 = false;
                    if(tuple2==NULL){
                        tuple2 = ua.find(Tuple({X},&_a));
                        undef2 = true;
                    }
                    if(tuple2!=NULL){
                        Tuple t({Z,V,U,Y,X,X,Z,V},&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                        {
                            std::vector<int> aggrKey({t[2]});
                            if(aggrKey[0]>=0){
                                if(ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        wb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = ub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
                                if(nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(Tuple(t))==NULL){
                                    if(nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.find(t))
                                        nwb_Z_V_U_a_Y_a_X_not_b_X_Z_V_.erase(t);
                                    const auto& insertResult = nub_Z_V_U_a_Y_a_X_not_b_X_Z_V_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({aggrKey}).size()<=0){
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
    predicateFSetMap[&_b]=&fb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_b]=&wb;
    predicateFSetMap[&_b]=&fb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_b]=&wb;
    predicateFSetMap[&_b]=&fb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_b]=&wb;
    predicateFSetMap[&_b]=&fb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_);
    predicateToAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&p_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_1_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_1_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&np_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_);
    predicateToUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_1_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_1_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_0_1_2_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_3_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_4_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_].push_back(&nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_5_6_7_2_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_0_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_1_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_1_2_);
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
                int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                //1
                if(!(undefPlusTrue>=1+maxPossibleNegativeSum[0][{}])){
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::cout<<"propagation started from Aggr"<<std::endl;
                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                        propagatedLiterals.push_back(-1);
                    }else{
                        const auto & it = tupleToVar.find(*tupleU);
                        if(it != tupleToVar.end()) {
                            int sign = tupleUNegated ? -1 : 1;
                            propagatedLiterals.push_back(it->second*sign);
                        }
                    }
                }//close aggr true if
                else{
                    bool propagated=false;
                    tupleU=NULL;
                    if(tupleU == NULL){
                        for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                            if(undefPlusTrue-undefKey->at(0)>=1+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues(*undefKey);
                                if(undefinedTuples->size()==1){

                                    const Tuple* tuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                    if(tuple0!=NULL){
                                        const auto & it0 = tupleToVar.find(*tuple0);
                                        if(it0 != tupleToVar.end()) {
                                            propagated=true;
                                            int sign = -1;
                                            propagatedLiterals.push_back(it0->second*sign);
                                        }
                                    }
                                    const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(3)},&_a));
                                    if(tuple1!=NULL){
                                        const auto & it1 = tupleToVar.find(*tuple1);
                                        if(it1 != tupleToVar.end()) {
                                            propagated=true;
                                            int sign = -1;
                                            propagatedLiterals.push_back(it1->second*sign);
                                        }
                                    }
                                    const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4)},&_a));
                                    if(tuple2!=NULL){
                                        const auto & it2 = tupleToVar.find(*tuple2);
                                        if(it2 != tupleToVar.end()) {
                                            propagated=true;
                                            int sign = -1;
                                            propagatedLiterals.push_back(it2->second*sign);
                                        }
                                    }
                                    const Tuple* tuple3 = ub.find(Tuple({undefinedTuples->at(0)->at(5),undefinedTuples->at(0)->at(6),undefinedTuples->at(0)->at(7)},&_b));
                                    if(tuple3!=NULL){
                                        const auto & it3 = tupleToVar.find(*tuple3);
                                        if(it3 != tupleToVar.end()) {
                                            propagated=true;
                                            int sign = 1;
                                            propagatedLiterals.push_back(it3->second*sign);
                                        }
                                    }
                                }
                            }
                        }
                        for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                            if(undefPlusTrue+undefKey->at(0)>=1+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                    bool negativeJoinPropagated=false;
                                    const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b));
                                    if(tupleU0!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple1 ({undefinedTuples->at(iUndef)->at(3)},&_a);
                                        if((wa.find(tuple1)!=NULL) ){
                                            const auto & it1 = tupleToVar.find(tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                reas.push_back(it1->second);
                                            }
                                            Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_a);
                                            if((wa.find(tuple2)!=NULL) ){
                                                const auto & it2 = tupleToVar.find(tuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    reas.push_back(it2->second);
                                                }
                                                Tuple tuple3 ({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b);
                                                if((wb.find(tuple3)==NULL && ub.find(tuple3)==NULL) ){
                                                    const auto & it3 = tupleToVar.find(tuple3);
                                                    if(it3 != tupleToVar.end()) {
                                                        reas.push_back(it3->second*-1);
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
                                    }
                                    const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                    if(tupleU1!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b);
                                        if((wb.find(tuple0)!=NULL) ){
                                            const auto & it0 = tupleToVar.find(tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_a);
                                            if((wa.find(tuple2)!=NULL)  || *tupleU1==tuple2){
                                                if(*tupleU1!=tuple2){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                }
                                                Tuple tuple3 ({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b);
                                                if((wb.find(tuple3)==NULL && ub.find(tuple3)==NULL) ){
                                                    const auto & it3 = tupleToVar.find(tuple3);
                                                    if(it3 != tupleToVar.end()) {
                                                        reas.push_back(it3->second*-1);
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
                                    }
                                    const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                    if(tupleU2!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b);
                                        if((wb.find(tuple0)!=NULL) ){
                                            const auto & it0 = tupleToVar.find(tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if((wa.find(tuple1)!=NULL)  || *tupleU2==tuple1){
                                                if(*tupleU2!=tuple1){
                                                    const auto & it1 = tupleToVar.find(tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second);
                                                    }
                                                }
                                                Tuple tuple3 ({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b);
                                                if((wb.find(tuple3)==NULL && ub.find(tuple3)==NULL) ){
                                                    const auto & it3 = tupleToVar.find(tuple3);
                                                    if(it3 != tupleToVar.end()) {
                                                        reas.push_back(it3->second*-1);
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
                                    const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b));
                                    if(tupleU3!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b);
                                        if((wb.find(tuple0)!=NULL) ){
                                            const auto & it0 = tupleToVar.find(tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if((wa.find(tuple1)!=NULL) ){
                                                const auto & it1 = tupleToVar.find(tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_a);
                                                if((wa.find(tuple2)!=NULL) ){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                    const auto & it3 = tupleToVar.find(*tupleU3);
                                                    if(it3 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.push_back(it3->second*sign);
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
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            {
                if(actualSum[0][{}]+actualNegativeSum[0][{}]>=1+1+maxPossibleNegativeSum[0][{}]){
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::cout<<"propagation started from Aggr"<<std::endl;
                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                        propagatedLiterals.push_back(-1);
                    }else{
                        const auto & it = tupleToVar.find(*tupleU);
                        if(it != tupleToVar.end()) {
                            int sign = tupleUNegated ? -1 : 1;
                            propagatedLiterals.push_back(it->second*sign);
                        }
                    }
                }//close aggr true if
                else{
                    bool propagated=false;
                    tupleU=NULL;
                    if(tupleU == NULL){
                        for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                            if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 1+1+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                    bool found=false;
                                    if(!found){
                                        const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple1 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        const Tuple* tuple3 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple negativeTuple3 ({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b,true);
                                        if(aggrTupleU0!=NULL && tuple1!=NULL && tuple2!=NULL && (tuple3==NULL && tupleU3==NULL)){
                                            const auto & it = tupleToVar.find(*aggrTupleU0);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                found=true;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                    if(!found){
                                        const Tuple* aggrTupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        const Tuple* tuple3 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple negativeTuple3 ({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b,true);
                                        if(aggrTupleU1!=NULL && tuple0!=NULL && (tuple2!=NULL || tupleU2==aggrTupleU1)&& (tuple3==NULL && tupleU3==NULL)){
                                            const auto & it = tupleToVar.find(*aggrTupleU1);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                found=true;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                    if(!found){
                                        const Tuple* aggrTupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple1 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tuple3 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple negativeTuple3 ({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b,true);
                                        if(aggrTupleU2!=NULL && tuple0!=NULL && (tuple1!=NULL || tupleU1==aggrTupleU2)&& (tuple3==NULL && tupleU3==NULL)){
                                            const auto & it = tupleToVar.find(*aggrTupleU2);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                found=true;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                    if(!found){
                                        const Tuple* aggrTupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                        const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple1 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        if(aggrTupleU3!=NULL && tuple0!=NULL && tuple1!=NULL && tuple2!=NULL ){
                                            const auto & it = tupleToVar.find(*aggrTupleU3);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                found=true;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                            if(actualSum[0][{}]+actualNegativeSum[0][{}]-undefKey->at(0) < 1+1+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({undefKey->at(0)});
                                if(undefinedTuples->size()==1){
                                    {
                                        Tuple tuple0 ({undefinedTuples->at(0)->at(0), undefinedTuples->at(0)->at(1), undefinedTuples->at(0)->at(2)},&_b);
                                        if(ub.find(tuple0)!=NULL){
                                            const auto & it = tupleToVar.find(tuple0);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                    {
                                        Tuple tuple1 ({undefinedTuples->at(0)->at(3)},&_a);
                                        if(ua.find(tuple1)!=NULL){
                                            const auto & it = tupleToVar.find(tuple1);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                    {
                                        Tuple tuple2 ({undefinedTuples->at(0)->at(4)},&_a);
                                        if(ua.find(tuple2)!=NULL){
                                            const auto & it = tupleToVar.find(tuple2);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it->second*sign);
                                            }
                                        }
                                    }
                                    {
                                        Tuple tuple3 ({undefinedTuples->at(0)->at(5), undefinedTuples->at(0)->at(6), undefinedTuples->at(0)->at(7)},&_b);
                                        if(ub.find(tuple3)!=NULL){
                                            const auto & it = tupleToVar.find(tuple3);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                propagatedLiterals.push_back(it->second*sign);
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
            if(starter.getPredicateName()== &_b || starter.getPredicateName()== &_a || starter.getPredicateName()== &_a || starter.getPredicateName()== &_b){
                {
                    if(actualSum[0][{}]+actualNegativeSum[0][{}]>=1+1+maxPossibleNegativeSum[0][{}]){
                        tupleU=NULL;
                        std::vector<int> local_reason;
                        std::vector<int> aggregates_id({0});
                        std::vector<bool> aggregates_sign({true});
                        std::vector<int> bodyReason;
                        const auto & it = tupleToVar.find(Tuple(starter));
                        if(it!=tupleToVar.end()){
                            bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
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
                    }//close aggr true if
                    else{
                        bool propagated=false;
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int> local_reason;
                            std::vector<int> aggregates_id({0});
                            std::vector<bool> aggregates_sign({true});
                            std::vector<int> bodyReason;
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 1+1+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple1 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            const Tuple* tuple3 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple negativeTuple3 ({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b,true);
                                            if(aggrTupleU0!=NULL && tuple1!=NULL && tuple2!=NULL && (tuple3==NULL && tupleU3==NULL)){
                                                std::vector<int> propagationReason(bodyReason);
                                                if(tuple1!=NULL){
                                                    const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                    if(it_tuple1!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple1->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tuple2!=NULL){
                                                    const auto & it_tuple2 = tupleToVar.find(*tuple2);
                                                    if(it_tuple2!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple2->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tupleU3 == NULL){
                                                    const auto & it_negativeTuple3 = tupleToVar.find(negativeTuple3);
                                                    if(it_negativeTuple3!=tupleToVar.end()){
                                                        propagationReason.push_back(it_negativeTuple3->second * -1);
                                                    }//closing if
                                                }//closing if
                                                const auto & it = tupleToVar.find(*aggrTupleU0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,propagationReason,{});
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            const Tuple* tuple3 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple negativeTuple3 ({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b,true);
                                            if(aggrTupleU1!=NULL && tuple0!=NULL && (tuple2!=NULL || tupleU2==aggrTupleU1)&& (tuple3==NULL && tupleU3==NULL)){
                                                std::vector<int> propagationReason(bodyReason);
                                                if(tuple0!=NULL){
                                                    const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                    if(it_tuple0!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple0->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tuple2!=NULL){
                                                    const auto & it_tuple2 = tupleToVar.find(*tuple2);
                                                    if(it_tuple2!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple2->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tupleU3 == NULL){
                                                    const auto & it_negativeTuple3 = tupleToVar.find(negativeTuple3);
                                                    if(it_negativeTuple3!=tupleToVar.end()){
                                                        propagationReason.push_back(it_negativeTuple3->second * -1);
                                                    }//closing if
                                                }//closing if
                                                const auto & it = tupleToVar.find(*aggrTupleU1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,propagationReason,{});
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple1 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tuple3 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple negativeTuple3 ({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b,true);
                                            if(aggrTupleU2!=NULL && tuple0!=NULL && (tuple1!=NULL || tupleU1==aggrTupleU2)&& (tuple3==NULL && tupleU3==NULL)){
                                                std::vector<int> propagationReason(bodyReason);
                                                if(tuple0!=NULL){
                                                    const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                    if(it_tuple0!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple0->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tuple1!=NULL){
                                                    const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                    if(it_tuple1!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple1->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tupleU3 == NULL){
                                                    const auto & it_negativeTuple3 = tupleToVar.find(negativeTuple3);
                                                    if(it_negativeTuple3!=tupleToVar.end()){
                                                        propagationReason.push_back(it_negativeTuple3->second * -1);
                                                    }//closing if
                                                }//closing if
                                                const auto & it = tupleToVar.find(*aggrTupleU2);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,propagationReason,{});
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5), undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_b));
                                            const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple1 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                            const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                            if(aggrTupleU3!=NULL && tuple0!=NULL && tuple1!=NULL && tuple2!=NULL ){
                                                std::vector<int> propagationReason(bodyReason);
                                                if(tuple0!=NULL){
                                                    const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                    if(it_tuple0!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple0->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tuple1!=NULL){
                                                    const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                    if(it_tuple1!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple1->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tuple2!=NULL){
                                                    const auto & it_tuple2 = tupleToVar.find(*tuple2);
                                                    if(it_tuple2!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple2->second * 1);
                                                    }//closing if
                                                }//closing if
                                                const auto & it = tupleToVar.find(*aggrTupleU3);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    found=true;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,propagationReason,{});
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                if(actualSum[0][{}]+actualNegativeSum[0][{}]-undefKey->at(0) < 1+1+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({undefKey->at(0)});
                                    if(undefinedTuples->size()==1){
                                        {
                                            Tuple tuple0 ({undefinedTuples->at(0)->at(0), undefinedTuples->at(0)->at(1), undefinedTuples->at(0)->at(2)},&_b);
                                            if(ub.find(tuple0)!=NULL){
                                                const auto & it = tupleToVar.find(tuple0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple1 ({undefinedTuples->at(0)->at(3)},&_a);
                                            if(ua.find(tuple1)!=NULL){
                                                const auto & it = tupleToVar.find(tuple1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple2 ({undefinedTuples->at(0)->at(4)},&_a);
                                            if(ua.find(tuple2)!=NULL){
                                                const auto & it = tupleToVar.find(tuple2);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple3 ({undefinedTuples->at(0)->at(5), undefinedTuples->at(0)->at(6), undefinedTuples->at(0)->at(7)},&_b);
                                            if(ub.find(tuple3)!=NULL){
                                                const auto & it = tupleToVar.find(tuple3);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    propagatedLiterals.push_back(it->second*sign);
                                                    reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
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
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_b || starter.getPredicateName()== &_a || starter.getPredicateName()== &_a || starter.getPredicateName()== &_b){
                {
                    int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                    //1
                    if(!(undefPlusTrue>=1+maxPossibleNegativeSum[0][{}])){
                        tupleU=NULL;
                        std::vector<int> local_reason;
                        std::vector<int> aggregates_id({0});
                        std::vector<bool> aggregates_sign({false});
                        std::vector<int> bodyReason;
                        const auto & it = tupleToVar.find(Tuple(starter));
                        if(it!=tupleToVar.end()){
                            bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
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
                    }//close aggr true if
                    else{
                        bool propagated=false;
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int> local_reason;
                            std::vector<int> aggregates_id({0});
                            std::vector<bool> aggregates_sign({false});
                            std::vector<int> bodyReason;
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                if(undefPlusTrue-undefKey->at(0)>=1+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues(*undefKey);
                                    if(undefinedTuples->size()==1){

                                        const Tuple* tuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                        if(tuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it0->second*sign);
                                                reasonMapping.addPropagation(it0->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                            }
                                        }
                                        const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(3)},&_a));
                                        if(tuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it1->second*sign);
                                                reasonMapping.addPropagation(it1->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                            }
                                        }
                                        const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(4)},&_a));
                                        if(tuple2!=NULL){
                                            const auto & it2 = tupleToVar.find(*tuple2);
                                            if(it2 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.push_back(it2->second*sign);
                                                reasonMapping.addPropagation(it2->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                            }
                                        }
                                        const Tuple* tuple3 = ub.find(Tuple({undefinedTuples->at(0)->at(5),undefinedTuples->at(0)->at(6),undefinedTuples->at(0)->at(7)},&_b));
                                        if(tuple3!=NULL){
                                            const auto & it3 = tupleToVar.find(*tuple3);
                                            if(it3 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                propagatedLiterals.push_back(it3->second*sign);
                                                reasonMapping.addPropagation(it3->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
                                            }
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                if(undefPlusTrue+undefKey->at(0)>=1+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_Z_V_U_a_Y_a_X_not_b_X_Z_V_2_.getValues({undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b));
                                        if(tupleU0!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if((wa.find(tuple1)!=NULL) ){
                                                const auto & it1 = tupleToVar.find(tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_a);
                                                if((wa.find(tuple2)!=NULL) ){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                    Tuple tuple3 ({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b);
                                                    if((wb.find(tuple3)==NULL && ub.find(tuple3)==NULL) ){
                                                        const auto & it3 = tupleToVar.find(tuple3);
                                                        if(it3 != tupleToVar.end()) {
                                                            reas.push_back(it3->second*-1);
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
                                        }
                                        const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(3)},&_a));
                                        if(tupleU1!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b);
                                            if((wb.find(tuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_a);
                                                if((wa.find(tuple2)!=NULL)  || *tupleU1==tuple2){
                                                    if(*tupleU1!=tuple2){
                                                        const auto & it2 = tupleToVar.find(tuple2);
                                                        if(it2 != tupleToVar.end()) {
                                                            reas.push_back(it2->second);
                                                        }
                                                    }
                                                    Tuple tuple3 ({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b);
                                                    if((wb.find(tuple3)==NULL && ub.find(tuple3)==NULL) ){
                                                        const auto & it3 = tupleToVar.find(tuple3);
                                                        if(it3 != tupleToVar.end()) {
                                                            reas.push_back(it3->second*-1);
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
                                        }
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_a));
                                        if(tupleU2!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b);
                                            if((wb.find(tuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple1 ({undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if((wa.find(tuple1)!=NULL)  || *tupleU2==tuple1){
                                                    if(*tupleU2!=tuple1){
                                                        const auto & it1 = tupleToVar.find(tuple1);
                                                        if(it1 != tupleToVar.end()) {
                                                            reas.push_back(it1->second);
                                                        }
                                                    }
                                                    Tuple tuple3 ({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b);
                                                    if((wb.find(tuple3)==NULL && ub.find(tuple3)==NULL) ){
                                                        const auto & it3 = tupleToVar.find(tuple3);
                                                        if(it3 != tupleToVar.end()) {
                                                            reas.push_back(it3->second*-1);
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
                                        const Tuple* tupleU3 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6),undefinedTuples->at(iUndef)->at(7)},&_b));
                                        if(tupleU3!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1),undefinedTuples->at(iUndef)->at(2)},&_b);
                                            if((wb.find(tuple0)!=NULL) ){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple1 ({undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if((wa.find(tuple1)!=NULL) ){
                                                    const auto & it1 = tupleToVar.find(tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second);
                                                    }
                                                    Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_a);
                                                    if((wa.find(tuple2)!=NULL) ){
                                                        const auto & it2 = tupleToVar.find(tuple2);
                                                        if(it2 != tupleToVar.end()) {
                                                            reas.push_back(it2->second);
                                                        }
                                                        const auto & it3 = tupleToVar.find(*tupleU3);
                                                        if(it3 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = -1;
                                                            propagatedLiterals.push_back(it3->second*sign);
                                                            for(int v: reas){ bodyReason.push_back(v); }
                                                            reasonMapping.addPropagation(it3->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{});
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
                    }//close can prop if
                }
            }
        }//local scope
    }
}
}
