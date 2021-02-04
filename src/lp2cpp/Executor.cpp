#include "Executor.h"

#include "utils/ConstantsManager.h"

#include "DLV2libs/input/InputDirector.h"

#include "parsing/AspCore2InstanceBuilder.h"

#include "datastructures/PredicateSet.h"

#include "datastructures/ReasonTable.h"

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
PredicateWSet wa(2);
PredicateWSet ua(2);
PredicateWSet fa(2);
const std::string _b = "b";
PredicateWSet wb(3);
PredicateWSet ub(3);
PredicateWSet fb(3);
const std::string _b_Z_X_Y_b_V_U_V_not_a_V_X_ = "b_Z_X_Y_b_V_U_V_not_a_V_X_";
PredicateWSet wb_Z_X_Y_b_V_U_V_not_a_V_X_(8);
PredicateWSet ub_Z_X_Y_b_V_U_V_not_a_V_X_(8);
PredicateWSet nwb_Z_X_Y_b_V_U_V_not_a_V_X_(8);
PredicateWSet nub_Z_X_Y_b_V_U_V_not_a_V_X_(8);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_0;
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
AuxMap pa_0_1_({0,1});
AuxMap ua_0_1_({0,1});
AuxMap fa_0_1_({0,1});
AuxMap pa_({});
AuxMap ua_({});
AuxMap fa_({});
AuxMap pb_1_({1});
AuxMap ub_1_({1});
AuxMap fb_1_({1});
AuxMap pb_0_2_({0,2});
AuxMap ub_0_2_({0,2});
AuxMap fb_0_2_({0,2});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_({3});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_({3});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_({3});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_({3});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_({});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_({});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_({});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_({});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_({0,1,2});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_({0,1,2});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_({0,1,2});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_({0,1,2});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_({3,4,5});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_({3,4,5});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_({3,4,5});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_({3,4,5});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_({6,7});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_({6,7});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_({6,7});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_({6,7});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_({0,1,2,3});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_({0,1,2,3});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_({0,1,2,3});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_({0,1,2,3});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_({3,4,5,3});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_({3,4,5,3});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_({3,4,5,3});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_({3,4,5,3});
AuxMap p_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_({6,7,3});
AuxMap u_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_({6,7,3});
AuxMap np_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_({6,7,3});
AuxMap nu_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_({6,7,3});
//printing aux maps needed for reasons of negative literals;
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
    if(var<0 && ( tuple.getPredicateName() == &_a || tuple.getPredicateName() == &_b)){
        std::unordered_map<const std::string*, PredicateWSet*>::iterator it_false = predicateFSetMap.find(tuple.getPredicateName());
        if (it_false == predicateFSetMap.end()) {
            } else {
            const auto& insertResult = it_false->second->insert(Tuple(tuple));
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[it_false->first]) {
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
        int X = tuple[1];
        int Y = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>* tuples1 = &pb_.getValues({});
            for(int i_1=0;i_1<tuples1->size();i_1++){
                const Tuple* tuple1=tuples1->at(i_1);
                if(tuple1->at(0) == tuple1->at(2)){
                    int V = tuple1->at(0);
                    int U = tuple1->at(1);
                    const Tuple negativeTuple2({V,X},&_a,true);
                    const Tuple* tuple2 = ua.find(Tuple({V,X},&_a));
                    if(wa.find(negativeTuple2)==NULL && tuple2==NULL){
                        tuple2=&negativeTuple2;
                        Tuple t({Z,X,Y,V,U,V,V,X},&_b_Z_X_Y_b_V_U_V_not_a_V_X_);
                        {
                            std::vector<int> aggrKey({t[3]});
                            if(aggrKey[0]>=0){
                                if(wb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t)==NULL){
                                    if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                        ub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                    const auto& insertResult = wb_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
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
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                            }else{
                                if(nwb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t)==NULL){
                                    if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                        nub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                    const auto& insertResult = nwb_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
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
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_.getValues({Z,X,Y});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[3]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_.getValues({Z,X,Y});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[3]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
        if(tuple.at(0) == tuple.at(2)){
            int V = tuple[0];
            int U = tuple[1];
            if(var > 0){
                const std::vector<const Tuple*>* tuples0 = &pb_.getValues({});
                for(int i_0=0;i_0<tuples0->size();i_0++){
                    const Tuple* tuple0=tuples0->at(i_0);
                    int Z = tuple0->at(0);
                    int X = tuple0->at(1);
                    int Y = tuple0->at(2);
                    const Tuple negativeTuple2({V,X},&_a,true);
                    const Tuple* tuple2 = ua.find(Tuple({V,X},&_a));
                    if(wa.find(negativeTuple2)==NULL && tuple2==NULL){
                        tuple2=&negativeTuple2;
                        Tuple t({Z,X,Y,V,U,V,V,X},&_b_Z_X_Y_b_V_U_V_not_a_V_X_);
                        {
                            std::vector<int> aggrKey({t[3]});
                            if(aggrKey[0]>=0){
                                if(wb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t)==NULL){
                                    if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                        ub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                    const auto& insertResult = wb_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
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
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                            }else{
                                if(nwb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t)==NULL){
                                    if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                        nub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                    const auto& insertResult = nwb_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
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
                                            reas.insert(it->second*-1);
                                        }
                                    }
                                    possibleNegativeSum[0][{}]+=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }else{
                const std::vector<const Tuple*>& tuplesU = u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_.getValues({V,U,V});
                while(!tuplesU.empty()){
                    Tuple t(*tuplesU.back());
                    ub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesU.back());
                    {
                        std::vector<int> aggrKey({t[3]});
                        auto& undefSet = undefAggrVars[0][{}];
                        if(u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
                const std::vector<const Tuple*>& tuplesNU = nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_.getValues({V,U,V});
                while(!tuplesNU.empty()){
                    Tuple t(*tuplesNU.back());
                    nub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesNU.back());
                    {
                        std::vector<int> aggrKey({t[3]});
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        if(nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
                            if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_a){
        int V = tuple[0];
        int X = tuple[1];
        if(var < 0){
            const std::vector<const Tuple*>* tuples0 = &pb_1_.getValues({X});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int Z = tuple0->at(0);
                int Y = tuple0->at(2);
                const std::vector<const Tuple*>* tuples1 = &pb_0_2_.getValues({V,V});
                for(int i_1=0;i_1<tuples1->size();i_1++){
                    const Tuple* tuple1=tuples1->at(i_1);
                    if(tuple1->at(0) == tuple1->at(2)){
                        int U = tuple1->at(1);
                        Tuple t({Z,X,Y,V,U,V,V,X},&_b_Z_X_Y_b_V_U_V_not_a_V_X_);
                        {
                            std::vector<int> aggrKey({t[3]});
                            if(aggrKey[0]>=0){
                                if(wb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t)==NULL){
                                    if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                        ub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                    const auto& insertResult = wb_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
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
                                if(nwb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t)==NULL){
                                    if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                        nub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                    const auto& insertResult = nwb_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
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
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_.getValues({V,X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[3]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesNU = nu_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_.getValues({V,X});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nub_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[3]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
                        if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
    if (var > 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple.getPredicateName());
        if (wSetIt != predicateWSetMap.end()) {
            wSetIt->second->erase(tuple);
        }
    }
    if(var<0 && ( tuple.getPredicateName() == &_a || tuple.getPredicateName() == &_b)){
        std::unordered_map<const std::string*, PredicateWSet*>::iterator falseSetIt = predicateFSetMap.find(tuple.getPredicateName());
        if (falseSetIt != predicateFSetMap.end()) {
            falseSetIt->second->erase(tuple);
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
        int X = tuple[1];
        int Y = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_.getValues({Z,X,Y});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuples.back());
                if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[3]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_.getValues({Z,X,Y});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesN.back());
                if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[3]});
                        if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
        const std::vector<const Tuple*>& tuples1 = pb_.getValues({});
        const std::vector<const Tuple*>& tuplesU1 = ub_.getValues({});
        for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
            const Tuple* tuple1;
            bool undef1=false;
            if(i_1<tuples1.size())                tuple1=tuples1[i_1];
            else{
                tuple1=tuplesU1[i_1-tuples1.size()];
                undef1=true;
            }
            if(tuple1->at(0) == tuple1->at(2)){
                int V = tuple1->at(0);
                int U = tuple1->at(1);
                const Tuple negativeTuple2({V,X},&_a,true);
                const Tuple* tuple2 = ua.find(Tuple({V,X},&_a));
                bool undef2 = false;
                if(tuple2!=NULL){
                    undef2 = true;
                }else if(wa.find(negativeTuple2)==NULL){
                    tuple2=&negativeTuple2;
                }
                if(tuple2!=NULL){
                    Tuple t({Z,X,Y,V,U,V,V,X},&_b_Z_X_Y_b_V_U_V_not_a_V_X_);
                    {
                        std::vector<int> aggrKey({t[3]});
                        if(aggrKey[0]>=0){
                            if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t))==NULL){
                                if(wb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                    wb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                const auto& insertResult = ub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
                            if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t))==NULL){
                                if(nwb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                    nwb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                const auto& insertResult = nub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_b && tuple.size()==3){
        if(tuple.at(0) == tuple.at(2)){
            int V = tuple[0];
            int U = tuple[1];
            if(var > 0){
                const std::vector<const Tuple*>& tuples = p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_.getValues({V,U,V});
                while(!tuples.empty()){
                    Tuple t(*tuples.back());
                    wb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuples.back());
                    if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t)) == NULL){
                        const auto& insertResult = ub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[3]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
                const std::vector<const Tuple*>& tuplesN = np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_.getValues({V,U,V});
                while(!tuplesN.empty()){
                    Tuple t(*tuplesN.back());
                    nwb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesN.back());
                    if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t)) == NULL){
                        const auto& insertResult = nub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[3]});
                            if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
                if(i_0<tuples0.size())                    tuple0=tuples0[i_0];
                else{
                    tuple0=tuplesU0[i_0-tuples0.size()];
                    undef0=true;
                }
                int Z = tuple0->at(0);
                int X = tuple0->at(1);
                int Y = tuple0->at(2);
                const Tuple negativeTuple2({V,X},&_a,true);
                const Tuple* tuple2 = ua.find(Tuple({V,X},&_a));
                bool undef2 = false;
                if(tuple2!=NULL){
                    undef2 = true;
                }else if(wa.find(negativeTuple2)==NULL){
                    tuple2=&negativeTuple2;
                }
                if(tuple2!=NULL){
                    Tuple t({Z,X,Y,V,U,V,V,X},&_b_Z_X_Y_b_V_U_V_not_a_V_X_);
                    {
                        std::vector<int> aggrKey({t[3]});
                        if(aggrKey[0]>=0){
                            if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t))==NULL){
                                if(wb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                    wb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                const auto& insertResult = ub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
                            if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t))==NULL){
                                if(nwb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                    nwb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                const auto& insertResult = nub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int V = tuple[0];
        int X = tuple[1];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_.getValues({V,X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuples.back());
                if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[3]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_.getValues({V,X});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(*tuplesN.back());
                if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[3]});
                        if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
        const std::vector<const Tuple*>& tuples0 = pb_1_.getValues({X});
        const std::vector<const Tuple*>& tuplesU0 = ub_1_.getValues({X});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int Z = tuple0->at(0);
            int Y = tuple0->at(2);
            const std::vector<const Tuple*>& tuples1 = pb_0_2_.getValues({V,V});
            const std::vector<const Tuple*>& tuplesU1 = ub_0_2_.getValues({V,V});
            for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
                const Tuple* tuple1;
                bool undef1=false;
                if(i_1<tuples1.size())                    tuple1=tuples1[i_1];
                else{
                    tuple1=tuplesU1[i_1-tuples1.size()];
                    undef1=true;
                }
                if(tuple1->at(0) == tuple1->at(2)){
                    int U = tuple1->at(1);
                    Tuple t({Z,X,Y,V,U,V,V,X},&_b_Z_X_Y_b_V_U_V_not_a_V_X_);
                    {
                        std::vector<int> aggrKey({t[3]});
                        if(aggrKey[0]>=0){
                            if(ub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t))==NULL){
                                if(wb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                    wb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                const auto& insertResult = ub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
                            if(nub_Z_X_Y_b_V_U_V_not_a_V_X_.find(Tuple(t))==NULL){
                                if(nwb_Z_X_Y_b_V_U_V_not_a_V_X_.find(t))
                                    nwb_Z_X_Y_b_V_U_V_not_a_V_X_.erase(t);
                                const auto& insertResult = nub_Z_X_Y_b_V_U_V_not_a_V_X_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({aggrKey}).size()<=0){
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
    createFunctionsMap();
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
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_);
    predicateToAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&p_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_1_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_1_2_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_2_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_1_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_);
    predicateToNegativeAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&np_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_);
    predicateToUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&u_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_1_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_2_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_0_1_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_4_5_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_Z_X_Y_b_V_U_V_not_a_V_X_].push_back(&nu_b_Z_X_Y_b_V_U_V_not_a_V_X_6_7_3_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_0_1_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_1_2_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_2_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_1_);
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
                if(actualSum[0][{}]+actualNegativeSum[0][{}]>=4+1+maxPossibleNegativeSum[0][{}]){
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::cout<<"propagation started from Aggr"<<std::endl;
                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                        propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});
                    }else{
                        const auto & it = tupleToVar.find(*tupleU);
                        if(it != tupleToVar.end()) {
                            int sign = tupleUNegated ? -1 : 1;
                            std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                            propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                        }
                    }
                }//close aggr true if
                else{
                    bool propagated=false;
                    tupleU=NULL;
                    if(tupleU == NULL){
                        for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                            if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 4+1+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({undefKey->at(0)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                    bool found=false;
                                    if(!found){
                                        const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple1 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                        const Tuple* tupleU1 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                        const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                        const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a,true);
                                        if(aggrTupleU0!=NULL && (tuple1!=NULL || tupleU1==aggrTupleU0)&& (tuple2==NULL && tupleU2==NULL)){
                                            const auto & it = tupleToVar.find(*aggrTupleU0);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                std::cout<<"Propagation positive 0 ";aggrTupleU0->print();std::cout<<std::endl;
                                                found=true;
                                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                    }
                                    if(!found){
                                        const Tuple* aggrTupleU1 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                        const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                        const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a,true);
                                        if(aggrTupleU1!=NULL && (tuple0!=NULL || tupleU0==aggrTupleU1)&& (tuple2==NULL && tupleU2==NULL)){
                                            const auto & it = tupleToVar.find(*aggrTupleU1);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                std::cout<<"Propagation positive 0 ";aggrTupleU1->print();std::cout<<std::endl;
                                                found=true;
                                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                    }
                                    if(!found){
                                        const Tuple* aggrTupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                        const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                        const Tuple* tuple1 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                        const Tuple* tupleU1 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                        if(aggrTupleU2!=NULL && tuple0!=NULL && tuple1!=NULL ){
                                            const auto & it = tupleToVar.find(*aggrTupleU2);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                std::cout<<"Propagation positive 0 ";aggrTupleU2->print();std::cout<<std::endl;
                                                found=true;
                                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                            if(actualSum[0][{}]+actualNegativeSum[0][{}]-undefKey->at(0) < 4+1+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({undefKey->at(0)});
                                if(undefinedTuples->size()==1){
                                    {
                                        Tuple tuple0 ({undefinedTuples->at(0)->at(0), undefinedTuples->at(0)->at(1), undefinedTuples->at(0)->at(2)},&_b);
                                        if(ub.find(tuple0)!=NULL){
                                            const auto & it = tupleToVar.find(tuple0);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                std::cout<<"Propagation positive negative join0 ";tuple0.print();std::cout<<std::endl;
                                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                    }
                                    {
                                        Tuple tuple1 ({undefinedTuples->at(0)->at(3), undefinedTuples->at(0)->at(4), undefinedTuples->at(0)->at(5)},&_b);
                                        if(ub.find(tuple1)!=NULL){
                                            const auto & it = tupleToVar.find(tuple1);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                std::cout<<"Propagation positive negative join0 ";tuple1.print();std::cout<<std::endl;
                                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                    }
                                    {
                                        Tuple tuple2 ({undefinedTuples->at(0)->at(6), undefinedTuples->at(0)->at(7)},&_a);
                                        if(ua.find(tuple2)!=NULL){
                                            const auto & it = tupleToVar.find(tuple2);
                                            if(it != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                std::cout<<"Propagation positive negative join0 ";tuple2.print();std::cout<<std::endl;
                                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
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
            if(starter.getPredicateName()== &_b || starter.getPredicateName()== &_b || starter.getPredicateName()== &_a){
                {
                    if(actualSum[0][{}]+actualNegativeSum[0][{}]>=4+1+maxPossibleNegativeSum[0][{}]){
                        tupleU=NULL;
                        std::vector<int> local_reason;
                        local_reason.insert(local_reason.end(),positiveAggrReason[0][{}].begin(), positiveAggrReason[0][{}].end());
                        const auto & it = tupleToVar.find(Tuple(starter));
                        if(it!=tupleToVar.end()){
                            local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                        }
                        if(tupleU == NULL){
                            std::cout<<"propagation started from Aggr"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                        }else{
                            const auto & it = tupleToVar.find(*tupleU);
                            if(it != tupleToVar.end()) {
                                int sign = tupleUNegated ? -1 : 1;
                                std::cout<<"External propagation "<<sign;tupleU->print();std::cout<<std::endl;
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                            }
                        }
                    }//close aggr true if
                    else{
                        bool propagated=false;
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),positiveAggrReason[0][{}].begin(), positiveAggrReason[0][{}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 4+1+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple1 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                            const Tuple* tupleU1 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                            const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                            const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a,true);
                                            if(aggrTupleU0!=NULL && (tuple1!=NULL || tupleU1==aggrTupleU0)&& (tuple2==NULL && tupleU2==NULL)){
                                                std::vector<int> propagationReason(local_reason);
                                                if(tuple1!=NULL){
                                                    const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                    if(it_tuple1!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple1->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tupleU2 == NULL){
                                                    const auto & it_negativeTuple2 = tupleToVar.find(negativeTuple2);
                                                    if(it_negativeTuple2!=tupleToVar.end()){
                                                        propagationReason.push_back(it_negativeTuple2->second * -1);
                                                    }//closing if
                                                }//closing if
                                                const auto & it = tupleToVar.find(*aggrTupleU0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    for(int v : propagationReason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                    std::cout<<"Propagation positive 0 ";aggrTupleU0->print();std::cout<<std::endl;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU1 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                            const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple2 = wa.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                            const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a,true);
                                            if(aggrTupleU1!=NULL && (tuple0!=NULL || tupleU0==aggrTupleU1)&& (tuple2==NULL && tupleU2==NULL)){
                                                std::vector<int> propagationReason(local_reason);
                                                if(tuple0!=NULL){
                                                    const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                    if(it_tuple0!=tupleToVar.end()){
                                                        propagationReason.push_back(it_tuple0->second * 1);
                                                    }//closing if
                                                }//closing if
                                                if(tupleU2 == NULL){
                                                    const auto & it_negativeTuple2 = tupleToVar.find(negativeTuple2);
                                                    if(it_negativeTuple2!=tupleToVar.end()){
                                                        propagationReason.push_back(it_negativeTuple2->second * -1);
                                                    }//closing if
                                                }//closing if
                                                const auto & it = tupleToVar.find(*aggrTupleU1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    for(int v : propagationReason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                    std::cout<<"Propagation positive 0 ";aggrTupleU1->print();std::cout<<std::endl;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU2 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(6), undefinedTuples->at(iUndef)->at(7)},&_a));
                                            const Tuple* tuple0 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2)},&_b));
                                            const Tuple* tuple1 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                            const Tuple* tupleU1 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(3), undefinedTuples->at(iUndef)->at(4), undefinedTuples->at(iUndef)->at(5)},&_b));
                                            if(aggrTupleU2!=NULL && tuple0!=NULL && tuple1!=NULL ){
                                                std::vector<int> propagationReason(local_reason);
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
                                                const auto & it = tupleToVar.find(*aggrTupleU2);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    for(int v : propagationReason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                    std::cout<<"Propagation positive 0 ";aggrTupleU2->print();std::cout<<std::endl;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                if(actualSum[0][{}]+actualNegativeSum[0][{}]-undefKey->at(0) < 4+1+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_Z_X_Y_b_V_U_V_not_a_V_X_3_.getValues({undefKey->at(0)});
                                    if(undefinedTuples->size()==1){
                                        {
                                            Tuple tuple0 ({undefinedTuples->at(0)->at(0), undefinedTuples->at(0)->at(1), undefinedTuples->at(0)->at(2)},&_b);
                                            if(ub.find(tuple0)!=NULL){
                                                std::vector<int> propagationReason(local_reason);
                                                const auto & it = tupleToVar.find(tuple0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    for(int v : propagationReason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                    std::cout<<"Propagation positive negative join0 ";tuple0.print();std::cout<<std::endl;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple1 ({undefinedTuples->at(0)->at(3), undefinedTuples->at(0)->at(4), undefinedTuples->at(0)->at(5)},&_b);
                                            if(ub.find(tuple1)!=NULL){
                                                std::vector<int> propagationReason(local_reason);
                                                const auto & it = tupleToVar.find(tuple1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    for(int v : propagationReason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                    std::cout<<"Propagation positive negative join0 ";tuple1.print();std::cout<<std::endl;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple2 ({undefinedTuples->at(0)->at(6), undefinedTuples->at(0)->at(7)},&_a);
                                            if(ua.find(tuple2)!=NULL){
                                                std::vector<int> propagationReason(local_reason);
                                                const auto & it = tupleToVar.find(tuple2);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    for(int v : propagationReason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                    std::cout<<"Propagation positive negative join0 ";tuple2.print();std::cout<<std::endl;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
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
