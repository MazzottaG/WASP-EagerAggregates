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
const std::string _robot = "robot";
PredicateWSet wrobot(1);
PredicateWSet urobot(1);
PredicateWSet frobot(1);
const std::string _step = "step";
PredicateWSet wstep(1);
PredicateWSet ustep(1);
PredicateWSet fstep(1);
const std::string _dim = "dim";
PredicateWSet wdim(1);
PredicateWSet udim(1);
PredicateWSet fdim(1);
const std::string _poss = "poss";
PredicateWSet wposs(4);
PredicateWSet uposs(4);
PredicateWSet fposs(4);
const std::string _poss_R_1_I_T_dim_I_ = "poss_R_1_I_T_dim_I_";
PredicateWSet wposs_R_1_I_T_dim_I_(5);
PredicateWSet uposs_R_1_I_T_dim_I_(5);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_2;
std::set<std::vector<int>> sharedVariables_1_ToAggregate_2;
const std::string _poss_R_n1I_T_dim_I_ = "poss_R_n1I_T_dim_I_";
PredicateWSet wposs_R_n1I_T_dim_I_(5);
PredicateWSet uposs_R_n1I_T_dim_I_(5);
std::set<std::vector<int>> sharedVariables_2_ToAggregate_2;
std::set<std::vector<int>> sharedVariables_3_ToAggregate_2;
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars[2];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars[2];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason[2];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason[2];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> actualSum[2];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleSum[2];
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
std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToFalseAuxiliaryMaps;
AuxMap pposs_0_1_2_3_({0,1,2,3});
AuxMap uposs_0_1_2_3_({0,1,2,3});
AuxMap fposs_0_1_2_3_({0,1,2,3});
AuxMap pposs_({});
AuxMap uposs_({});
AuxMap fposs_({});
AuxMap pdim_0_({0});
AuxMap udim_0_({0});
AuxMap fdim_0_({0});
AuxMap pdim_({});
AuxMap udim_({});
AuxMap fdim_({});
AuxMap pposs_1_2_({1,2});
AuxMap uposs_1_2_({1,2});
AuxMap fposs_1_2_({1,2});
AuxMap p_poss_R_1_I_T_dim_I_2_({2});
AuxMap u_poss_R_1_I_T_dim_I_2_({2});
AuxMap p_poss_R_1_I_T_dim_I_({});
AuxMap u_poss_R_1_I_T_dim_I_({});
AuxMap p_poss_R_1_I_T_dim_I_0_3_({0,3});
AuxMap u_poss_R_1_I_T_dim_I_0_3_({0,3});
AuxMap p_poss_R_1_I_T_dim_I_0_3_2_({0,3,2});
AuxMap u_poss_R_1_I_T_dim_I_0_3_2_({0,3,2});
AuxMap p_poss_R_1_I_T_dim_I_0_3_0_1_2_3_({0,3,0,1,2,3});
AuxMap u_poss_R_1_I_T_dim_I_0_3_0_1_2_3_({0,3,0,1,2,3});
AuxMap p_poss_R_1_I_T_dim_I_0_3_4_({0,3,4});
AuxMap u_poss_R_1_I_T_dim_I_0_3_4_({0,3,4});
AuxMap p_poss_R_1_I_T_dim_I_0_1_2_3_({0,1,2,3});
AuxMap u_poss_R_1_I_T_dim_I_0_1_2_3_({0,1,2,3});
AuxMap p_poss_R_1_I_T_dim_I_0_1_2_3_0_3_({0,1,2,3,0,3});
AuxMap u_poss_R_1_I_T_dim_I_0_1_2_3_0_3_({0,1,2,3,0,3});
AuxMap p_poss_R_1_I_T_dim_I_0_1_2_3_0_3_2_({0,1,2,3,0,3,2});
AuxMap u_poss_R_1_I_T_dim_I_0_1_2_3_0_3_2_({0,1,2,3,0,3,2});
AuxMap p_poss_R_1_I_T_dim_I_4_({4});
AuxMap u_poss_R_1_I_T_dim_I_4_({4});
AuxMap p_poss_R_1_I_T_dim_I_4_0_3_({4,0,3});
AuxMap u_poss_R_1_I_T_dim_I_4_0_3_({4,0,3});
AuxMap p_poss_R_1_I_T_dim_I_4_0_3_2_({4,0,3,2});
AuxMap u_poss_R_1_I_T_dim_I_4_0_3_2_({4,0,3,2});
AuxMap probot_0_({0});
AuxMap urobot_0_({0});
AuxMap pstep_0_({0});
AuxMap ustep_0_({0});
AuxMap pposs_0_1_3_({0,1,3});
AuxMap uposs_0_1_3_({0,1,3});
AuxMap fposs_0_1_3_({0,1,3});
AuxMap probot_({});
AuxMap urobot_({});
AuxMap pstep_({});
AuxMap ustep_({});
AuxMap p_poss_R_n1I_T_dim_I_2_({2});
AuxMap u_poss_R_n1I_T_dim_I_2_({2});
AuxMap p_poss_R_n1I_T_dim_I_({});
AuxMap u_poss_R_n1I_T_dim_I_({});
AuxMap p_poss_R_n1I_T_dim_I_0_3_({0,3});
AuxMap u_poss_R_n1I_T_dim_I_0_3_({0,3});
AuxMap p_poss_R_n1I_T_dim_I_0_3_2_({0,3,2});
AuxMap u_poss_R_n1I_T_dim_I_0_3_2_({0,3,2});
AuxMap p_poss_R_n1I_T_dim_I_0_3_0_1_2_3_({0,3,0,1,2,3});
AuxMap u_poss_R_n1I_T_dim_I_0_3_0_1_2_3_({0,3,0,1,2,3});
AuxMap p_poss_R_n1I_T_dim_I_0_3_4_({0,3,4});
AuxMap u_poss_R_n1I_T_dim_I_0_3_4_({0,3,4});
AuxMap p_poss_R_n1I_T_dim_I_0_1_2_3_({0,1,2,3});
AuxMap u_poss_R_n1I_T_dim_I_0_1_2_3_({0,1,2,3});
AuxMap p_poss_R_n1I_T_dim_I_0_1_2_3_0_3_({0,1,2,3,0,3});
AuxMap u_poss_R_n1I_T_dim_I_0_1_2_3_0_3_({0,1,2,3,0,3});
AuxMap p_poss_R_n1I_T_dim_I_0_1_2_3_0_3_2_({0,1,2,3,0,3,2});
AuxMap u_poss_R_n1I_T_dim_I_0_1_2_3_0_3_2_({0,1,2,3,0,3,2});
AuxMap p_poss_R_n1I_T_dim_I_4_({4});
AuxMap u_poss_R_n1I_T_dim_I_4_({4});
AuxMap p_poss_R_n1I_T_dim_I_4_0_3_({4,0,3});
AuxMap u_poss_R_n1I_T_dim_I_4_0_3_({4,0,3});
AuxMap p_poss_R_n1I_T_dim_I_4_0_3_2_({4,0,3,2});
AuxMap u_poss_R_n1I_T_dim_I_4_0_3_2_({4,0,3,2});
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
    if(var<0 && ( tuple.getPredicateName() == &_dim || tuple.getPredicateName() == &_poss)){
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
    if(tuple.getPredicateName() == &_poss){
        if(tuple.at(1) == -1){
            int R = tuple[0];
            int I = tuple[2];
            int T = tuple[3];
            if(var > 0){
                const Tuple* tuple1 = wdim.find(Tuple({I},&_dim));
                bool undef1 = false;
                if(tuple1==NULL){
                    tuple1 = udim.find(Tuple({I},&_dim));
                    undef1 = true;
                }
                if(tuple1!=NULL){
                    if(!undef1){
                        Tuple t({R,-1,I,T,I},&_poss_R_n1I_T_dim_I_);
                        if(wposs_R_n1I_T_dim_I_.find(t)==NULL){
                            if(uposs_R_n1I_T_dim_I_.find(t))
                                uposs_R_n1I_T_dim_I_.erase(t);
                            const auto& insertResult = wposs_R_n1I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                    positiveAggrReason[1][{R,T}].insert(var);
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            positiveAggrReason[1][{R,T}].insert(it->second);
                                        }
                                    }
                                }
                            }
                        }
                    }else{
                        Tuple t({R,-1,I,T,I},&_poss_R_n1I_T_dim_I_);
                        if(uposs_R_n1I_T_dim_I_.find(t)==NULL){
                            if(wposs_R_n1I_T_dim_I_.find(t))
                                wposs_R_n1I_T_dim_I_.erase(t);
                            const auto& insertResult = uposs_R_n1I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }else{
                const std::vector<const Tuple*>& tuplesU = u_poss_R_n1I_T_dim_I_0_1_2_3_.getValues({R,-1,I,T});
                while(!tuplesU.empty()){
                    Tuple t(*tuplesU.back());
                    uposs_R_n1I_T_dim_I_.erase(*tuplesU.back());
                    {
                        //bound var0
                        //bound var3
                        std::vector<int> aggrKey({t[2]});
                        auto& undefSet = undefAggrVars[1][{R,T}];
                        if(u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                            }
                        }
                        negativeAggrReason[1][{R,T}].insert(var);
                    }
                    {
                        //bound var0
                        //bound var3
                        std::vector<int> aggrKey({t[2]});
                        auto& undefSet = undefAggrVars[1][{R,T}];
                        if(u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_dim){
        int I = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pposs_1_2_.getValues({-1,I});
            const std::vector<const Tuple*>* tuplesU0 = &uposs_1_2_.getValues({-1,I});
            for(int i_0=0;i_0<tuples0->size()+tuplesU0->size();i_0++){
                const Tuple* tuple0;
                bool undef0=false;
                if(i_0<tuples0->size())
                    tuple0=tuples0->at(i_0);
                else{
                    tuple0=tuplesU0->at(i_0-tuples0->size());
                    undef0=true;
                }
                if(tuple0->at(1) == -1){
                    int R = tuple0->at(0);
                    int T = tuple0->at(3);
                    if(!undef0){
                        Tuple t({R,-1,I,T,I},&_poss_R_n1I_T_dim_I_);
                        if(wposs_R_n1I_T_dim_I_.find(t)==NULL){
                            if(uposs_R_n1I_T_dim_I_.find(t))
                                uposs_R_n1I_T_dim_I_.erase(t);
                            const auto& insertResult = wposs_R_n1I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            positiveAggrReason[1][{R,T}].insert(it->second);
                                        }
                                    }
                                    positiveAggrReason[1][{R,T}].insert(var);
                                }
                            }
                        }
                    }else{
                        Tuple t({R,-1,I,T,I},&_poss_R_n1I_T_dim_I_);
                        if(uposs_R_n1I_T_dim_I_.find(t)==NULL){
                            if(wposs_R_n1I_T_dim_I_.find(t))
                                wposs_R_n1I_T_dim_I_.erase(t);
                            const auto& insertResult = uposs_R_n1I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[1][{R,T}];
                                    auto& undefSet = undefAggrVars[1][{R,T}];
                                    if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_poss_R_n1I_T_dim_I_4_.getValues({I});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uposs_R_n1I_T_dim_I_.erase(*tuplesU.back());
                {
                    int R = t[0];
                    int T = t[3];
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[1][{R,T}];
                    if(u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                        }
                    }
                    negativeAggrReason[1][{R,T}].insert(var);
                }
                {
                    int R = t[0];
                    int T = t[3];
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[1][{R,T}];
                    if(u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_poss){
        if(tuple.at(1) == 1){
            int R = tuple[0];
            int I = tuple[2];
            int T = tuple[3];
            if(var > 0){
                const Tuple* tuple1 = wdim.find(Tuple({I},&_dim));
                bool undef1 = false;
                if(tuple1==NULL){
                    tuple1 = udim.find(Tuple({I},&_dim));
                    undef1 = true;
                }
                if(tuple1!=NULL){
                    if(!undef1){
                        Tuple t({R,1,I,T,I},&_poss_R_1_I_T_dim_I_);
                        if(wposs_R_1_I_T_dim_I_.find(t)==NULL){
                            if(uposs_R_1_I_T_dim_I_.find(t))
                                uposs_R_1_I_T_dim_I_.erase(t);
                            const auto& insertResult = wposs_R_1_I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                    positiveAggrReason[0][{R,T}].insert(var);
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            positiveAggrReason[0][{R,T}].insert(it->second);
                                        }
                                    }
                                }
                            }
                        }
                    }else{
                        Tuple t({R,1,I,T,I},&_poss_R_1_I_T_dim_I_);
                        if(uposs_R_1_I_T_dim_I_.find(t)==NULL){
                            if(wposs_R_1_I_T_dim_I_.find(t))
                                wposs_R_1_I_T_dim_I_.erase(t);
                            const auto& insertResult = uposs_R_1_I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }else{
                const std::vector<const Tuple*>& tuplesU = u_poss_R_1_I_T_dim_I_0_1_2_3_.getValues({R,1,I,T});
                while(!tuplesU.empty()){
                    Tuple t(*tuplesU.back());
                    uposs_R_1_I_T_dim_I_.erase(*tuplesU.back());
                    {
                        //bound var0
                        //bound var3
                        std::vector<int> aggrKey({t[2]});
                        auto& undefSet = undefAggrVars[0][{R,T}];
                        if(u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                            }
                        }
                        negativeAggrReason[0][{R,T}].insert(var);
                    }
                    {
                        //bound var0
                        //bound var3
                        std::vector<int> aggrKey({t[2]});
                        auto& undefSet = undefAggrVars[0][{R,T}];
                        if(u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_dim){
        int I = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pposs_1_2_.getValues({1,I});
            const std::vector<const Tuple*>* tuplesU0 = &uposs_1_2_.getValues({1,I});
            for(int i_0=0;i_0<tuples0->size()+tuplesU0->size();i_0++){
                const Tuple* tuple0;
                bool undef0=false;
                if(i_0<tuples0->size())
                    tuple0=tuples0->at(i_0);
                else{
                    tuple0=tuplesU0->at(i_0-tuples0->size());
                    undef0=true;
                }
                if(tuple0->at(1) == 1){
                    int R = tuple0->at(0);
                    int T = tuple0->at(3);
                    if(!undef0){
                        Tuple t({R,1,I,T,I},&_poss_R_1_I_T_dim_I_);
                        if(wposs_R_1_I_T_dim_I_.find(t)==NULL){
                            if(uposs_R_1_I_T_dim_I_.find(t))
                                uposs_R_1_I_T_dim_I_.erase(t);
                            const auto& insertResult = wposs_R_1_I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        trueSet.insert(aggrKey);
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            positiveAggrReason[0][{R,T}].insert(it->second);
                                        }
                                    }
                                    positiveAggrReason[0][{R,T}].insert(var);
                                }
                            }
                        }
                    }else{
                        Tuple t({R,1,I,T,I},&_poss_R_1_I_T_dim_I_);
                        if(uposs_R_1_I_T_dim_I_.find(t)==NULL){
                            if(wposs_R_1_I_T_dim_I_.find(t))
                                wposs_R_1_I_T_dim_I_.erase(t);
                            const auto& insertResult = uposs_R_1_I_T_dim_I_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                                {
                                    std::vector<int> aggrKey({t[2]});
                                    auto& trueSet = trueAggrVars[0][{R,T}];
                                    auto& undefSet = undefAggrVars[0][{R,T}];
                                    if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                        if(trueSet.find(aggrKey)!=trueSet.end()){
                                            trueSet.erase(aggrKey);
                                        }
                                    }
                                    if(undefSet.find(aggrKey)==undefSet.end()){
                                        if(trueSet.find(aggrKey)==trueSet.end()){
                                            undefSet.insert(aggrKey);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_poss_R_1_I_T_dim_I_4_.getValues({I});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uposs_R_1_I_T_dim_I_.erase(*tuplesU.back());
                {
                    int R = t[0];
                    int T = t[3];
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{R,T}];
                    if(u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                        }
                    }
                    negativeAggrReason[0][{R,T}].insert(var);
                }
                {
                    int R = t[0];
                    int T = t[3];
                    std::vector<int> aggrKey({t[2]});
                    auto& undefSet = undefAggrVars[0][{R,T}];
                    if(u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_0_ToAggregate_2.count({R,T})){
                    sharedVariables_0_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_0_ToAggregate_2.count({R,T})){
                    sharedVariables_0_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_1_ToAggregate_2.count({R,T})){
                    sharedVariables_1_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_1_ToAggregate_2.count({R,T})){
                    sharedVariables_1_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_2_ToAggregate_2.count({R,T})){
                    sharedVariables_2_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_2_ToAggregate_2.count({R,T})){
                    sharedVariables_2_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_3_ToAggregate_2.count({R,T})){
                    sharedVariables_3_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_3_ToAggregate_2.count({R,T})){
                    sharedVariables_3_ToAggregate_2.insert({R,T});
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
    if(var<0 && ( tuple.getPredicateName() == &_dim || tuple.getPredicateName() == &_poss)){
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
    if(tuple.getPredicateName() == &_poss && tuple.size()==4){
        if(tuple.at(1) == -1){
            int R = tuple[0];
            int I = tuple[2];
            int T = tuple[3];
            if(var > 0){
                const std::vector<const Tuple*>& tuples = p_poss_R_n1I_T_dim_I_0_1_2_3_.getValues({R,-1,I,T});
                while(!tuples.empty()){
                    Tuple t(*tuples.back());
                    wposs_R_n1I_T_dim_I_.erase(*tuples.back());
                    if(uposs_R_n1I_T_dim_I_.find(Tuple(t)) == NULL){
                        const auto& insertResult = uposs_R_n1I_T_dim_I_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                auto& trueSet = trueAggrVars[1][{R,T}];
                                auto& undefSet = undefAggrVars[1][{R,T}];
                                if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                    }
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                    }
                                }
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                auto& trueSet = trueAggrVars[1][{R,T}];
                                auto& undefSet = undefAggrVars[1][{R,T}];
                                if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                    }
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                    }
                                }
                                if(p_poss_R_n1I_T_dim_I_0_1_2_3_0_3_.getValues({t[0],t[1],t[2],t[3],R,T}).size() == 0){
                                    const auto & it = tupleToVar.find(Tuple({t[0],t[1],t[2],t[3]},&_poss));
                                    if(it != tupleToVar.end()) {
                                        positiveAggrReason[1][{R,T}].erase(it->second);
                                    }
                                }
                                if(p_poss_R_n1I_T_dim_I_4_0_3_.getValues({t[4],R,T}).size() == 0){
                                    const auto & it = tupleToVar.find(Tuple({t[4]},&_dim));
                                    if(it != tupleToVar.end()) {
                                        positiveAggrReason[1][{R,T}].erase(it->second);
                                    }
                                }
                            }
                        }
                    }
                }
            }else{
                for(auto& pair : negativeAggrReason[1]){
                    pair.second.erase(var);
                }
                for(auto& pair : negativeAggrReason[1]){
                    pair.second.erase(var);
                }
            }
            const Tuple* tuple1 = wdim.find(Tuple({I},&_dim));
            bool undef1 = false;
            if(tuple1==NULL){
                tuple1 = udim.find(Tuple({I},&_dim));
                undef1 = true;
            }
            if(tuple1!=NULL){
                Tuple t({R,-1,I,T,I},&_poss_R_n1I_T_dim_I_);
                if(uposs_R_n1I_T_dim_I_.find(Tuple(t))==NULL){
                    if(wposs_R_n1I_T_dim_I_.find(t))
                        wposs_R_n1I_T_dim_I_.erase(t);
                    const auto& insertResult = uposs_R_n1I_T_dim_I_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[1][{R,T}];
                            auto& undefSet = undefAggrVars[1][{R,T}];
                            if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[1][{R,T}];
                            auto& undefSet = undefAggrVars[1][{R,T}];
                            if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_dim && tuple.size()==1){
        int I = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_poss_R_n1I_T_dim_I_4_.getValues({I});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wposs_R_n1I_T_dim_I_.erase(*tuples.back());
                if(uposs_R_n1I_T_dim_I_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uposs_R_n1I_T_dim_I_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            int R = t[0];
                            int T = t[3];
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[1][{R,T}];
                            auto& undefSet = undefAggrVars[1][{R,T}];
                            if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                        {
                            int R = t[0];
                            int T = t[3];
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[1][{R,T}];
                            auto& undefSet = undefAggrVars[1][{R,T}];
                            if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                            if(p_poss_R_n1I_T_dim_I_0_1_2_3_0_3_.getValues({t[0],t[1],t[2],t[3],R,T}).size() == 0){
                                const auto & it = tupleToVar.find(Tuple({t[0],t[1],t[2],t[3]},&_poss));
                                if(it != tupleToVar.end()) {
                                    positiveAggrReason[1][{R,T}].erase(it->second);
                                }
                            }
                            if(p_poss_R_n1I_T_dim_I_4_0_3_.getValues({t[4],R,T}).size() == 0){
                                const auto & it = tupleToVar.find(Tuple({t[4]},&_dim));
                                if(it != tupleToVar.end()) {
                                    positiveAggrReason[1][{R,T}].erase(it->second);
                                }
                            }
                        }
                    }
                }
            }
        }else{
            for(auto& pair : negativeAggrReason[1]){
                pair.second.erase(var);
            }
            for(auto& pair : negativeAggrReason[1]){
                pair.second.erase(var);
            }
        }
        const std::vector<const Tuple*>& tuples0 = pposs_1_2_.getValues({-1,I});
        const std::vector<const Tuple*>& tuplesU0 = uposs_1_2_.getValues({-1,I});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            if(tuple0->at(1) == -1){
                int R = tuple0->at(0);
                int T = tuple0->at(3);
                Tuple t({R,-1,I,T,I},&_poss_R_n1I_T_dim_I_);
                if(uposs_R_n1I_T_dim_I_.find(Tuple(t))==NULL){
                    if(wposs_R_n1I_T_dim_I_.find(t))
                        wposs_R_n1I_T_dim_I_.erase(t);
                    const auto& insertResult = uposs_R_n1I_T_dim_I_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[1][{R,T}];
                            auto& undefSet = undefAggrVars[1][{R,T}];
                            if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[1][{R,T}];
                            auto& undefSet = undefAggrVars[1][{R,T}];
                            if(p_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_poss && tuple.size()==4){
        if(tuple.at(1) == 1){
            int R = tuple[0];
            int I = tuple[2];
            int T = tuple[3];
            if(var > 0){
                const std::vector<const Tuple*>& tuples = p_poss_R_1_I_T_dim_I_0_1_2_3_.getValues({R,1,I,T});
                while(!tuples.empty()){
                    Tuple t(*tuples.back());
                    wposs_R_1_I_T_dim_I_.erase(*tuples.back());
                    if(uposs_R_1_I_T_dim_I_.find(Tuple(t)) == NULL){
                        const auto& insertResult = uposs_R_1_I_T_dim_I_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                auto& trueSet = trueAggrVars[0][{R,T}];
                                auto& undefSet = undefAggrVars[0][{R,T}];
                                if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                    }
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                    }
                                }
                            }
                            {
                                std::vector<int> aggrKey({t[2]});
                                auto& trueSet = trueAggrVars[0][{R,T}];
                                auto& undefSet = undefAggrVars[0][{R,T}];
                                if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                    }
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                    }
                                }
                                if(p_poss_R_1_I_T_dim_I_0_1_2_3_0_3_.getValues({t[0],t[1],t[2],t[3],R,T}).size() == 0){
                                    const auto & it = tupleToVar.find(Tuple({t[0],t[1],t[2],t[3]},&_poss));
                                    if(it != tupleToVar.end()) {
                                        positiveAggrReason[0][{R,T}].erase(it->second);
                                    }
                                }
                                if(p_poss_R_1_I_T_dim_I_4_0_3_.getValues({t[4],R,T}).size() == 0){
                                    const auto & it = tupleToVar.find(Tuple({t[4]},&_dim));
                                    if(it != tupleToVar.end()) {
                                        positiveAggrReason[0][{R,T}].erase(it->second);
                                    }
                                }
                            }
                        }
                    }
                }
            }else{
                for(auto& pair : negativeAggrReason[0]){
                    pair.second.erase(var);
                }
                for(auto& pair : negativeAggrReason[0]){
                    pair.second.erase(var);
                }
            }
            const Tuple* tuple1 = wdim.find(Tuple({I},&_dim));
            bool undef1 = false;
            if(tuple1==NULL){
                tuple1 = udim.find(Tuple({I},&_dim));
                undef1 = true;
            }
            if(tuple1!=NULL){
                Tuple t({R,1,I,T,I},&_poss_R_1_I_T_dim_I_);
                if(uposs_R_1_I_T_dim_I_.find(Tuple(t))==NULL){
                    if(wposs_R_1_I_T_dim_I_.find(t))
                        wposs_R_1_I_T_dim_I_.erase(t);
                    const auto& insertResult = uposs_R_1_I_T_dim_I_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[0][{R,T}];
                            auto& undefSet = undefAggrVars[0][{R,T}];
                            if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[0][{R,T}];
                            auto& undefSet = undefAggrVars[0][{R,T}];
                            if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_dim && tuple.size()==1){
        int I = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_poss_R_1_I_T_dim_I_4_.getValues({I});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wposs_R_1_I_T_dim_I_.erase(*tuples.back());
                if(uposs_R_1_I_T_dim_I_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uposs_R_1_I_T_dim_I_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            int R = t[0];
                            int T = t[3];
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[0][{R,T}];
                            auto& undefSet = undefAggrVars[0][{R,T}];
                            if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                        {
                            int R = t[0];
                            int T = t[3];
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[0][{R,T}];
                            auto& undefSet = undefAggrVars[0][{R,T}];
                            if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                            if(p_poss_R_1_I_T_dim_I_0_1_2_3_0_3_.getValues({t[0],t[1],t[2],t[3],R,T}).size() == 0){
                                const auto & it = tupleToVar.find(Tuple({t[0],t[1],t[2],t[3]},&_poss));
                                if(it != tupleToVar.end()) {
                                    positiveAggrReason[0][{R,T}].erase(it->second);
                                }
                            }
                            if(p_poss_R_1_I_T_dim_I_4_0_3_.getValues({t[4],R,T}).size() == 0){
                                const auto & it = tupleToVar.find(Tuple({t[4]},&_dim));
                                if(it != tupleToVar.end()) {
                                    positiveAggrReason[0][{R,T}].erase(it->second);
                                }
                            }
                        }
                    }
                }
            }
        }else{
            for(auto& pair : negativeAggrReason[0]){
                pair.second.erase(var);
            }
            for(auto& pair : negativeAggrReason[0]){
                pair.second.erase(var);
            }
        }
        const std::vector<const Tuple*>& tuples0 = pposs_1_2_.getValues({1,I});
        const std::vector<const Tuple*>& tuplesU0 = uposs_1_2_.getValues({1,I});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            if(tuple0->at(1) == 1){
                int R = tuple0->at(0);
                int T = tuple0->at(3);
                Tuple t({R,1,I,T,I},&_poss_R_1_I_T_dim_I_);
                if(uposs_R_1_I_T_dim_I_.find(Tuple(t))==NULL){
                    if(wposs_R_1_I_T_dim_I_.find(t))
                        wposs_R_1_I_T_dim_I_.erase(t);
                    const auto& insertResult = uposs_R_1_I_T_dim_I_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[0][{R,T}];
                            auto& undefSet = undefAggrVars[0][{R,T}];
                            if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[2]});
                            auto& trueSet = trueAggrVars[0][{R,T}];
                            auto& undefSet = undefAggrVars[0][{R,T}];
                            if(p_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,t[2]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_0_ToAggregate_2.count({R,T})){
                    sharedVariables_0_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_0_ToAggregate_2.count({R,T})){
                    sharedVariables_0_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_1_ToAggregate_2.count({R,T})){
                    sharedVariables_1_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_1_ToAggregate_2.count({R,T})){
                    sharedVariables_1_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_2_ToAggregate_2.count({R,T})){
                    sharedVariables_2_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_2_ToAggregate_2.count({R,T})){
                    sharedVariables_2_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_robot){
        int R = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = ustep_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = pstep_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int T = tuple1->at(0);
            {
                if(!sharedVariables_3_ToAggregate_2.count({R,T})){
                    sharedVariables_3_ToAggregate_2.insert({R,T});
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_step){
        int T = tuple.at(0);
        const std::vector<const Tuple *>& undefTuples1 = urobot_.getValues({});
        const std::vector<const Tuple*>& trueTuples1 = probot_.getValues({});
        for(int i=0;i<undefTuples1.size()+trueTuples1.size();i++){
            const Tuple * tuple1;
            if(i<undefTuples1.size())
                tuple1 = undefTuples1[i];
            else tuple1 = trueTuples1[i-undefTuples1.size()];
            int R = tuple1->at(0);
            {
                if(!sharedVariables_3_ToAggregate_2.count({R,T})){
                    sharedVariables_3_ToAggregate_2.insert({R,T});
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
    predicateWSetMap[&_robot]=&wrobot;
    predicateUSetMap[&_robot]=&urobot;
    stringToUniqueStringPointer["robot"] = &_robot;
    predicateWSetMap[&_step]=&wstep;
    predicateUSetMap[&_step]=&ustep;
    stringToUniqueStringPointer["step"] = &_step;
    predicateWSetMap[&_poss]=&wposs;
    predicateFSetMap[&_poss]=&fposs;
    predicateUSetMap[&_poss]=&uposs;
    stringToUniqueStringPointer["poss"] = &_poss;
    predicateWSetMap[&_dim]=&wdim;
    predicateFSetMap[&_dim]=&fdim;
    predicateUSetMap[&_dim]=&udim;
    stringToUniqueStringPointer["dim"] = &_dim;
    predicateWSetMap[&_poss]=&wposs;
    predicateFSetMap[&_poss]=&fposs;
    predicateUSetMap[&_poss]=&uposs;
    stringToUniqueStringPointer["poss"] = &_poss;
    predicateWSetMap[&_dim]=&wdim;
    predicateFSetMap[&_dim]=&fdim;
    predicateUSetMap[&_dim]=&udim;
    stringToUniqueStringPointer["dim"] = &_dim;
    predicateWSetMap[&_poss]=&wposs;
    predicateFSetMap[&_poss]=&fposs;
    predicateUSetMap[&_poss]=&uposs;
    stringToUniqueStringPointer["poss"] = &_poss;
    predicateWSetMap[&_dim]=&wdim;
    predicateFSetMap[&_dim]=&fdim;
    predicateUSetMap[&_dim]=&udim;
    stringToUniqueStringPointer["dim"] = &_dim;
    predicateWSetMap[&_poss]=&wposs;
    predicateFSetMap[&_poss]=&fposs;
    predicateUSetMap[&_poss]=&uposs;
    stringToUniqueStringPointer["poss"] = &_poss;
    predicateWSetMap[&_dim]=&wdim;
    predicateFSetMap[&_dim]=&fdim;
    predicateUSetMap[&_dim]=&udim;
    stringToUniqueStringPointer["dim"] = &_dim;
    predicateToAuxiliaryMaps[&_step].push_back(&pstep_);
    predicateToAuxiliaryMaps[&_step].push_back(&pstep_0_);
    predicateToAuxiliaryMaps[&_robot].push_back(&probot_);
    predicateToAuxiliaryMaps[&_robot].push_back(&probot_0_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_1_2_3_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_1_2_3_0_3_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_1_2_3_0_3_2_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_3_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_3_0_1_2_3_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_3_2_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_0_3_4_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_2_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_4_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_4_0_3_);
    predicateToAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&p_poss_R_1_I_T_dim_I_4_0_3_2_);
    predicateToAuxiliaryMaps[&_dim].push_back(&pdim_);
    predicateToAuxiliaryMaps[&_dim].push_back(&pdim_0_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_1_2_3_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_1_2_3_0_3_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_1_2_3_0_3_2_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_3_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_3_0_1_2_3_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_3_2_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_0_3_4_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_2_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_4_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_4_0_3_);
    predicateToAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&p_poss_R_n1I_T_dim_I_4_0_3_2_);
    predicateToAuxiliaryMaps[&_poss].push_back(&pposs_);
    predicateToAuxiliaryMaps[&_poss].push_back(&pposs_0_1_2_3_);
    predicateToAuxiliaryMaps[&_poss].push_back(&pposs_0_1_3_);
    predicateToAuxiliaryMaps[&_poss].push_back(&pposs_1_2_);
    predicateToUndefAuxiliaryMaps[&_step].push_back(&ustep_);
    predicateToUndefAuxiliaryMaps[&_step].push_back(&ustep_0_);
    predicateToUndefAuxiliaryMaps[&_robot].push_back(&urobot_);
    predicateToUndefAuxiliaryMaps[&_robot].push_back(&urobot_0_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_1_2_3_0_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_1_2_3_0_3_2_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_3_0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_3_2_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_0_3_4_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_2_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_4_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_4_0_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_1_I_T_dim_I_].push_back(&u_poss_R_1_I_T_dim_I_4_0_3_2_);
    predicateToUndefAuxiliaryMaps[&_dim].push_back(&udim_);
    predicateToUndefAuxiliaryMaps[&_dim].push_back(&udim_0_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_1_2_3_0_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_1_2_3_0_3_2_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_3_0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_3_2_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_0_3_4_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_2_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_4_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_4_0_3_);
    predicateToUndefAuxiliaryMaps[&_poss_R_n1I_T_dim_I_].push_back(&u_poss_R_n1I_T_dim_I_4_0_3_2_);
    predicateToUndefAuxiliaryMaps[&_poss].push_back(&uposs_);
    predicateToUndefAuxiliaryMaps[&_poss].push_back(&uposs_0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_poss].push_back(&uposs_0_1_3_);
    predicateToUndefAuxiliaryMaps[&_poss].push_back(&uposs_1_2_);
    predicateToFalseAuxiliaryMaps[&_dim].push_back(&fdim_);
    predicateToFalseAuxiliaryMaps[&_dim].push_back(&fdim_0_);
    predicateToFalseAuxiliaryMaps[&_poss].push_back(&fposs_);
    predicateToFalseAuxiliaryMaps[&_poss].push_back(&fposs_0_1_2_3_);
    predicateToFalseAuxiliaryMaps[&_poss].push_back(&fposs_0_1_3_);
    predicateToFalseAuxiliaryMaps[&_poss].push_back(&fposs_1_2_);
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
            tuples = &probot_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &urobot_.getValues({});
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
                int R = (*tuple0)[0];
                const std::vector<const Tuple* >* tuples;
                tuples = &pstep_.getValues({});
                const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                if(tupleU == NULL){
                    tuplesU = &ustep_.getValues({});
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
                    int T = (*tuple1)[0];
                    int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                    //1
                    if(!(undefPlusTrue>=1)){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});
                        }else{
                            const auto & it = tupleToVar.find(*tupleU);
                            if(it != tupleToVar.end()) {
                                int sign = tupleUNegated ? -1 : 1;
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                            bool propagated=false;
                            if(undefPlusTrue == 1){
                                for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                    const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                        if(tuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                        const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                        if(tuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
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
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &probot_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &urobot_.getValues({});
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
                int R = (*tuple0)[0];
                const std::vector<const Tuple* >* tuples;
                tuples = &pstep_.getValues({});
                const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                if(tupleU == NULL){
                    tuplesU = &ustep_.getValues({});
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
                    int T = (*tuple1)[0];
                    if(trueAggrVars[0][{R,T}].size()>=1+1){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});
                        }else{
                            const auto & it = tupleToVar.find(*tupleU);
                            if(it != tupleToVar.end()) {
                                int sign = tupleUNegated ? -1 : 1;
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            bool propagated=false;
                            if(trueAggrVars[0][{R,T}].size() == 1){
                                for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                    const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                            const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                            const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                            if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                const auto & it = tupleToVar.find(*aggrTupleU0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                            const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                            const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                            if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                const auto & it = tupleToVar.find(*aggrTupleU1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
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
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &probot_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &urobot_.getValues({});
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
                int R = (*tuple0)[0];
                const std::vector<const Tuple* >* tuples;
                tuples = &pstep_.getValues({});
                const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                if(tupleU == NULL){
                    tuplesU = &ustep_.getValues({});
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
                    int T = (*tuple1)[0];
                    int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                    //1
                    if(!(undefPlusTrue>=1)){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});
                        }else{
                            const auto & it = tupleToVar.find(*tupleU);
                            if(it != tupleToVar.end()) {
                                int sign = tupleUNegated ? -1 : 1;
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                            bool propagated=false;
                            if(undefPlusTrue == 1){
                                for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                    const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                        if(tuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                        const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                        if(tuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
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
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &probot_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &urobot_.getValues({});
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
                int R = (*tuple0)[0];
                const std::vector<const Tuple* >* tuples;
                tuples = &pstep_.getValues({});
                const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                if(tupleU == NULL){
                    tuplesU = &ustep_.getValues({});
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
                    int T = (*tuple1)[0];
                    if(trueAggrVars[1][{R,T}].size()>=1+1){
                        if(tupleU == NULL){
                            std::cout<<"propagation started from literal"<<std::endl;
                            std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                            propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});
                        }else{
                            const auto & it = tupleToVar.find(*tupleU);
                            if(it != tupleToVar.end()) {
                                int sign = tupleUNegated ? -1 : 1;
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                            }
                        }
                    }
                    if(tupleU == NULL){
                        {
                            bool propagated=false;
                            if(trueAggrVars[1][{R,T}].size() == 1){
                                for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                    const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                            const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                            const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                            if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                const auto & it = tupleToVar.find(*aggrTupleU0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                            const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                            const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                            if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                const auto & it = tupleToVar.find(*aggrTupleU1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
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
            if((starter.getPredicateName()== &_poss && facts[i]>0) || (starter.getPredicateName()== &_dim && facts[i]>0)){
                for(const auto & sharedVarTuple3_2 : sharedVariables_3_ToAggregate_2){
                    int R = sharedVarTuple3_2[0];
                    int T = sharedVarTuple3_2[1];
                    if(trueAggrVars[1][{R,T}].size()>=1+1){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                std::vector<int> local_reason;
                                local_reason.insert(local_reason.end(),positiveAggrReason[1][{R,T}].begin(), positiveAggrReason[1][{R,T}].end());
                                const auto & it = tupleToVar.find(Tuple(starter));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                }
                                if(tuple1!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple1));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tuple2!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple2));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tupleU == NULL){
                                    std::cout<<"propagation started from Aggr"<<std::endl;
                                    std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                    propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                                }else{
                                    const auto & it = tupleToVar.find(*tupleU);
                                    if(it != tupleToVar.end()) {
                                        int sign = tupleUNegated ? -1 : 1;
                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                    }
                                }
                            }
                        }
                    }//close aggr true if
                    bool propagated=false;
                    if(trueAggrVars[1][{R,T}].size() == 1){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),positiveAggrReason[1][{R,T}].begin(), positiveAggrReason[1][{R,T}].end());
                                    const auto & it = tupleToVar.find(Tuple(starter));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple2!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple2));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple1!=NULL){
                                                        const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                        if(it_tuple1!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple1->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU0);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple0!=NULL){
                                                        const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                        if(it_tuple0!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }//close can prop if
                    else{
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                }
                            }
                        }
                    }//close prop multi join
                }
            }
        }//local scope
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if((starter.getPredicateName()== &_poss && facts[i]<0) || (starter.getPredicateName()== &_dim && facts[i]<0)){
                for(const auto & sharedVarTuple2_2 : sharedVariables_2_ToAggregate_2){
                    int R = sharedVarTuple2_2[0];
                    int T = sharedVarTuple2_2[1];
                    int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                    //1
                    if(!(undefPlusTrue>=1)){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                std::vector<int> local_reason;
                                local_reason.insert(local_reason.end(),negativeAggrReason[1][{R,T}].begin(), negativeAggrReason[1][{R,T}].end());
                                const auto & it = tupleToVar.find(Tuple(starter));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                }
                                if(tuple1!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple1));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tuple2!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple2));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tupleU == NULL){
                                    std::cout<<"propagation started from Aggr"<<std::endl;
                                    std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                    propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                                }else{
                                    const auto & it = tupleToVar.find(*tupleU);
                                    if(it != tupleToVar.end()) {
                                        int sign = tupleUNegated ? -1 : 1;
                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                    }
                                }
                            }
                        }
                    }//close aggr true if
                    bool propagated=false;
                    if(undefPlusTrue == 1){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[1][{R,T}].begin(), negativeAggrReason[1][{R,T}].end());
                                    const auto & it = tupleToVar.find(Tuple(starter));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple2!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple2));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }//close can prop if
                    else{
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                }
                            }
                        }
                    }//close prop multi join
                }
            }
        }//local scope
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if((starter.getPredicateName()== &_poss && facts[i]>0) || (starter.getPredicateName()== &_dim && facts[i]>0)){
                for(const auto & sharedVarTuple1_2 : sharedVariables_1_ToAggregate_2){
                    int R = sharedVarTuple1_2[0];
                    int T = sharedVarTuple1_2[1];
                    if(trueAggrVars[0][{R,T}].size()>=1+1){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                std::vector<int> local_reason;
                                local_reason.insert(local_reason.end(),positiveAggrReason[0][{R,T}].begin(), positiveAggrReason[0][{R,T}].end());
                                const auto & it = tupleToVar.find(Tuple(starter));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                }
                                if(tuple1!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple1));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tuple2!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple2));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tupleU == NULL){
                                    std::cout<<"propagation started from Aggr"<<std::endl;
                                    std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                    propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                                }else{
                                    const auto & it = tupleToVar.find(*tupleU);
                                    if(it != tupleToVar.end()) {
                                        int sign = tupleUNegated ? -1 : 1;
                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                    }
                                }
                            }
                        }
                    }//close aggr true if
                    bool propagated=false;
                    if(trueAggrVars[0][{R,T}].size() == 1){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),positiveAggrReason[0][{R,T}].begin(), positiveAggrReason[0][{R,T}].end());
                                    const auto & it = tupleToVar.find(Tuple(starter));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple2!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple2));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple1!=NULL){
                                                        const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                        if(it_tuple1!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple1->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU0);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple0!=NULL){
                                                        const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                        if(it_tuple0!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }//close can prop if
                    else{
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                }
                            }
                        }
                    }//close prop multi join
                }
            }
        }//local scope
        if(starter.getPredicateName() == &_robot) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int R = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pstep_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &ustep_.getValues({});
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
                        int T = (*tuple1)[0];
                        int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                        //1
                        if(!(undefPlusTrue>=1)){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[0][{R,T}].begin(), negativeAggrReason[0][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                                bool propagated=false;
                                if(undefPlusTrue == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[0][{R,T}].begin(), negativeAggrReason[0][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int R = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pstep_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &ustep_.getValues({});
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
                        int T = (*tuple1)[0];
                        if(trueAggrVars[0][{R,T}].size()>=1+1){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),positiveAggrReason[0][{R,T}].begin(), positiveAggrReason[0][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                bool propagated=false;
                                if(trueAggrVars[0][{R,T}].size() == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),positiveAggrReason[0][{R,T}].begin(), positiveAggrReason[0][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple1!=NULL){
                                                        const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                        if(it_tuple1!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple1->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU0);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple0!=NULL){
                                                        const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                        if(it_tuple0!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int R = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pstep_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &ustep_.getValues({});
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
                        int T = (*tuple1)[0];
                        int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                        //1
                        if(!(undefPlusTrue>=1)){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[1][{R,T}].begin(), negativeAggrReason[1][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                                bool propagated=false;
                                if(undefPlusTrue == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[1][{R,T}].begin(), negativeAggrReason[1][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int R = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pstep_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &ustep_.getValues({});
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
                        int T = (*tuple1)[0];
                        if(trueAggrVars[1][{R,T}].size()>=1+1){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),positiveAggrReason[1][{R,T}].begin(), positiveAggrReason[1][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                bool propagated=false;
                                if(trueAggrVars[1][{R,T}].size() == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),positiveAggrReason[1][{R,T}].begin(), positiveAggrReason[1][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple1!=NULL){
                                                        const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                        if(it_tuple1!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple1->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU0);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple0!=NULL){
                                                        const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                        if(it_tuple0!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        if(starter.getPredicateName() == &_step) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int T = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &probot_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &urobot_.getValues({});
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
                        int R = (*tuple1)[0];
                        int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                        //1
                        if(!(undefPlusTrue>=1)){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[0][{R,T}].begin(), negativeAggrReason[0][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                                bool propagated=false;
                                if(undefPlusTrue == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[0][{R,T}].begin(), negativeAggrReason[0][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int T = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &probot_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &urobot_.getValues({});
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
                        int R = (*tuple1)[0];
                        if(trueAggrVars[0][{R,T}].size()>=1+1){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),positiveAggrReason[0][{R,T}].begin(), positiveAggrReason[0][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                bool propagated=false;
                                if(trueAggrVars[0][{R,T}].size() == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),positiveAggrReason[0][{R,T}].begin(), positiveAggrReason[0][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple1!=NULL){
                                                        const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                        if(it_tuple1!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple1->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU0);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple0!=NULL){
                                                        const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                        if(it_tuple0!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int T = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &probot_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &urobot_.getValues({});
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
                        int R = (*tuple1)[0];
                        int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                        //1
                        if(!(undefPlusTrue>=1)){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[1][{R,T}].begin(), negativeAggrReason[1][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                int undefPlusTrue = trueAggrVars[1][{R,T}].size()+undefAggrVars[1][{R,T}].size();
                                bool propagated=false;
                                if(undefPlusTrue == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[1][{R,T}].begin(), negativeAggrReason[1][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int T = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &probot_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &urobot_.getValues({});
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
                        int R = (*tuple1)[0];
                        if(trueAggrVars[1][{R,T}].size()>=1+1){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),positiveAggrReason[1][{R,T}].begin(), positiveAggrReason[1][{R,T}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            if(tuple1!=tupleU){
                                const auto & it = tupleToVar.find(Tuple(*tuple1));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second);
                                }
                            }
                            if(tupleU == NULL){
                                std::cout<<"propagation started from literal"<<std::endl;
                                std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                            }else{
                                const auto & it = tupleToVar.find(*tupleU);
                                if(it != tupleToVar.end()) {
                                    int sign = tupleUNegated ? -1 : 1;
                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                bool propagated=false;
                                if(trueAggrVars[1][{R,T}].size() == 1){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),positiveAggrReason[1][{R,T}].begin(), positiveAggrReason[1][{R,T}].end());
                                    if(tuple0!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple0));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[1][{R,T}].begin();undefKey!=undefAggrVars[1][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_n1I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tuple1 = wdim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                if(aggrTupleU0!=NULL && tuple1!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple1!=NULL){
                                                        const auto & it_tuple1 = tupleToVar.find(*tuple1);
                                                        if(it_tuple1!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple1->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU0);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = udim.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_dim));
                                                const Tuple* tuple0 = wposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                const Tuple* tupleU0 = uposs.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1), undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_poss));
                                                if(aggrTupleU1!=NULL && tuple0!=NULL ){
                                                    std::vector<int> propagationReason(local_reason);
                                                    if(tuple0!=NULL){
                                                        const auto & it_tuple0 = tupleToVar.find(*tuple0);
                                                        if(it_tuple0!=tupleToVar.end()){
                                                            propagationReason.push_back(it_tuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = 1;
                                                        found=true;
                                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
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
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if((starter.getPredicateName()== &_poss && facts[i]<0) || (starter.getPredicateName()== &_dim && facts[i]<0)){
                for(const auto & sharedVarTuple0_2 : sharedVariables_0_ToAggregate_2){
                    int R = sharedVarTuple0_2[0];
                    int T = sharedVarTuple0_2[1];
                    int undefPlusTrue = trueAggrVars[0][{R,T}].size()+undefAggrVars[0][{R,T}].size();
                    //1
                    if(!(undefPlusTrue>=1)){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                std::vector<int> local_reason;
                                local_reason.insert(local_reason.end(),negativeAggrReason[0][{R,T}].begin(), negativeAggrReason[0][{R,T}].end());
                                const auto & it = tupleToVar.find(Tuple(starter));
                                if(it!=tupleToVar.end()){
                                    local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                }
                                if(tuple1!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple1));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tuple2!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple2));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                if(tupleU == NULL){
                                    std::cout<<"propagation started from Aggr"<<std::endl;
                                    std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                                    propagatedLiteralsAndReasons.insert({-1, std::vector<int>(local_reason)});
                                }else{
                                    const auto & it = tupleToVar.find(*tupleU);
                                    if(it != tupleToVar.end()) {
                                        int sign = tupleUNegated ? -1 : 1;
                                        propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                                    }
                                }
                            }
                        }
                    }//close aggr true if
                    bool propagated=false;
                    if(undefPlusTrue == 1){
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[0][{R,T}].begin(), negativeAggrReason[0][{R,T}].end());
                                    const auto & it = tupleToVar.find(Tuple(starter));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                                    }
                                    if(tuple1!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple1));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    if(tuple2!=tupleU){
                                        const auto & it = tupleToVar.find(Tuple(*tuple2));
                                        if(it!=tupleToVar.end()){
                                            local_reason.push_back(it->second);
                                        }
                                    }
                                    for(auto undefKey = undefAggrVars[0][{R,T}].begin();undefKey!=undefAggrVars[0][{R,T}].end();undefKey++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_poss_R_1_I_T_dim_I_0_3_2_.getValues({R,T,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = uposs.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_poss));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = udim.find(Tuple({undefinedTuples->at(0)->at(4)},&_dim));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }//close can prop if
                    else{
                        tupleU=NULL;
                        const Tuple * tuple1 = (wrobot.find(Tuple({R},&_robot)));
                        if(!tuple1 && !tupleU ){
                            tuple1 = tupleU = (urobot.find(Tuple({R},&_robot)));
                            tupleUNegated = false;
                        }
                        if(tuple1){
                            const Tuple * tuple2 = (wstep.find(Tuple({T},&_step)));
                            if(!tuple2 && !tupleU ){
                                tuple2 = tupleU = (ustep.find(Tuple({T},&_step)));
                                tupleUNegated = false;
                            }
                            if(tuple2){
                                if(tupleU == NULL){
                                }
                            }
                        }
                    }//close prop multi join
                }
            }
        }//local scope
    }
}
}
