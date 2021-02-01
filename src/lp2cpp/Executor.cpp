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
const std::string _c = "c";
PredicateWSet wc(3);
PredicateWSet uc(3);
PredicateWSet fc(3);
const std::string _a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_ = "a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_";
PredicateWSet wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_(9);
PredicateWSet ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_(9);
PredicateWSet nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_(9);
PredicateWSet nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_(9);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_0;
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueNegativeAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefNegativeAggrVars[1];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason[1];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> actualSum[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleSum[1];
std::unordered_map<std::vector<int>, int,TuplesHash> actualNegativeSum[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleNegativeSum[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> maxPossibleNegativeSum[1];
int currentReasonLevel=-1;
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
AuxMap pa_0_1_({0,1});
AuxMap ua_0_1_({0,1});
AuxMap fa_0_1_({0,1});
AuxMap pa_({});
AuxMap ua_({});
AuxMap fa_({});
AuxMap pc_0_1_({0,1});
AuxMap uc_0_1_({0,1});
AuxMap fc_0_1_({0,1});
AuxMap pc_0_1_2_({0,1,2});
AuxMap uc_0_1_2_({0,1,2});
AuxMap fc_0_1_2_({0,1,2});
AuxMap pc_({});
AuxMap uc_({});
AuxMap fc_({});
AuxMap pa_1_({1});
AuxMap ua_1_({1});
AuxMap fa_1_({1});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_({6,2,0});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_({6,2,0});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_({6,2,0});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_({6,2,0});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_({});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_({});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_({});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_({});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_({0,1});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_({0,1});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_({0,1});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_({0,1});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_({2,3});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_({2,3});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_({2,3});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_({2,3});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_({4,5,6});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_({4,5,6});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_({4,5,6});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_({4,5,6});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_({7,8});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_({7,8});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_({7,8});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_({7,8});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_({0,1,6,2,0});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_({0,1,6,2,0});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_({0,1,6,2,0});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_({0,1,6,2,0});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_({2,3,6,2,0});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_({2,3,6,2,0});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_({2,3,6,2,0});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_({2,3,6,2,0});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_({4,5,6,6,2,0});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_({4,5,6,6,2,0});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_({4,5,6,6,2,0});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_({4,5,6,6,2,0});
AuxMap p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_({7,8,6,2,0});
AuxMap u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_({7,8,6,2,0});
AuxMap np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_({7,8,6,2,0});
AuxMap nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_({7,8,6,2,0});
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
    std::cout<<"True "<<minus;tuple.print();std::cout<<std::endl;
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
    if(var<0 && ( tuple.getPredicateName() == &_a || tuple.getPredicateName() == &_c)){
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
    if(tuple.getPredicateName() == &_a){
        int W = tuple[0];
        int Z = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
            for(int i_1=0;i_1<tuples1->size();i_1++){
                const Tuple* tuple1=tuples1->at(i_1);
                int Y = tuple1->at(0);
                int V = tuple1->at(1);
                const std::vector<const Tuple*>* tuples2 = &pc_0_1_.getValues({Z,Z});
                for(int i_2=0;i_2<tuples2->size();i_2++){
                    const Tuple* tuple2=tuples2->at(i_2);
                    if(tuple2->at(0) == tuple2->at(1)){
                        int X = tuple2->at(2);
                        const Tuple negativeTuple3({X,Z},&_a,true);
                        const Tuple* tuple3 = ua.find(Tuple({X,Z},&_a));
                        if(wa.find(negativeTuple3)==NULL && tuple3==NULL){
                            tuple3=&negativeTuple3;
                            Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                            {
                                std::vector<int> aggrKey({t[6],t[2],t[0]});
                                if(aggrKey[0]>0){
                                    if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                        if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                            ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                        const auto& insertResult = wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                                auxMap -> insert2(*insertResult.first);
                                            }
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
                                        tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple2);
                                            if(it != tupleToVar.end()) {
                                                tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                tuple3->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }else{
                                    if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                        if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                            nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                        const auto& insertResult = nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
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
                                        tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple2);
                                            if(it != tupleToVar.end()) {
                                                tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                tuple3->print();std::cout<<"Added to positive reason"<<std::endl;
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
            const std::vector<const Tuple*>& tuplesU = u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_.getValues({W,Z});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[6],t[2],t[0]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                    tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_.getValues({W,Z});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[6],t[2],t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                        if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
        int V = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pa_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int W = tuple0->at(0);
                int Z = tuple0->at(1);
                const std::vector<const Tuple*>* tuples2 = &pc_0_1_.getValues({Z,Z});
                for(int i_2=0;i_2<tuples2->size();i_2++){
                    const Tuple* tuple2=tuples2->at(i_2);
                    if(tuple2->at(0) == tuple2->at(1)){
                        int X = tuple2->at(2);
                        const Tuple negativeTuple3({X,Z},&_a,true);
                        const Tuple* tuple3 = ua.find(Tuple({X,Z},&_a));
                        if(wa.find(negativeTuple3)==NULL && tuple3==NULL){
                            tuple3=&negativeTuple3;
                            Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                            {
                                std::vector<int> aggrKey({t[6],t[2],t[0]});
                                if(aggrKey[0]>0){
                                    if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                        if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                            ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                        const auto& insertResult = wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                                auxMap -> insert2(*insertResult.first);
                                            }
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
                                        tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                        {
                                            const auto & it = tupleToVar.find(*tuple0);
                                            if(it != tupleToVar.end()) {
                                                tuple0->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple2);
                                            if(it != tupleToVar.end()) {
                                                tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                tuple3->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }else{
                                    if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                        if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                            nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                        const auto& insertResult = nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
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
                                        tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                        {
                                            const auto & it = tupleToVar.find(*tuple0);
                                            if(it != tupleToVar.end()) {
                                                tuple0->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple2);
                                            if(it != tupleToVar.end()) {
                                                tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                tuple3->print();std::cout<<"Added to positive reason"<<std::endl;
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
            const std::vector<const Tuple*>& tuplesU = u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_.getValues({Y,V});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[6],t[2],t[0]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                    tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_.getValues({Y,V});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[6],t[2],t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                        if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_c){
        if(tuple.at(0) == tuple.at(1)){
            int Z = tuple[0];
            int X = tuple[2];
            if(var > 0){
                const std::vector<const Tuple*>* tuples0 = &pa_1_.getValues({Z});
                for(int i_0=0;i_0<tuples0->size();i_0++){
                    const Tuple* tuple0=tuples0->at(i_0);
                    int W = tuple0->at(0);
                    const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
                    for(int i_1=0;i_1<tuples1->size();i_1++){
                        const Tuple* tuple1=tuples1->at(i_1);
                        int Y = tuple1->at(0);
                        int V = tuple1->at(1);
                        const Tuple negativeTuple3({X,Z},&_a,true);
                        const Tuple* tuple3 = ua.find(Tuple({X,Z},&_a));
                        if(wa.find(negativeTuple3)==NULL && tuple3==NULL){
                            tuple3=&negativeTuple3;
                            Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                            {
                                std::vector<int> aggrKey({t[6],t[2],t[0]});
                                if(aggrKey[0]>0){
                                    if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                        if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                            ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                        const auto& insertResult = wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                                auxMap -> insert2(*insertResult.first);
                                            }
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
                                        tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                        {
                                            const auto & it = tupleToVar.find(*tuple0);
                                            if(it != tupleToVar.end()) {
                                                tuple0->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                tuple3->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }else{
                                    if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                        if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                            nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                        const auto& insertResult = nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
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
                                        tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                        {
                                            const auto & it = tupleToVar.find(*tuple0);
                                            if(it != tupleToVar.end()) {
                                                tuple0->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                                reas.insert(it->second);
                                            }
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple3);
                                            if(it != tupleToVar.end()) {
                                                tuple3->print();std::cout<<"Added to positive reason"<<std::endl;
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
                const std::vector<const Tuple*>& tuplesU = u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_.getValues({Z,Z,X});
                while(!tuplesU.empty()){
                    Tuple t(*tuplesU.back());
                    ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesU.back());
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        auto& undefSet = undefAggrVars[0][{}];
                        if(u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleSum[0][{}]-=aggrKey[0];
                            }
                        }
                        auto& reas = negativeAggrReason[0][{}];
                        while(reas.getCurrentLevel()<currentReasonLevel)
                            reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
                const std::vector<const Tuple*>& tuplesNU = nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_.getValues({Z,Z,X});
                while(!tuplesNU.empty()){
                    Tuple t(*tuplesNU.back());
                    nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesNU.back());
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        if(nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                            if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
        int X = tuple[0];
        int Z = tuple[1];
        if(var < 0){
            const std::vector<const Tuple*>* tuples0 = &pa_1_.getValues({Z});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int W = tuple0->at(0);
                const std::vector<const Tuple*>* tuples1 = &pa_.getValues({});
                for(int i_1=0;i_1<tuples1->size();i_1++){
                    const Tuple* tuple1=tuples1->at(i_1);
                    int Y = tuple1->at(0);
                    int V = tuple1->at(1);
                    const Tuple* tuple2 = wc.find(Tuple({Z,Z,X},&_c));
                    if(tuple2!=NULL){
                        Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                        {
                            std::vector<int> aggrKey({t[6],t[2],t[0]});
                            if(aggrKey[0]>0){
                                if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                    if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
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
                                    tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            tuple0->print();std::cout<<"Added to positive reason"<<std::endl;
                                            reas.insert(it->second);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                            reas.insert(it->second);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple2);
                                        if(it != tupleToVar.end()) {
                                            tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
                                            reas.insert(it->second);
                                        }
                                    }
                                }
                            }else{
                                if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t)==NULL){
                                    if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
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
                                    tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            tuple0->print();std::cout<<"Added to positive reason"<<std::endl;
                                            reas.insert(it->second);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                            reas.insert(it->second);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple2);
                                        if(it != tupleToVar.end()) {
                                            tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
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
            const std::vector<const Tuple*>& tuplesU = u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_.getValues({X,Z});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[6],t[2],t[0]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                    tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_.getValues({X,Z});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesNU.back());
                {
                    std::vector<int> aggrKey({t[6],t[2],t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    if(nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                        if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
    std::cout<<"Undef "<<minus;tuple.print();std::cout<<std::endl;
    std::cout<<"Unde "<<minus<<var<<std::endl;
    if (var > 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple.getPredicateName());
        if (wSetIt != predicateWSetMap.end()) {
            wSetIt->second->erase(tuple);
        }
    }
    if(var<0 && ( tuple.getPredicateName() == &_a || tuple.getPredicateName() == &_c)){
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
    if(currentReasonLevel>=0)
        currentReasonLevel--;
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int W = tuple[0];
        int Z = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_.getValues({W,Z});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuples.back());
                if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_.getValues({W,Z});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesN.back());
                if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& reas = negativeAggrReason[0][{}];
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
            int V = tuple1->at(1);
            const std::vector<const Tuple*>& tuples2 = pc_0_1_.getValues({Z,Z});
            const std::vector<const Tuple*>& tuplesU2 = uc_0_1_.getValues({Z,Z});
            for(int i_2=0;i_2<tuples2.size()+tuplesU2.size();i_2++){
                const Tuple* tuple2;
                bool undef2=false;
                if(i_2<tuples2.size())                    tuple2=tuples2[i_2];
                else{
                    tuple2=tuplesU2[i_2-tuples2.size()];
                    undef2=true;
                }
                if(tuple2->at(0) == tuple2->at(1)){
                    int X = tuple2->at(2);
                    const Tuple negativeTuple3({X,Z},&_a,true);
                    const Tuple* tuple3 = ua.find(Tuple({X,Z},&_a));
                    bool undef3 = false;
                    if(tuple3!=NULL){
                        undef3 = true;
                    }else if(wa.find(negativeTuple3)==NULL){
                        tuple3=&negativeTuple3;
                    }
                    if(tuple3!=NULL){
                        Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                        {
                            std::vector<int> aggrKey({t[6],t[2],t[0]});
                            if(aggrKey[0]>0){
                                if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                    if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
                            }else{
                                if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                    if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int Y = tuple[0];
        int V = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_.getValues({Y,V});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuples.back());
                if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_.getValues({Y,V});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesN.back());
                if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& reas = negativeAggrReason[0][{}];
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
        const std::vector<const Tuple*>& tuples0 = pa_.getValues({});
        const std::vector<const Tuple*>& tuplesU0 = ua_.getValues({});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int W = tuple0->at(0);
            int Z = tuple0->at(1);
            const std::vector<const Tuple*>& tuples2 = pc_0_1_.getValues({Z,Z});
            const std::vector<const Tuple*>& tuplesU2 = uc_0_1_.getValues({Z,Z});
            for(int i_2=0;i_2<tuples2.size()+tuplesU2.size();i_2++){
                const Tuple* tuple2;
                bool undef2=false;
                if(i_2<tuples2.size())                    tuple2=tuples2[i_2];
                else{
                    tuple2=tuplesU2[i_2-tuples2.size()];
                    undef2=true;
                }
                if(tuple2->at(0) == tuple2->at(1)){
                    int X = tuple2->at(2);
                    const Tuple negativeTuple3({X,Z},&_a,true);
                    const Tuple* tuple3 = ua.find(Tuple({X,Z},&_a));
                    bool undef3 = false;
                    if(tuple3!=NULL){
                        undef3 = true;
                    }else if(wa.find(negativeTuple3)==NULL){
                        tuple3=&negativeTuple3;
                    }
                    if(tuple3!=NULL){
                        Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                        {
                            std::vector<int> aggrKey({t[6],t[2],t[0]});
                            if(aggrKey[0]>0){
                                if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                    if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
                            }else{
                                if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                    if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_c && tuple.size()==3){
        if(tuple.at(0) == tuple.at(1)){
            int Z = tuple[0];
            int X = tuple[2];
            if(var > 0){
                const std::vector<const Tuple*>& tuples = p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_.getValues({Z,Z,X});
                while(!tuples.empty()){
                    Tuple t(*tuples.back());
                    wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuples.back());
                    if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                        const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[6],t[2],t[0]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
                const std::vector<const Tuple*>& tuplesN = np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_.getValues({Z,Z,X});
                while(!tuplesN.empty()){
                    Tuple t(*tuplesN.back());
                    nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesN.back());
                    if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                        const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[6],t[2],t[0]});
                            if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& reas = negativeAggrReason[0][{}];
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
            const std::vector<const Tuple*>& tuples0 = pa_1_.getValues({Z});
            const std::vector<const Tuple*>& tuplesU0 = ua_1_.getValues({Z});
            for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
                const Tuple* tuple0;
                bool undef0=false;
                if(i_0<tuples0.size())                    tuple0=tuples0[i_0];
                else{
                    tuple0=tuplesU0[i_0-tuples0.size()];
                    undef0=true;
                }
                int W = tuple0->at(0);
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
                    int V = tuple1->at(1);
                    const Tuple negativeTuple3({X,Z},&_a,true);
                    const Tuple* tuple3 = ua.find(Tuple({X,Z},&_a));
                    bool undef3 = false;
                    if(tuple3!=NULL){
                        undef3 = true;
                    }else if(wa.find(negativeTuple3)==NULL){
                        tuple3=&negativeTuple3;
                    }
                    if(tuple3!=NULL){
                        Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                        {
                            std::vector<int> aggrKey({t[6],t[2],t[0]});
                            if(aggrKey[0]>0){
                                if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                    if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
                            }else{
                                if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                    if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                        nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                    const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{}];
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int X = tuple[0];
        int Z = tuple[1];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_.getValues({X,Z});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuples.back());
                if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        auto& trueSet = trueAggrVars[0][{}];
                        auto& undefSet = undefAggrVars[0][{}];
                        if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_.getValues({X,Z});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(*tuplesN.back());
                if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& reas = negativeAggrReason[0][{}];
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
        const std::vector<const Tuple*>& tuples0 = pa_1_.getValues({Z});
        const std::vector<const Tuple*>& tuplesU0 = ua_1_.getValues({Z});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int W = tuple0->at(0);
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
                int V = tuple1->at(1);
                const Tuple* tuple2 = wc.find(Tuple({Z,Z,X},&_c));
                bool undef2 = false;
                if(tuple2==NULL){
                    tuple2 = uc.find(Tuple({Z,Z,X},&_c));
                    undef2 = true;
                }
                if(tuple2!=NULL){
                    Tuple t({W,Z,Y,V,Z,Z,X,X,Z},&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
                    {
                        std::vector<int> aggrKey({t[6],t[2],t[0]});
                        if(aggrKey[0]>0){
                            if(ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                if(wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                    wa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                const auto& insertResult = ua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
                        }else{
                            if(nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(Tuple(t))==NULL){
                                if(nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.find(t))
                                    nwa_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.erase(t);
                                const auto& insertResult = nua_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            if(np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({aggrKey}).size()<=0){
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
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_c]=&wc;
    predicateFSetMap[&_c]=&fc;
    predicateUSetMap[&_c]=&uc;
    stringToUniqueStringPointer["c"] = &_c;
    predicateWSetMap[&_a]=&wa;
    predicateFSetMap[&_a]=&fa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_);
    predicateToAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&p_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_0_1_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_0_1_2_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_1_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_1_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_);
    predicateToNegativeAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&np_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_);
    predicateToUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_0_1_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_1_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_0_1_6_2_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_2_3_6_2_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_4_5_6_6_2_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_].push_back(&nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_7_8_6_2_0_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_0_1_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_0_1_2_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_0_1_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_1_);
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
                //2
                if(!(undefPlusTrue>=2+maxPossibleNegativeSum[0][{}])){
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::cout<<"propagation started from Aggr"<<std::endl;
                        std::cout<<"conflict detected on propagator Ending with aggr"<<std::endl;
                        propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});
                    }else{
                        const auto & it = tupleToVar.find(*tupleU);
                        if(it != tupleToVar.end()) {
                            int sign = tupleUNegated ? -1 : 1;
                            propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;
                        }
                    }
                }//close aggr true if
                bool propagated=false;
                {
                    tupleU=NULL;
                    if(tupleU == NULL){
                        std::cout<<undefPlusTrue<<std::endl;
                        for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                            if(undefPlusTrue-undefKey->at(0)>=2+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues(*undefKey);
                                if(undefinedTuples->size()==1){

                                    const Tuple* tuple0 = ua.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a));
                                    if(tuple0!=NULL){
                                        const auto & it0 = tupleToVar.find(*tuple0);
                                        if(it0 != tupleToVar.end()) {
                                            propagated=true;
                                            std::cout<<"Propagation Negated";tuple0->print();std::cout<<std::endl;
                                            int sign = -1;
                                            propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>()}).first->second;
                                        }
                                    }
                                    const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                    if(tuple1!=NULL){
                                        const auto & it1 = tupleToVar.find(*tuple1);
                                        if(it1 != tupleToVar.end()) {
                                            propagated=true;
                                            std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                            int sign = -1;
                                            propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
                                        }
                                    }
                                    const Tuple* tuple2 = uc.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5),undefinedTuples->at(0)->at(6)},&_c));
                                    if(tuple2!=NULL){
                                        const auto & it2 = tupleToVar.find(*tuple2);
                                        if(it2 != tupleToVar.end()) {
                                            propagated=true;
                                            std::cout<<"Propagation Negated";tuple2->print();std::cout<<std::endl;
                                            int sign = -1;
                                            propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>()}).first->second;
                                        }
                                    }
                                    const Tuple* tuple3 = ua.find(Tuple({undefinedTuples->at(0)->at(7),undefinedTuples->at(0)->at(8)},&_a));
                                    if(tuple3!=NULL){
                                        const auto & it3 = tupleToVar.find(*tuple3);
                                        if(it3 != tupleToVar.end()) {
                                            propagated=true;
                                            std::cout<<"Propagation Negated";tuple3->print();std::cout<<std::endl;
                                            int sign = 1;
                                            propagatedLiteralsAndReasons.insert({it3->second*sign, std::vector<int>()}).first->second;
                                        }
                                    }
                                }
                            }
                        }
                        for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                            if(undefPlusTrue+undefKey->at(0)>=2+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({undefKey->at(0),undefKey->at(1),undefKey->at(2)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                    bool negativeJoinPropagated=false;
                                    const Tuple* tupleU0 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a));
                                    if(tupleU0!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                        if(wa.find(tuple1)!=NULL){
                                            const auto & it1 = tupleToVar.find(tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                reas.push_back(it1->second);
                                            }
                                            Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c);
                                            if(wc.find(tuple2)!=NULL){
                                                const auto & it2 = tupleToVar.find(tuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    reas.push_back(it2->second);
                                                }
                                                Tuple tuple3 ({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a);
                                                if(wa.find(tuple3)==NULL && ua.find(tuple3)==NULL){
                                                    const auto & it3 = tupleToVar.find(tuple3);
                                                    if(it3 != tupleToVar.end()) {
                                                        reas.push_back(it3->second*-1);
                                                    }
                                                    const auto & it0 = tupleToVar.find(*tupleU0);
                                                    if(it0 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        std::cout<<"Propagation Negated Negative join";tupleU0->print();std::cout<<std::endl;
                                                        int sign = 1;
                                                        propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>()}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                    if(tupleU1!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a);
                                        if(wa.find(tuple0)!=NULL){
                                            const auto & it0 = tupleToVar.find(tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c);
                                            if(wc.find(tuple2)!=NULL){
                                                const auto & it2 = tupleToVar.find(tuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    reas.push_back(it2->second);
                                                }
                                                Tuple tuple3 ({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a);
                                                if(wa.find(tuple3)==NULL && ua.find(tuple3)==NULL){
                                                    const auto & it3 = tupleToVar.find(tuple3);
                                                    if(it3 != tupleToVar.end()) {
                                                        reas.push_back(it3->second*-1);
                                                    }
                                                    const auto & it1 = tupleToVar.find(*tupleU1);
                                                    if(it1 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        std::cout<<"Propagation Negated Negative join";tupleU1->print();std::cout<<std::endl;
                                                        int sign = 1;
                                                        propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    const Tuple* tupleU2 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c));
                                    if(tupleU2!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a);
                                        if(wa.find(tuple0)!=NULL){
                                            const auto & it0 = tupleToVar.find(tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if(wa.find(tuple1)!=NULL){
                                                const auto & it1 = tupleToVar.find(tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple tuple3 ({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a);
                                                if(wa.find(tuple3)==NULL && ua.find(tuple3)==NULL){
                                                    const auto & it3 = tupleToVar.find(tuple3);
                                                    if(it3 != tupleToVar.end()) {
                                                        reas.push_back(it3->second*-1);
                                                    }
                                                    const auto & it2 = tupleToVar.find(*tupleU2);
                                                    if(it2 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        std::cout<<"Propagation Negated Negative join";tupleU2->print();std::cout<<std::endl;
                                                        int sign = 1;
                                                        propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>()}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    const Tuple* tupleU3 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a));
                                    if(tupleU3!=NULL && !negativeJoinPropagated){
                                        std::vector<int> reas;
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a);
                                        if(wa.find(tuple0)!=NULL){
                                            const auto & it0 = tupleToVar.find(tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                reas.push_back(it0->second);
                                            }
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if(wa.find(tuple1)!=NULL){
                                                const auto & it1 = tupleToVar.find(tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c);
                                                if(wc.find(tuple2)!=NULL){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                    const auto & it3 = tupleToVar.find(*tupleU3);
                                                    if(it3 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        std::cout<<"Propagation Negated Negative join";tupleU3->print();std::cout<<std::endl;
                                                        int sign = -1;
                                                        propagatedLiteralsAndReasons.insert({it3->second*sign, std::vector<int>()}).first->second;
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
                if(!propagated){
                    tupleU=NULL;
                    if(tupleU == NULL){
                    }
                }//close prop multi join
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
            if(starter.getPredicateName()== &_a || starter.getPredicateName()== &_a || starter.getPredicateName()== &_c || starter.getPredicateName()== &_a){
                {
                    int undefPlusTrue = actualSum[0][{}]+possibleSum[0][{}]+actualNegativeSum[0][{}]+possibleNegativeSum[0][{}];
                    //2
                    if(!(undefPlusTrue>=2+maxPossibleNegativeSum[0][{}])){
                        tupleU=NULL;
                        std::vector<int> local_reason;
                        local_reason.insert(local_reason.end(),negativeAggrReason[0][{}].begin(), negativeAggrReason[0][{}].end());
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
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                            }
                        }
                    }//close aggr true if
                    bool propagated=false;
                    {
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[0][{}].begin(), negativeAggrReason[0][{}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            std::cout<<undefPlusTrue<<std::endl;
                            for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                if(undefPlusTrue-undefKey->at(0)>=2+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues(*undefKey);
                                    if(undefinedTuples->size()==1){

                                        const Tuple* tuple0 = ua.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a));
                                        if(tuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"propagation reason";
                                                for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                std::cout<<std::endl;
                                                std::cout<<"Propagation Negated";tuple0->print();std::cout<<std::endl;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                            }
                                        }
                                        const Tuple* tuple1 = ua.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_a));
                                        if(tuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"propagation reason";
                                                for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                std::cout<<std::endl;
                                                std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                            }
                                        }
                                        const Tuple* tuple2 = uc.find(Tuple({undefinedTuples->at(0)->at(4),undefinedTuples->at(0)->at(5),undefinedTuples->at(0)->at(6)},&_c));
                                        if(tuple2!=NULL){
                                            const auto & it2 = tupleToVar.find(*tuple2);
                                            if(it2 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"propagation reason";
                                                for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                std::cout<<std::endl;
                                                std::cout<<"Propagation Negated";tuple2->print();std::cout<<std::endl;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>(local_reason)}).first->second;
                                            }
                                        }
                                        const Tuple* tuple3 = ua.find(Tuple({undefinedTuples->at(0)->at(7),undefinedTuples->at(0)->at(8)},&_a));
                                        if(tuple3!=NULL){
                                            const auto & it3 = tupleToVar.find(*tuple3);
                                            if(it3 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"propagation reason";
                                                for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                std::cout<<std::endl;
                                                std::cout<<"Propagation Negated";tuple3->print();std::cout<<std::endl;
                                                int sign = 1;
                                                propagatedLiteralsAndReasons.insert({it3->second*sign, std::vector<int>(local_reason)}).first->second;
                                            }
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{}].rbegin();undefKey!=undefNegativeAggrVars[0][{}].rend();undefKey++){
                                if(undefPlusTrue+undefKey->at(0)>=2+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_a_W_Z_a_Y_V_c_Z_Z_X_not_a_X_Z_6_2_0_.getValues({undefKey->at(0),undefKey->at(1),undefKey->at(2)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* tupleU0 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a));
                                        if(tupleU0!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                            if(wa.find(tuple1)!=NULL){
                                                const auto & it1 = tupleToVar.find(tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    reas.push_back(it1->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c);
                                                if(wc.find(tuple2)!=NULL){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                    Tuple tuple3 ({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a);
                                                    if(wa.find(tuple3)==NULL && ua.find(tuple3)==NULL){
                                                        const auto & it3 = tupleToVar.find(tuple3);
                                                        if(it3 != tupleToVar.end()) {
                                                            reas.push_back(it3->second*-1);
                                                        }
                                                        const auto & it0 = tupleToVar.find(*tupleU0);
                                                        if(it0 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            for(int v: reas){ local_reason.push_back(v); }
                                                            std::cout<<"propagation reason";
                                                            for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                            std::cout<<std::endl;
                                                            std::cout<<"Propagation Negated Negative join";tupleU0->print();std::cout<<std::endl;
                                                            int sign = 1;
                                                            propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                            while(!reas.empty()){ local_reason.pop_back(); reas.pop_back();}
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* tupleU1 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a));
                                        if(tupleU1!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a);
                                            if(wa.find(tuple0)!=NULL){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c);
                                                if(wc.find(tuple2)!=NULL){
                                                    const auto & it2 = tupleToVar.find(tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        reas.push_back(it2->second);
                                                    }
                                                    Tuple tuple3 ({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a);
                                                    if(wa.find(tuple3)==NULL && ua.find(tuple3)==NULL){
                                                        const auto & it3 = tupleToVar.find(tuple3);
                                                        if(it3 != tupleToVar.end()) {
                                                            reas.push_back(it3->second*-1);
                                                        }
                                                        const auto & it1 = tupleToVar.find(*tupleU1);
                                                        if(it1 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            for(int v: reas){ local_reason.push_back(v); }
                                                            std::cout<<"propagation reason";
                                                            for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                            std::cout<<std::endl;
                                                            std::cout<<"Propagation Negated Negative join";tupleU1->print();std::cout<<std::endl;
                                                            int sign = 1;
                                                            propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                            while(!reas.empty()){ local_reason.pop_back(); reas.pop_back();}
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* tupleU2 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c));
                                        if(tupleU2!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a);
                                            if(wa.find(tuple0)!=NULL){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if(wa.find(tuple1)!=NULL){
                                                    const auto & it1 = tupleToVar.find(tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second);
                                                    }
                                                    Tuple tuple3 ({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a);
                                                    if(wa.find(tuple3)==NULL && ua.find(tuple3)==NULL){
                                                        const auto & it3 = tupleToVar.find(tuple3);
                                                        if(it3 != tupleToVar.end()) {
                                                            reas.push_back(it3->second*-1);
                                                        }
                                                        const auto & it2 = tupleToVar.find(*tupleU2);
                                                        if(it2 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            for(int v: reas){ local_reason.push_back(v); }
                                                            std::cout<<"propagation reason";
                                                            for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                            std::cout<<std::endl;
                                                            std::cout<<"Propagation Negated Negative join";tupleU2->print();std::cout<<std::endl;
                                                            int sign = 1;
                                                            propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>(local_reason)}).first->second;
                                                            while(!reas.empty()){ local_reason.pop_back(); reas.pop_back();}
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* tupleU3 = ua.find(Tuple({undefinedTuples->at(iUndef)->at(7),undefinedTuples->at(iUndef)->at(8)},&_a));
                                        if(tupleU3!=NULL && !negativeJoinPropagated){
                                            std::vector<int> reas;
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_a);
                                            if(wa.find(tuple0)!=NULL){
                                                const auto & it0 = tupleToVar.find(tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    reas.push_back(it0->second);
                                                }
                                                Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_a);
                                                if(wa.find(tuple1)!=NULL){
                                                    const auto & it1 = tupleToVar.find(tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second);
                                                    }
                                                    Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4),undefinedTuples->at(iUndef)->at(5),undefinedTuples->at(iUndef)->at(6)},&_c);
                                                    if(wc.find(tuple2)!=NULL){
                                                        const auto & it2 = tupleToVar.find(tuple2);
                                                        if(it2 != tupleToVar.end()) {
                                                            reas.push_back(it2->second);
                                                        }
                                                        const auto & it3 = tupleToVar.find(*tupleU3);
                                                        if(it3 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            for(int v: reas){ local_reason.push_back(v); }
                                                            std::cout<<"propagation reason";
                                                            for(int v : local_reason) {if (v < 0){ std::cout<<"-"; v*=-1;}atomsTable[v].print();}
                                                            std::cout<<std::endl;
                                                            std::cout<<"Propagation Negated Negative join";tupleU3->print();std::cout<<std::endl;
                                                            int sign = -1;
                                                            propagatedLiteralsAndReasons.insert({it3->second*sign, std::vector<int>(local_reason)}).first->second;
                                                            while(!reas.empty()){ local_reason.pop_back(); reas.pop_back();}
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
                    if(!propagated){
                        tupleU=NULL;
                        if(tupleU == NULL){
                        }
                    }//close prop multi join
                }
            }
        }//local scope
    }
}
}
