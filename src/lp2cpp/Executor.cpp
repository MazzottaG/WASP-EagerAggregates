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
PredicateWSet wa(1);
PredicateWSet ua(1);
PredicateWSet fa(1);
const std::string _b = "b";
PredicateWSet wb(3);
PredicateWSet ub(3);
PredicateWSet fb(3);
const std::string _c = "c";
PredicateWSet wc(2);
PredicateWSet uc(2);
PredicateWSet fc(2);
const std::string _b_V_Z_U_not_c_U_V_not_a_Z_ = "b_V_Z_U_not_c_U_V_not_a_Z_";
PredicateWSet wb_V_Z_U_not_c_U_V_not_a_Z_(6);
PredicateWSet ub_V_Z_U_not_c_U_V_not_a_Z_(6);
PredicateWSet nwb_V_Z_U_not_c_U_V_not_a_Z_(6);
PredicateWSet nub_V_Z_U_not_c_U_V_not_a_Z_(6);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_1;
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueNegativeAggrVars[1];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefNegativeAggrVars[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> maxPossibleNegativeSum[1];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason[1];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> actualSum[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleSum[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> actualNegativeSum[1];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleNegativeSum[1];
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
AuxMap pc_0_1_({0,1});
AuxMap uc_0_1_({0,1});
AuxMap fc_0_1_({0,1});
AuxMap pa_0_({0});
AuxMap ua_0_({0});
AuxMap fa_0_({0});
AuxMap pc_({});
AuxMap uc_({});
AuxMap fc_({});
AuxMap pb_0_2_({0,2});
AuxMap ub_0_2_({0,2});
AuxMap fb_0_2_({0,2});
AuxMap pa_({});
AuxMap ua_({});
AuxMap fa_({});
AuxMap pb_1_({1});
AuxMap ub_1_({1});
AuxMap fb_1_({1});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_0_({0});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_0_({0});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_0_({0});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_0_({0});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_({});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_({});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_({});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_({});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_({2,3});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_({2,3});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_({2,3});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_({2,3});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_({2,3,0});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_({2,3,0});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_({2,3,0});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_({2,3,0});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_({2,3,0,1,2});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_({2,3,0,1,2});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_({2,3,0,1,2});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_({2,3,0,1,2});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_({2,3,3,4});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_({2,3,3,4});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_({2,3,3,4});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_({2,3,3,4});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_({2,3,5});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_({2,3,5});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_({2,3,5});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_({2,3,5});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_({0,1,2});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_({0,1,2});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_({0,1,2});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_({0,1,2});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_({0,1,2,2,3});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_({0,1,2,2,3});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_({0,1,2,2,3});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_({0,1,2,2,3});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_({0,1,2,2,3,0});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_({0,1,2,2,3,0});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_({0,1,2,2,3,0});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_({0,1,2,2,3,0});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_({3,4});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_({3,4});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_({3,4});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_({3,4});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_({3,4,2,3});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_({3,4,2,3});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_({3,4,2,3});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_({3,4,2,3});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_({3,4,2,3,0});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_({3,4,2,3,0});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_({3,4,2,3,0});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_({3,4,2,3,0});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_5_({5});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_5_({5});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_5_({5});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_5_({5});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_({5,2,3});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_({5,2,3});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_({5,2,3});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_({5,2,3});
AuxMap p_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_({5,2,3,0});
AuxMap u_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_({5,2,3,0});
AuxMap np_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_({5,2,3,0});
AuxMap nu_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_({5,2,3,0});
AuxMap pb_2_({2});
AuxMap ub_2_({2});
AuxMap fb_2_({2});
AuxMap pc_0_({0});
AuxMap uc_0_({0});
AuxMap fc_0_({0});
AuxMap pb_1_2_({1,2});
AuxMap ub_1_2_({1,2});
AuxMap fb_1_2_({1,2});
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
    if(var<0 && ( tuple.getPredicateName() == &_a || tuple.getPredicateName() == &_b || tuple.getPredicateName() == &_c)){
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
    if(tuple.getPredicateName() == &_b){
        int V = tuple[0];
        int Z = tuple[1];
        int U = tuple[2];
        if(var > 0){
            bool negative_join=false;
            bool positive_join=false;
            const Tuple negativeTuple1({U,V},&_c,true);
            const Tuple* tuple1 = uc.find(Tuple({U,V},&_c));
            if(wc.find(negativeTuple1)==NULL && tuple1==NULL){
                tuple1=&negativeTuple1;
                const Tuple negativeTuple2({Z},&_a,true);
                const Tuple* tuple2 = ua.find(Tuple({Z},&_a));
                if(wa.find(negativeTuple2)==NULL && tuple2==NULL){
                    tuple2=&negativeTuple2;
                    Tuple t({V,Z,U,U,V,Z},&_b_V_Z_U_not_c_U_V_not_a_Z_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]>0){
                            if(wb_V_Z_U_not_c_U_V_not_a_Z_.find(t)==NULL){
                                if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(t))
                                    ub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                                const auto& insertResult = wb_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{U,U}];
                            auto& undefSet = undefAggrVars[0][{U,U}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleSum[0][{U,U}]-=aggrKey[0];
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                                actualSum[0][{U,U}]+=aggrKey[0];
                                auto& reas = positiveAggrReason[0][{U,U}];
                                if(reas.level(var)==-1){
                                    reas.addLevel();
                                    reas.insert(var);
                                    tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        tuple1->print();std::cout<<"Added to positive reason"<<std::endl;
                                        reas.insert(it->second*-1);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple2);
                                    if(it != tupleToVar.end()) {
                                        tuple2->print();std::cout<<"Added to positive reason"<<std::endl;
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }else{
                            if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(t)){
                                nub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                                auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                                if(nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                    aggrKey[0]*=-1;
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                        possibleNegativeSum[0][{U,U}]-=aggrKey[0];
                                    }
                                }
                                auto& reas = negativeAggrReason[0][{U,U}];
                                if(reas.level(var)==-1){
                                    reas.addLevel();
                                    reas.insert(var);
                                    tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        tuple1->print();std::cout<<"Added to negative reason"<<std::endl;
                                        reas.insert(it->second*-1);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple2);
                                    if(it != tupleToVar.end()) {
                                        tuple2->print();std::cout<<"Added to negative reason"<<std::endl;
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_.getValues({V,Z,U});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_V_Z_U_not_c_U_V_not_a_Z_.erase(*tuplesU.back());
                {
                    //bound var2
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefAggrVars[0][{U,U}];
                    if(u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{U,U}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{U,U}];
                    if(reas.level(var)==-1){
                        reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_.getValues({V,Z,U});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                const auto& insertResult = nwb_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    //bound var2
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                    auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                        possibleNegativeSum[0][{U,U}]-=aggrKey[0];
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                        actualNegativeSum[0][{U,U}]+=aggrKey[0];
                        auto& reas = positiveAggrReason[0][{U,U}];
                        if(reas.level(var)==-1){
                            reas.addLevel();
                            reas.insert(var);
                            tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_c){
        int U = tuple[0];
        int V = tuple[1];
        if(var < 0){
            bool negative_join=false;
            bool positive_join=false;
            const std::vector<const Tuple*>* tuples0 = &pb_0_2_.getValues({V,U});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int Z = tuple0->at(1);
                const Tuple negativeTuple2({Z},&_a,true);
                const Tuple* tuple2 = ua.find(Tuple({Z},&_a));
                if(wa.find(negativeTuple2)==NULL && tuple2==NULL){
                    tuple2=&negativeTuple2;
                    Tuple t({V,Z,U,U,V,Z},&_b_V_Z_U_not_c_U_V_not_a_Z_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]>0){
                            if(wb_V_Z_U_not_c_U_V_not_a_Z_.find(t)==NULL){
                                if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(t))
                                    ub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                                const auto& insertResult = wb_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{U,U}];
                            auto& undefSet = undefAggrVars[0][{U,U}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleSum[0][{U,U}]-=aggrKey[0];
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                                actualSum[0][{U,U}]+=aggrKey[0];
                                auto& reas = positiveAggrReason[0][{U,U}];
                                if(reas.level(var)==-1){
                                    reas.addLevel();
                                    reas.insert(var);
                                    tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                }
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
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }else{
                            if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(t)){
                                nub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                                auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                                if(nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                    aggrKey[0]*=-1;
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                        possibleNegativeSum[0][{U,U}]-=aggrKey[0];
                                    }
                                }
                                auto& reas = negativeAggrReason[0][{U,U}];
                                if(reas.level(var)==-1){
                                    reas.addLevel();
                                    reas.insert(var);
                                    tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple0);
                                    if(it != tupleToVar.end()) {
                                        tuple0->print();std::cout<<"Added to negative reason"<<std::endl;
                                        reas.insert(it->second);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple2);
                                    if(it != tupleToVar.end()) {
                                        tuple2->print();std::cout<<"Added to negative reason"<<std::endl;
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_.getValues({U,V});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_V_Z_U_not_c_U_V_not_a_Z_.erase(*tuplesU.back());
                {
                    //bound var2
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefAggrVars[0][{U,U}];
                    if(u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{U,U}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{U,U}];
                    if(reas.level(var)==-1){
                        reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_.getValues({U,V});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                const auto& insertResult = nwb_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    //bound var2
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                    auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                        possibleNegativeSum[0][{U,U}]-=aggrKey[0];
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                        actualNegativeSum[0][{U,U}]+=aggrKey[0];
                        auto& reas = positiveAggrReason[0][{U,U}];
                        if(reas.level(var)==-1){
                            reas.addLevel();
                            reas.insert(var);
                            tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_a){
        int Z = tuple[0];
        if(var < 0){
            bool negative_join=false;
            bool positive_join=false;
            const std::vector<const Tuple*>* tuples0 = &pb_1_.getValues({Z});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int V = tuple0->at(0);
                int U = tuple0->at(2);
                const Tuple negativeTuple1({U,V},&_c,true);
                const Tuple* tuple1 = uc.find(Tuple({U,V},&_c));
                if(wc.find(negativeTuple1)==NULL && tuple1==NULL){
                    tuple1=&negativeTuple1;
                    Tuple t({V,Z,U,U,V,Z},&_b_V_Z_U_not_c_U_V_not_a_Z_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]>0){
                            if(wb_V_Z_U_not_c_U_V_not_a_Z_.find(t)==NULL){
                                if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(t))
                                    ub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                                const auto& insertResult = wb_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{U,U}];
                            auto& undefSet = undefAggrVars[0][{U,U}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                                possibleSum[0][{U,U}]-=aggrKey[0];
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                                actualSum[0][{U,U}]+=aggrKey[0];
                                auto& reas = positiveAggrReason[0][{U,U}];
                                if(reas.level(var)==-1){
                                    reas.addLevel();
                                    reas.insert(var);
                                    tuple.print();std::cout<<"Added to positive reason"<<std::endl;
                                }
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
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }else{
                            if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(t)){
                                nub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                                auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                                if(nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                    aggrKey[0]*=-1;
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                        possibleNegativeSum[0][{U,U}]-=aggrKey[0];
                                    }
                                }
                                auto& reas = negativeAggrReason[0][{U,U}];
                                if(reas.level(var)==-1){
                                    reas.addLevel();
                                    reas.insert(var);
                                    tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple0);
                                    if(it != tupleToVar.end()) {
                                        tuple0->print();std::cout<<"Added to negative reason"<<std::endl;
                                        reas.insert(it->second);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        tuple1->print();std::cout<<"Added to negative reason"<<std::endl;
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_b_V_Z_U_not_c_U_V_not_a_Z_5_.getValues({Z});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ub_V_Z_U_not_c_U_V_not_a_Z_.erase(*tuplesU.back());
                {
                    int U = t[2];
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefAggrVars[0][{U,U}];
                    if(u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{U,U}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{U,U}];
                    if(reas.level(var)==-1){
                        reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_b_V_Z_U_not_c_U_V_not_a_Z_5_.getValues({Z});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nub_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                const auto& insertResult = nwb_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    int U = t[2];
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                    auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                        possibleNegativeSum[0][{U,U}]-=aggrKey[0];
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                        actualNegativeSum[0][{U,U}]+=aggrKey[0];
                        auto& reas = positiveAggrReason[0][{U,U}];
                        if(reas.level(var)==-1){
                            reas.addLevel();
                            reas.insert(var);
                            tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                        }
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_a){
        int U = tuple.at(0);
        {
            if(!sharedVariables_0_ToAggregate_1.count({U,U})){
                sharedVariables_0_ToAggregate_1.insert({U,U});
            }
        }
    }
    std::cout<<"Negative aggr reason: "<<negativeAggrReason[0][{}].size()<<std::endl;
    std::cout<<"Positive aggr reason: "<<positiveAggrReason[0][{}].size()<<std::endl;
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
    if(var<0 && ( tuple.getPredicateName() == &_a || tuple.getPredicateName() == &_b || tuple.getPredicateName() == &_c)){
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
    if(tuple.getPredicateName() == &_b && tuple.size()==3){
        int V = tuple[0];
        int Z = tuple[1];
        int U = tuple[2];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_.getValues({V,Z,U});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_V_Z_U_not_c_U_V_not_a_Z_.erase(*tuples.back());
                if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueAggrVars[0][{U,U}];
                            auto& undefSet = undefAggrVars[0][{U,U}];
                            if(p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualSum[0][{U,U}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{U,U}];
                                    int starter_level=reas.level(var);
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[3],t[4]},&_c));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[5]},&_a));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleSum[0][{U,U}]+=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesNegative = np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_.getValues({V,Z,U});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[3],t[4]},&_c);
                if(wc.find(literal)==NULL){
                    Tuple literal({t[5]},&_a);
                    if(wa.find(literal)==NULL){
                        nwb_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                        if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(t)==NULL){
                            const auto& insertResult = nub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                            auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                            std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                            if(np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                aggrKey[0]*=-1;
                                std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualNegativeSum[0][{U,U}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{U,U}];
                                    reas.erase(var,reas.level(var));
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{U,U}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{U,U}];
                                        if(sum > maxPossibleNegativeSum[0][{U,U}])
                                            maxPossibleNegativeSum[0][{U,U}]=sum;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        const Tuple negativeTuple1({U,V},&_c,true);
        const Tuple* tuple1 = uc.find(Tuple({U,V},&_c));
        bool undef1 = false;
        if(tuple1!=NULL){
            undef1 = true;
        }else if(wc.find(negativeTuple1)==NULL){
            tuple1=&negativeTuple1;
        }
        if(tuple1!=NULL){
            const Tuple negativeTuple2({Z},&_a,true);
            const Tuple* tuple2 = ua.find(Tuple({Z},&_a));
            bool undef2 = false;
            if(tuple2!=NULL){
                undef2 = true;
            }else if(wa.find(negativeTuple2)==NULL){
                tuple2=&negativeTuple2;
            }
            if(tuple2!=NULL){
                Tuple t({V,Z,U,U,V,Z},&_b_V_Z_U_not_c_U_V_not_a_Z_);
                {
                    std::vector<int> aggrKey({t[0]});
                    if(aggrKey[0]>0){
                        if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t))==NULL){
                            if(wb_V_Z_U_not_c_U_V_not_a_Z_.find(t))
                                wb_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                            const auto& insertResult = ub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueAggrVars[0][{U,U}];
                        auto& undefSet = undefAggrVars[0][{U,U}];
                        if(p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{U,U}]-=aggrKey[0];
                                auto& reas = positiveAggrReason[0][{U,U}];
                                int starter_level=reas.level(var);
                                reas.erase(var,reas.level(var));
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        std::cout<<"Erasing from reason";tuple1->print();std::cout<<std::endl;
                                        reas.erase(-1*it->second,starter_level);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple2);
                                    if(it != tupleToVar.end()) {
                                        std::cout<<"Erasing from reason";tuple2->print();std::cout<<std::endl;
                                        reas.erase(-1*it->second,starter_level);
                                    }
                                }
                            }
                        }
                        if(undefSet.find(aggrKey)==undefSet.end()){
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                undefSet.insert(aggrKey);
                                possibleSum[0][{U,U}]+=aggrKey[0];
                            }
                        }
                    }else{
                        if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t))==NULL){
                            const auto& insertResult = nub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                                auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                                aggrKey[0]*=-1;
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{U,U}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{U,U}];
                                        if(sum > maxPossibleNegativeSum[0][{U,U}])
                                            maxPossibleNegativeSum[0][{U,U}]=sum;
                                    }
                                }
                                if(var > 0 && !undef1 && !undef2){
                                    auto& reas = negativeAggrReason[0][{U,U}];
                                    int starter_level=reas.level(var);
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            std::cout<<"Erasing from reason";tuple1->print();std::cout<<std::endl;
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple2);
                                        if(it != tupleToVar.end()) {
                                            std::cout<<"Erasing from reason";tuple2->print();std::cout<<std::endl;
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for(auto& pair : negativeAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
        for(auto& pair : positiveAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
    }
    if(tuple.getPredicateName() == &_c && tuple.size()==2){
        int U = tuple[0];
        int V = tuple[1];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_.getValues({U,V});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_V_Z_U_not_c_U_V_not_a_Z_.erase(*tuples.back());
                if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueAggrVars[0][{U,U}];
                            auto& undefSet = undefAggrVars[0][{U,U}];
                            if(p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualSum[0][{U,U}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{U,U}];
                                    int starter_level=reas.level(var);
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[0],t[1],t[2]},&_b));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[5]},&_a));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleSum[0][{U,U}]+=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesNegative = np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_.getValues({U,V});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[0],t[1],t[2]},&_b);
                if(ub.find(literal)!=NULL || wb.find(literal)!=NULL){
                    Tuple literal({t[5]},&_a);
                    if(wa.find(literal)==NULL){
                        nwb_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                        if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(t)==NULL){
                            const auto& insertResult = nub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                            auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                            std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                            if(np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                aggrKey[0]*=-1;
                                std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualNegativeSum[0][{U,U}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{U,U}];
                                    reas.erase(var,reas.level(var));
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{U,U}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{U,U}];
                                        if(sum > maxPossibleNegativeSum[0][{U,U}])
                                            maxPossibleNegativeSum[0][{U,U}]=sum;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        const std::vector<const Tuple*>& tuples0 = pb_0_2_.getValues({V,U});
        const std::vector<const Tuple*>& tuplesU0 = ub_0_2_.getValues({V,U});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int Z = tuple0->at(1);
            const Tuple negativeTuple2({Z},&_a,true);
            const Tuple* tuple2 = ua.find(Tuple({Z},&_a));
            bool undef2 = false;
            if(tuple2!=NULL){
                undef2 = true;
            }else if(wa.find(negativeTuple2)==NULL){
                tuple2=&negativeTuple2;
            }
            if(tuple2!=NULL){
                Tuple t({V,Z,U,U,V,Z},&_b_V_Z_U_not_c_U_V_not_a_Z_);
                {
                    std::vector<int> aggrKey({t[0]});
                    if(aggrKey[0]>0){
                        if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t))==NULL){
                            if(wb_V_Z_U_not_c_U_V_not_a_Z_.find(t))
                                wb_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                            const auto& insertResult = ub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueAggrVars[0][{U,U}];
                        auto& undefSet = undefAggrVars[0][{U,U}];
                        if(p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{U,U}]-=aggrKey[0];
                                auto& reas = positiveAggrReason[0][{U,U}];
                                int starter_level=reas.level(var);
                                reas.erase(var,reas.level(var));
                                {
                                    const auto & it = tupleToVar.find(*tuple0);
                                    if(it != tupleToVar.end()) {
                                        std::cout<<"Erasing from reason";tuple0->print();std::cout<<std::endl;
                                        reas.erase(it->second,starter_level);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple2);
                                    if(it != tupleToVar.end()) {
                                        std::cout<<"Erasing from reason";tuple2->print();std::cout<<std::endl;
                                        reas.erase(-1*it->second,starter_level);
                                    }
                                }
                            }
                        }
                        if(undefSet.find(aggrKey)==undefSet.end()){
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                undefSet.insert(aggrKey);
                                possibleSum[0][{U,U}]+=aggrKey[0];
                            }
                        }
                    }else{
                        if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t))==NULL){
                            const auto& insertResult = nub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                                auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                                aggrKey[0]*=-1;
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{U,U}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{U,U}];
                                        if(sum > maxPossibleNegativeSum[0][{U,U}])
                                            maxPossibleNegativeSum[0][{U,U}]=sum;
                                    }
                                }
                                if(var > 0 && !undef0 && !undef2){
                                    auto& reas = negativeAggrReason[0][{U,U}];
                                    int starter_level=reas.level(var);
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            std::cout<<"Erasing from reason";tuple0->print();std::cout<<std::endl;
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple2);
                                        if(it != tupleToVar.end()) {
                                            std::cout<<"Erasing from reason";tuple2->print();std::cout<<std::endl;
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for(auto& pair : negativeAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
        for(auto& pair : positiveAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
    }
    if(tuple.getPredicateName() == &_a && tuple.size()==1){
        int Z = tuple[0];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_b_V_Z_U_not_c_U_V_not_a_Z_5_.getValues({Z});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wb_V_Z_U_not_c_U_V_not_a_Z_.erase(*tuples.back());
                if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            int U = t[2];
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueAggrVars[0][{U,U}];
                            auto& undefSet = undefAggrVars[0][{U,U}];
                            if(p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualSum[0][{U,U}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{U,U}];
                                    int starter_level=reas.level(var);
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[0],t[1],t[2]},&_b));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[3],t[4]},&_c));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                }
                            }
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                    possibleSum[0][{U,U}]+=aggrKey[0];
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesNegative = np_b_V_Z_U_not_c_U_V_not_a_Z_5_.getValues({Z});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[0],t[1],t[2]},&_b);
                if(ub.find(literal)!=NULL || wb.find(literal)!=NULL){
                    Tuple literal({t[3],t[4]},&_c);
                    if(wc.find(literal)==NULL){
                        nwb_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                        if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(t)==NULL){
                            const auto& insertResult = nub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        {
                            int U = t[2];
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                            auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                            std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                            if(np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                                aggrKey[0]*=-1;
                                std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualNegativeSum[0][{U,U}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{U,U}];
                                    reas.erase(var,reas.level(var));
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{U,U}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{U,U}];
                                        if(sum > maxPossibleNegativeSum[0][{U,U}])
                                            maxPossibleNegativeSum[0][{U,U}]=sum;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        const std::vector<const Tuple*>& tuples0 = pb_1_.getValues({Z});
        const std::vector<const Tuple*>& tuplesU0 = ub_1_.getValues({Z});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int V = tuple0->at(0);
            int U = tuple0->at(2);
            const Tuple negativeTuple1({U,V},&_c,true);
            const Tuple* tuple1 = uc.find(Tuple({U,V},&_c));
            bool undef1 = false;
            if(tuple1!=NULL){
                undef1 = true;
            }else if(wc.find(negativeTuple1)==NULL){
                tuple1=&negativeTuple1;
            }
            if(tuple1!=NULL){
                Tuple t({V,Z,U,U,V,Z},&_b_V_Z_U_not_c_U_V_not_a_Z_);
                {
                    std::vector<int> aggrKey({t[0]});
                    if(aggrKey[0]>0){
                        if(ub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t))==NULL){
                            if(wb_V_Z_U_not_c_U_V_not_a_Z_.find(t))
                                wb_V_Z_U_not_c_U_V_not_a_Z_.erase(t);
                            const auto& insertResult = ub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        auto& trueSet = trueAggrVars[0][{U,U}];
                        auto& undefSet = undefAggrVars[0][{U,U}];
                        if(p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,t[0]}).size()<=0){
                            if(trueSet.find(aggrKey)!=trueSet.end()){
                                trueSet.erase(aggrKey);
                                actualSum[0][{U,U}]-=aggrKey[0];
                                auto& reas = positiveAggrReason[0][{U,U}];
                                int starter_level=reas.level(var);
                                reas.erase(var,reas.level(var));
                                {
                                    const auto & it = tupleToVar.find(*tuple0);
                                    if(it != tupleToVar.end()) {
                                        std::cout<<"Erasing from reason";tuple0->print();std::cout<<std::endl;
                                        reas.erase(it->second,starter_level);
                                    }
                                }
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        std::cout<<"Erasing from reason";tuple1->print();std::cout<<std::endl;
                                        reas.erase(-1*it->second,starter_level);
                                    }
                                }
                            }
                        }
                        if(undefSet.find(aggrKey)==undefSet.end()){
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                undefSet.insert(aggrKey);
                                possibleSum[0][{U,U}]+=aggrKey[0];
                            }
                        }
                    }else{
                        if(nub_V_Z_U_not_c_U_V_not_a_Z_.find(Tuple(t))==NULL){
                            const auto& insertResult = nub_V_Z_U_not_c_U_V_not_a_Z_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                                auto& trueSet = trueNegativeAggrVars[0][{U,U}];
                                auto& undefSet = undefNegativeAggrVars[0][{U,U}];
                                aggrKey[0]*=-1;
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{U,U}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{U,U}];
                                        if(sum > maxPossibleNegativeSum[0][{U,U}])
                                            maxPossibleNegativeSum[0][{U,U}]=sum;
                                    }
                                }
                                if(var > 0 && !undef0 && !undef1){
                                    auto& reas = negativeAggrReason[0][{U,U}];
                                    int starter_level=reas.level(var);
                                    {
                                        const auto & it = tupleToVar.find(*tuple0);
                                        if(it != tupleToVar.end()) {
                                            std::cout<<"Erasing from reason";tuple0->print();std::cout<<std::endl;
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(*tuple1);
                                        if(it != tupleToVar.end()) {
                                            std::cout<<"Erasing from reason";tuple1->print();std::cout<<std::endl;
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for(auto& pair : negativeAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
        for(auto& pair : positiveAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
    }
    if(tuple.getPredicateName() == &_a){
        int U = tuple.at(0);
        {
            if(!sharedVariables_0_ToAggregate_1.count({U,U})){
                sharedVariables_0_ToAggregate_1.insert({U,U});
            }
        }
    }
    std::cout<<"Negative Reason size: "<<negativeAggrReason[0][{}].size()<<std::endl;
    std::cout<<"Positive Reason size: "<<positiveAggrReason[0][{}].size()<<std::endl;
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
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_b]=&wb;
    predicateFSetMap[&_b]=&fb;
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
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_0_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_5_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_);
    predicateToAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&p_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_0_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_0_1_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_1_2_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_2_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_1_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_1_2_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_2_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_0_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_5_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_);
    predicateToNegativeAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&np_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_0_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_5_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_);
    predicateToUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&u_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_0_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_0_1_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_2_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_1_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_1_2_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_0_1_2_2_3_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_1_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_3_4_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_5_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_3_4_2_3_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_5_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_b_V_Z_U_not_c_U_V_not_a_Z_].push_back(&nu_b_V_Z_U_not_c_U_V_not_a_Z_5_2_3_0_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_0_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_0_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_0_1_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_1_2_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_2_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_1_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_1_2_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_2_);
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
            tuples = &pa_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &ua_.getValues({});
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
                int undefPlusTrue = actualSum[0][{U,U}]+possibleSum[0][{U,U}]+actualNegativeSum[0][{U,U}]+possibleNegativeSum[0][{U,U}];
                //U
                if(!(undefPlusTrue>=U+maxPossibleNegativeSum[0][{U,U}])){
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
                        int undefPlusTrue = actualSum[0][{U,U}]+possibleSum[0][{U,U}];
                        bool propagated=false;
                        {
                            for(auto undefKey = undefAggrVars[0][{U,U}].rbegin();undefKey!=undefAggrVars[0][{U,U}].rend();undefKey++){
                                if(undefPlusTrue-undefKey->at(0)>=U+maxPossibleNegativeSum[0][{U,U}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,undefKey->at(0)});
                                    if(undefinedTuples->size()==1){

                                        const Tuple* tuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                        if(tuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*tuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"Propagation Negated";tuple0->print();std::cout<<std::endl;
                                                int sign = -1;
                                                propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                        const Tuple* tuple1 = uc.find(Tuple({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c));
                                        if(tuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*tuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                                int sign = 1;
                                                propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                        const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(5)},&_a));
                                        if(tuple2!=NULL){
                                            const auto & it2 = tupleToVar.find(*tuple2);
                                            if(it2 != tupleToVar.end()) {
                                                propagated=true;
                                                std::cout<<"Propagation Negated";tuple2->print();std::cout<<std::endl;
                                                int sign = 1;
                                                propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>()}).first->second;
                                            }
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{U,U}].rbegin();undefKey!=undefNegativeAggrVars[0][{U,U}].rend();undefKey++){
                                int V = undefKey->at(0);
                                V*=-1;
                                if(undefPlusTrue-undefKey->at(0)>=U+maxPossibleNegativeSum[0][{U,U}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,V});
                                    if(undefinedTuples->size()==1){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                        if(tupleU0!=NULL && !negativeJoinPropagated){
                                            Tuple tuple1 ({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c);
                                            if(wc.find(tuple1)==NULL && uc.find(tuple1)==NULL){
                                                Tuple tuple2 ({undefinedTuples->at(0)->at(5)},&_a);
                                                if(wa.find(tuple2)==NULL && ua.find(tuple2)==NULL){
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
                                        const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c));
                                        if(tupleU1!=NULL && !negativeJoinPropagated){
                                            Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b);
                                            if(wb.find(tuple0)!=NULL){
                                                Tuple tuple2 ({undefinedTuples->at(0)->at(5)},&_a);
                                                if(wa.find(tuple2)==NULL && ua.find(tuple2)==NULL){
                                                    const auto & it1 = tupleToVar.find(*tupleU1);
                                                    if(it1 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        std::cout<<"Propagation Negated Negative join";tupleU1->print();std::cout<<std::endl;
                                                        int sign = -1;
                                                        propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                        const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(0)->at(5)},&_a));
                                        if(tupleU2!=NULL && !negativeJoinPropagated){
                                            Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b);
                                            if(wb.find(tuple0)!=NULL){
                                                Tuple tuple1 ({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c);
                                                if(wc.find(tuple1)==NULL && uc.find(tuple1)==NULL){
                                                    const auto & it2 = tupleToVar.find(*tupleU2);
                                                    if(it2 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        std::cout<<"Propagation Negated Negative join";tupleU2->print();std::cout<<std::endl;
                                                        int sign = -1;
                                                        propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>()}).first->second;
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
        if(starter.getPredicateName() == &_a) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int U = (*tuple0)[0];
                    int undefPlusTrue = actualSum[0][{U,U}]+possibleSum[0][{U,U}]+actualNegativeSum[0][{U,U}]+possibleNegativeSum[0][{U,U}];
                    //U
                    if(!(undefPlusTrue>=U+maxPossibleNegativeSum[0][{U,U}])){
                        std::vector<int> local_reason;
                        local_reason.insert(local_reason.end(),negativeAggrReason[0][{U,U}].begin(), negativeAggrReason[0][{U,U}].end());
                        const auto & it = tupleToVar.find(Tuple(starter));
                        if(it!=tupleToVar.end()){
                            local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
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
                            int undefPlusTrue = actualSum[0][{U,U}]+possibleSum[0][{U,U}];
                            bool propagated=false;
                            {
                                std::vector<int> local_reason;
                                local_reason.insert(local_reason.end(),negativeAggrReason[0][{U,U}].begin(), negativeAggrReason[0][{U,U}].end());
                                if(tuple0!=tupleU){
                                    const auto & it = tupleToVar.find(Tuple(*tuple0));
                                    if(it!=tupleToVar.end()){
                                        local_reason.push_back(it->second);
                                    }
                                }
                                for(auto undefKey = undefAggrVars[0][{U,U}].rbegin();undefKey!=undefAggrVars[0][{U,U}].rend();undefKey++){
                                    if(undefPlusTrue-undefKey->at(0)>=U+maxPossibleNegativeSum[0][{U,U}])
                                        break;
                                    else{
                                        const std::vector<const Tuple*>* undefinedTuples = &u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,undefKey->at(0)});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* tuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                            if(tuple0!=NULL){
                                                const auto & it0 = tupleToVar.find(*tuple0);
                                                if(it0 != tupleToVar.end()) {
                                                    propagated=true;
                                                    std::cout<<"Propagation Negated";tuple0->print();std::cout<<std::endl;
                                                    int sign = -1;
                                                    propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple1 = uc.find(Tuple({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c));
                                            if(tuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*tuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
                                                    std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                                    int sign = 1;
                                                    propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                            const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(5)},&_a));
                                            if(tuple2!=NULL){
                                                const auto & it2 = tupleToVar.find(*tuple2);
                                                if(it2 != tupleToVar.end()) {
                                                    propagated=true;
                                                    std::cout<<"Propagation Negated";tuple2->print();std::cout<<std::endl;
                                                    int sign = 1;
                                                    propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>(local_reason)}).first->second;
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKey = undefNegativeAggrVars[0][{U,U}].rbegin();undefKey!=undefNegativeAggrVars[0][{U,U}].rend();undefKey++){
                                    int V = undefKey->at(0);
                                    V*=-1;
                                    if(undefPlusTrue-undefKey->at(0)>=U+maxPossibleNegativeSum[0][{U,U}])
                                        break;
                                    else{
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,V});
                                        if(undefinedTuples->size()==1){

                                            bool negativeJoinPropagated=false;
                                            const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                            if(tupleU0!=NULL && !negativeJoinPropagated){
                                                Tuple tuple1 ({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c);
                                                if(wc.find(tuple1)==NULL && uc.find(tuple1)==NULL){
                                                    Tuple tuple2 ({undefinedTuples->at(0)->at(5)},&_a);
                                                    if(wa.find(tuple2)==NULL && ua.find(tuple2)==NULL){
                                                        const auto & it0 = tupleToVar.find(*tupleU0);
                                                        if(it0 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            std::cout<<"Propagation Negated Negative join";tupleU0->print();std::cout<<std::endl;
                                                            int sign = 1;
                                                            propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                        }
                                                    }
                                                }
                                            }
                                            const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c));
                                            if(tupleU1!=NULL && !negativeJoinPropagated){
                                                Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b);
                                                if(wb.find(tuple0)!=NULL){
                                                    Tuple tuple2 ({undefinedTuples->at(0)->at(5)},&_a);
                                                    if(wa.find(tuple2)==NULL && ua.find(tuple2)==NULL){
                                                        const auto & it1 = tupleToVar.find(*tupleU1);
                                                        if(it1 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            std::cout<<"Propagation Negated Negative join";tupleU1->print();std::cout<<std::endl;
                                                            int sign = -1;
                                                            propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                        }
                                                    }
                                                }
                                            }
                                            const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(0)->at(5)},&_a));
                                            if(tupleU2!=NULL && !negativeJoinPropagated){
                                                Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b);
                                                if(wb.find(tuple0)!=NULL){
                                                    Tuple tuple1 ({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c);
                                                    if(wc.find(tuple1)==NULL && uc.find(tuple1)==NULL){
                                                        const auto & it2 = tupleToVar.find(*tupleU2);
                                                        if(it2 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            std::cout<<"Propagation Negated Negative join";tupleU2->print();std::cout<<std::endl;
                                                            int sign = -1;
                                                            propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>(local_reason)}).first->second;
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
            if(starter.getPredicateName()== &_b || starter.getPredicateName()== &_c || starter.getPredicateName()== &_a){
                for(const auto & sharedVarTuple0_1 : sharedVariables_0_ToAggregate_1){
                    int U = sharedVarTuple0_1[0];
                    tupleU=NULL;
                    const Tuple * tuple1 = (wa.find(Tuple({U},&_a)));
                    if(!tuple1 && !tupleU ){
                        tuple1 = tupleU = (ua.find(Tuple({U},&_a)));
                        tupleUNegated = false;
                    }
                    if(tuple1){
                        int undefPlusTrue = actualSum[0][{U,U}]+possibleSum[0][{U,U}]+actualNegativeSum[0][{U,U}]+possibleNegativeSum[0][{U,U}];
                        //U
                        if(!(undefPlusTrue>=U+maxPossibleNegativeSum[0][{U,U}])){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[0][{U,U}].begin(), negativeAggrReason[0][{U,U}].end());
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
                        }else{
                            bool propagated=false;
                            {
                                if(tupleU == NULL){
                                    std::vector<int> local_reason;
                                    local_reason.insert(local_reason.end(),negativeAggrReason[0][{U,U}].begin(), negativeAggrReason[0][{U,U}].end());
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
                                    for(auto undefKey = undefAggrVars[0][{U,U}].rbegin();undefKey!=undefAggrVars[0][{U,U}].rend();undefKey++){
                                        if(undefPlusTrue-undefKey->at(0)>=U+maxPossibleNegativeSum[0][{U,U}])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &u_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,undefKey->at(0)});
                                            if(undefinedTuples->size()==1){

                                                const Tuple* tuple0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                                if(tuple0!=NULL){
                                                    const auto & it0 = tupleToVar.find(*tuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        propagated=true;
                                                        std::cout<<"Propagation Negated";tuple0->print();std::cout<<std::endl;
                                                        int sign = -1;
                                                        propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                    }
                                                }
                                                const Tuple* tuple1 = uc.find(Tuple({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c));
                                                if(tuple1!=NULL){
                                                    const auto & it1 = tupleToVar.find(*tuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        propagated=true;
                                                        std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                                        int sign = 1;
                                                        propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                    }
                                                }
                                                const Tuple* tuple2 = ua.find(Tuple({undefinedTuples->at(0)->at(5)},&_a));
                                                if(tuple2!=NULL){
                                                    const auto & it2 = tupleToVar.find(*tuple2);
                                                    if(it2 != tupleToVar.end()) {
                                                        propagated=true;
                                                        std::cout<<"Propagation Negated";tuple2->print();std::cout<<std::endl;
                                                        int sign = 1;
                                                        propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>(local_reason)}).first->second;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKey = undefNegativeAggrVars[0][{U,U}].rbegin();undefKey!=undefNegativeAggrVars[0][{U,U}].rend();undefKey++){
                                        int V = undefKey->at(0);
                                        V*=-1;
                                        if(undefPlusTrue-undefKey->at(0)>=U+maxPossibleNegativeSum[0][{U,U}])
                                            break;
                                        else{
                                            const std::vector<const Tuple*>* undefinedTuples = &nu_b_V_Z_U_not_c_U_V_not_a_Z_2_3_0_.getValues({U,U,V});
                                            if(undefinedTuples->size()==1){

                                                bool negativeJoinPropagated=false;
                                                const Tuple* tupleU0 = ub.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b));
                                                if(tupleU0!=NULL && !negativeJoinPropagated){
                                                    Tuple tuple1 ({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c);
                                                    if(wc.find(tuple1)==NULL && uc.find(tuple1)==NULL){
                                                        Tuple tuple2 ({undefinedTuples->at(0)->at(5)},&_a);
                                                        if(wa.find(tuple2)==NULL && ua.find(tuple2)==NULL){
                                                            const auto & it0 = tupleToVar.find(*tupleU0);
                                                            if(it0 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                std::cout<<"Propagation Negated Negative join";tupleU0->print();std::cout<<std::endl;
                                                                int sign = 1;
                                                                propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                                            }
                                                        }
                                                    }
                                                }
                                                const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c));
                                                if(tupleU1!=NULL && !negativeJoinPropagated){
                                                    Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b);
                                                    if(wb.find(tuple0)!=NULL){
                                                        Tuple tuple2 ({undefinedTuples->at(0)->at(5)},&_a);
                                                        if(wa.find(tuple2)==NULL && ua.find(tuple2)==NULL){
                                                            const auto & it1 = tupleToVar.find(*tupleU1);
                                                            if(it1 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                std::cout<<"Propagation Negated Negative join";tupleU1->print();std::cout<<std::endl;
                                                                int sign = -1;
                                                                propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                                            }
                                                        }
                                                    }
                                                }
                                                const Tuple* tupleU2 = ua.find(Tuple({undefinedTuples->at(0)->at(5)},&_a));
                                                if(tupleU2!=NULL && !negativeJoinPropagated){
                                                    Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1),undefinedTuples->at(0)->at(2)},&_b);
                                                    if(wb.find(tuple0)!=NULL){
                                                        Tuple tuple1 ({undefinedTuples->at(0)->at(3),undefinedTuples->at(0)->at(4)},&_c);
                                                        if(wc.find(tuple1)==NULL && uc.find(tuple1)==NULL){
                                                            const auto & it2 = tupleToVar.find(*tupleU2);
                                                            if(it2 != tupleToVar.end()) {
                                                                negativeJoinPropagated=true;
                                                                std::cout<<"Propagation Negated Negative join";tupleU2->print();std::cout<<std::endl;
                                                                int sign = -1;
                                                                propagatedLiteralsAndReasons.insert({it2->second*sign, std::vector<int>(local_reason)}).first->second;
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
