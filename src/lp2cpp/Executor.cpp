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
const std::string _b = "b";
PredicateWSet wb(1);
PredicateWSet ub(1);
PredicateWSet fb(1);
const std::string _c = "c";
PredicateWSet wc(2);
PredicateWSet uc(2);
PredicateWSet fc(2);
const std::string _c_W_U_c_V_X_not_b_X_WGTEV_VGTX_ = "c_W_U_c_V_X_not_b_X_WGTEV_VGTX_";
PredicateWSet wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_(5);
PredicateWSet uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_(5);
PredicateWSet nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_(5);
PredicateWSet nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_(5);
std::set<std::vector<int>> sharedVariables_0_ToAggregate_0;
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
AuxMap pc_0_1_({0,1});
AuxMap uc_0_1_({0,1});
AuxMap fc_0_1_({0,1});
AuxMap pc_({});
AuxMap uc_({});
AuxMap fc_({});
AuxMap pb_0_({0});
AuxMap ub_0_({0});
AuxMap fb_0_({0});
AuxMap pb_({});
AuxMap ub_({});
AuxMap fb_({});
AuxMap pc_1_({1});
AuxMap uc_1_({1});
AuxMap fc_1_({1});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_({1,2,0,3});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_({1,2,0,3});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_({1,2,0,3});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_({1,2,0,3});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_({});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_({});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_({});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_({});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_({0,1});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_({0,1});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_({0,1});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_({0,1});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_({2,3});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_({2,3});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_({2,3});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_({2,3});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_({4});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_({4});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_({4});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_({4});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_({0,1,1,2,0,3});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_({0,1,1,2,0,3});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_({0,1,1,2,0,3});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_({0,1,1,2,0,3});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_({2,3,1,2,0,3});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_({2,3,1,2,0,3});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_({2,3,1,2,0,3});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_({2,3,1,2,0,3});
AuxMap p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_({4,1,2,0,3});
AuxMap u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_({4,1,2,0,3});
AuxMap np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_({4,1,2,0,3});
AuxMap nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_({4,1,2,0,3});
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
    if(var<0 && ( tuple.getPredicateName() == &_b || tuple.getPredicateName() == &_c)){
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
    if(tuple.getPredicateName() == &_c){
        int W = tuple[0];
        int U = tuple[1];
        if(var > 0){
            bool negative_join=false;
            bool positive_join=false;
            const std::vector<const Tuple*>* tuples1 = &pc_.getValues({});
            for(int i_1=0;i_1<tuples1->size();i_1++){
                const Tuple* tuple1=tuples1->at(i_1);
                int V = tuple1->at(0);
                int X = tuple1->at(1);
                const Tuple negativeTuple2({X},&_b,true);
                const Tuple* tuple2 = ub.find(Tuple({X},&_b));
                if(wb.find(negativeTuple2)==NULL && tuple2==NULL){
                    tuple2=&negativeTuple2;
                    if(W >= V){
                        if(V > X){
                            Tuple t({W,U,V,X,X},&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
                            {
                                std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                                if(aggrKey[0]>0){
                                    if(wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)==NULL){
                                        if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t))
                                            uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                        const auto& insertResult = wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
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
                                        if(!reas.level(var)==-1){
                                            reas.addLevel();
                                            reas.insert(var);
                                            tuple.print();std::cout<<"Added to positive reason"<<std::endl;
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
                                                reas.insert(it->second*-1);
                                            }
                                        }
                                    }
                                }else{
                                    if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)){
                                        nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                        auto& undefSet = undefNegativeAggrVars[0][{}];
                                        if(nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                            aggrKey[0]*=-1;
                                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                                undefSet.erase(aggrKey);
                                                possibleNegativeSum[0][{}]-=aggrKey[0];
                                            }
                                        }
                                        auto& reas = negativeAggrReason[0][{}];
                                        if(reas.level(var)==-1){
                                            reas.addLevel();
                                            reas.insert(var);
                                            tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                                        }
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                tuple1->print();std::cout<<"Added to negative reason"<<std::endl;
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
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_.getValues({W,U});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    if(reas.level(var)==-1){
                        reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_.getValues({W,U});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                const auto& insertResult = nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                        possibleNegativeSum[0][{}]-=aggrKey[0];
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                        actualNegativeSum[0][{}]+=aggrKey[0];
                        auto& reas = positiveAggrReason[0][{}];
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
        int V = tuple[0];
        int X = tuple[1];
        if(var > 0){
            bool negative_join=false;
            bool positive_join=false;
            const std::vector<const Tuple*>* tuples0 = &pc_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int W = tuple0->at(0);
                int U = tuple0->at(1);
                const Tuple negativeTuple2({X},&_b,true);
                const Tuple* tuple2 = ub.find(Tuple({X},&_b));
                if(wb.find(negativeTuple2)==NULL && tuple2==NULL){
                    tuple2=&negativeTuple2;
                    if(W >= V){
                        if(V > X){
                            Tuple t({W,U,V,X,X},&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
                            {
                                std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                                if(aggrKey[0]>0){
                                    if(wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)==NULL){
                                        if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t))
                                            uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                        const auto& insertResult = wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
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
                                        if(!reas.level(var)==-1){
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
                                    if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)){
                                        nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                        auto& undefSet = undefNegativeAggrVars[0][{}];
                                        if(nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                            aggrKey[0]*=-1;
                                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                                undefSet.erase(aggrKey);
                                                possibleNegativeSum[0][{}]-=aggrKey[0];
                                            }
                                        }
                                        auto& reas = negativeAggrReason[0][{}];
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
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_.getValues({V,X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    if(reas.level(var)==-1){
                        reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_.getValues({V,X});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                const auto& insertResult = nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                        possibleNegativeSum[0][{}]-=aggrKey[0];
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                        actualNegativeSum[0][{}]+=aggrKey[0];
                        auto& reas = positiveAggrReason[0][{}];
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
    if(tuple.getPredicateName() == &_b){
        int X = tuple[0];
        if(var < 0){
            bool negative_join=false;
            bool positive_join=false;
            const std::vector<const Tuple*>* tuples0 = &pc_.getValues({});
            for(int i_0=0;i_0<tuples0->size();i_0++){
                const Tuple* tuple0=tuples0->at(i_0);
                int W = tuple0->at(0);
                int U = tuple0->at(1);
                const std::vector<const Tuple*>* tuples1 = &pc_1_.getValues({X});
                for(int i_1=0;i_1<tuples1->size();i_1++){
                    const Tuple* tuple1=tuples1->at(i_1);
                    int V = tuple1->at(0);
                    if(W >= V){
                        if(V > X){
                            Tuple t({W,U,V,X,X},&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
                            {
                                std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                                if(aggrKey[0]>0){
                                    if(wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)==NULL){
                                        if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t))
                                            uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                        const auto& insertResult = wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                        if (insertResult.second) {
                                            for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
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
                                        if(!reas.level(var)==-1){
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
                                                reas.insert(it->second);
                                            }
                                        }
                                    }
                                }else{
                                    if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)){
                                        nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                        auto& undefSet = undefNegativeAggrVars[0][{}];
                                        if(nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                            aggrKey[0]*=-1;
                                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                                undefSet.erase(aggrKey);
                                                possibleNegativeSum[0][{}]-=aggrKey[0];
                                            }
                                        }
                                        auto& reas = negativeAggrReason[0][{}];
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
                                                reas.insert(it->second);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_.getValues({X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                            possibleSum[0][{}]-=aggrKey[0];
                        }
                    }
                    auto& reas = negativeAggrReason[0][{}];
                    if(reas.level(var)==-1){
                        reas.addLevel();
                        reas.insert(var);
                        tuple.print();std::cout<<"Added to negative reason"<<std::endl;
                    }
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_.getValues({X});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                const auto& insertResult = nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                        possibleNegativeSum[0][{}]-=aggrKey[0];
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                        actualNegativeSum[0][{}]+=aggrKey[0];
                        auto& reas = positiveAggrReason[0][{}];
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
    if(var<0 && ( tuple.getPredicateName() == &_b || tuple.getPredicateName() == &_c)){
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
    if(tuple.getPredicateName() == &_c && tuple.size()==2){
        int W = tuple[0];
        int U = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_.getValues({W,U});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(*tuples.back());
                if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualSum[0][{}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
                                    int starter_level=reas.level(var);
                                    reas.erase(var,starter_level);
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[2],t[3]},&_c));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[4]},&_b));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
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
            }
        }else{
            const std::vector<const Tuple*>& tuplesNegative = np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_.getValues({W,U});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[2],t[3]},&_c);
                if(uc.find(literal)!=NULL || wc.find(literal)!=NULL){
                    Tuple literal({t[4]},&_b);
                    if(wb.find(literal)==NULL){
                        nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                        if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)==NULL){
                            const auto& insertResult = nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                            if(np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                aggrKey[0]*=-1;
                                std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualNegativeSum[0][{}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
                                    reas.erase(var,reas.level(var));
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{}];
                                        if(sum > maxPossibleNegativeSum[0][{}])
                                            maxPossibleNegativeSum[0][{}]=sum;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        const std::vector<const Tuple*>& tuples1 = pc_.getValues({});
        const std::vector<const Tuple*>& tuplesU1 = uc_.getValues({});
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
            const Tuple negativeTuple2({X},&_b,true);
            const Tuple* tuple2 = ub.find(Tuple({X},&_b));
            bool undef2 = false;
            if(tuple2!=NULL){
                undef2 = true;
            }else if(wb.find(negativeTuple2)==NULL){
                tuple2=&negativeTuple2;
            }
            if(tuple2!=NULL){
                if(W >= V){
                    if(V > X){
                        Tuple t({W,U,V,X,X},&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            if(aggrKey[0]>0){
                                if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t))==NULL){
                                    if(wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t))
                                        wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                    const auto& insertResult = uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                        actualSum[0][{}]-=aggrKey[0];
                                        auto& reas = positiveAggrReason[0][{}];
                                        int starter_level=reas.level(var);
                                        reas.erase(var,reas.level(var));
                                        {
                                            const auto & it = tupleToVar.find(*tuple1);
                                            if(it != tupleToVar.end()) {
                                                std::cout<<"Erasing from reason";tuple1->print();std::cout<<std::endl;
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
                                        possibleSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }else{
                                if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t))==NULL){
                                    const auto& insertResult = nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                        auto& trueSet = trueNegativeAggrVars[0][{}];
                                        auto& undefSet = undefNegativeAggrVars[0][{}];
                                        aggrKey[0]*=-1;
                                        if(undefSet.find(aggrKey)==undefSet.end()){
                                            if(trueSet.find(aggrKey)==trueSet.end()){
                                                undefSet.insert(aggrKey);
                                                possibleNegativeSum[0][{}]+=aggrKey[0];
                                                int sum = possibleNegativeSum[0][{}];
                                                if(sum > maxPossibleNegativeSum[0][{}])
                                                    maxPossibleNegativeSum[0][{}]=sum;
                                            }
                                        }
                                        if(var > 0 && !undef1 && !undef2){
                                            auto& reas = negativeAggrReason[0][{}];
                                            int starter_level=reas.level(var);
                                            {
                                                const auto & it = tupleToVar.find(*tuple1);
                                                if(it != tupleToVar.end()) {
                                                    std::cout<<"Erasing from reason";tuple1->print();std::cout<<std::endl;
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
            }
        }
        for(auto& pair : negativeAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
    }
    if(tuple.getPredicateName() == &_c && tuple.size()==2){
        int V = tuple[0];
        int X = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_.getValues({V,X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(*tuples.back());
                if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualSum[0][{}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
                                    int starter_level=reas.level(var);
                                    reas.erase(var,starter_level);
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[0],t[1]},&_c));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[4]},&_b));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(-1*it->second,starter_level);
                                        }
                                    }
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
            }
        }else{
            const std::vector<const Tuple*>& tuplesNegative = np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_.getValues({V,X});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[0],t[1]},&_c);
                if(uc.find(literal)!=NULL || wc.find(literal)!=NULL){
                    Tuple literal({t[4]},&_b);
                    if(wb.find(literal)==NULL){
                        nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                        if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)==NULL){
                            const auto& insertResult = nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                            if(np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                aggrKey[0]*=-1;
                                std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualNegativeSum[0][{}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
                                    reas.erase(var,reas.level(var));
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{}];
                                        if(sum > maxPossibleNegativeSum[0][{}])
                                            maxPossibleNegativeSum[0][{}]=sum;
                                    }
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
            int W = tuple0->at(0);
            int U = tuple0->at(1);
            const Tuple negativeTuple2({X},&_b,true);
            const Tuple* tuple2 = ub.find(Tuple({X},&_b));
            bool undef2 = false;
            if(tuple2!=NULL){
                undef2 = true;
            }else if(wb.find(negativeTuple2)==NULL){
                tuple2=&negativeTuple2;
            }
            if(tuple2!=NULL){
                if(W >= V){
                    if(V > X){
                        Tuple t({W,U,V,X,X},&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            if(aggrKey[0]>0){
                                if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t))==NULL){
                                    if(wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t))
                                        wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                    const auto& insertResult = uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                        actualSum[0][{}]-=aggrKey[0];
                                        auto& reas = positiveAggrReason[0][{}];
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
                                        possibleSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }else{
                                if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t))==NULL){
                                    const auto& insertResult = nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                        auto& trueSet = trueNegativeAggrVars[0][{}];
                                        auto& undefSet = undefNegativeAggrVars[0][{}];
                                        aggrKey[0]*=-1;
                                        if(undefSet.find(aggrKey)==undefSet.end()){
                                            if(trueSet.find(aggrKey)==trueSet.end()){
                                                undefSet.insert(aggrKey);
                                                possibleNegativeSum[0][{}]+=aggrKey[0];
                                                int sum = possibleNegativeSum[0][{}];
                                                if(sum > maxPossibleNegativeSum[0][{}])
                                                    maxPossibleNegativeSum[0][{}]=sum;
                                            }
                                        }
                                        if(var > 0 && !undef0 && !undef2){
                                            auto& reas = negativeAggrReason[0][{}];
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
            }
        }
        for(auto& pair : negativeAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
        }
    }
    if(tuple.getPredicateName() == &_b && tuple.size()==1){
        int X = tuple[0];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_.getValues({X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(*tuples.back());
                if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualSum[0][{}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
                                    int starter_level=reas.level(var);
                                    reas.erase(var,starter_level);
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[0],t[1]},&_c));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
                                    {
                                        const auto & it = tupleToVar.find(Tuple({t[2],t[3]},&_c));
                                        if(it != tupleToVar.end()) {
                                            reas.erase(it->second,starter_level);
                                        }
                                    }
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
            }
        }else{
            const std::vector<const Tuple*>& tuplesNegative = np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_.getValues({X});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[0],t[1]},&_c);
                if(uc.find(literal)!=NULL || wc.find(literal)!=NULL){
                    Tuple literal({t[2],t[3]},&_c);
                    if(uc.find(literal)!=NULL || wc.find(literal)!=NULL){
                        nwc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                        if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t)==NULL){
                            const auto& insertResult = nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                            if(np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                aggrKey[0]*=-1;
                                std::cout<<"aggr key:"<<aggrKey[0]<<std::endl;
                                if(trueSet.find(aggrKey)!=trueSet.end()){
                                    trueSet.erase(aggrKey);
                                    actualNegativeSum[0][{}]-=aggrKey[0];
                                    auto& reas = positiveAggrReason[0][{}];
                                    reas.erase(var,reas.level(var));
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleNegativeSum[0][{}]+=aggrKey[0];
                                        int sum = possibleNegativeSum[0][{}];
                                        if(sum > maxPossibleNegativeSum[0][{}])
                                            maxPossibleNegativeSum[0][{}]=sum;
                                    }
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
            int W = tuple0->at(0);
            int U = tuple0->at(1);
            const std::vector<const Tuple*>& tuples1 = pc_1_.getValues({X});
            const std::vector<const Tuple*>& tuplesU1 = uc_1_.getValues({X});
            for(int i_1=0;i_1<tuples1.size()+tuplesU1.size();i_1++){
                const Tuple* tuple1;
                bool undef1=false;
                if(i_1<tuples1.size())                    tuple1=tuples1[i_1];
                else{
                    tuple1=tuplesU1[i_1-tuples1.size()];
                    undef1=true;
                }
                int V = tuple1->at(0);
                if(W >= V){
                    if(V > X){
                        Tuple t({W,U,V,X,X},&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
                        {
                            std::vector<int> aggrKey({t[1],t[2],t[0],t[3]});
                            if(aggrKey[0]>0){
                                if(uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t))==NULL){
                                    if(wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(t))
                                        wc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.erase(t);
                                    const auto& insertResult = uc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                    }
                                }
                                auto& trueSet = trueAggrVars[0][{}];
                                auto& undefSet = undefAggrVars[0][{}];
                                if(p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({aggrKey}).size()<=0){
                                    if(trueSet.find(aggrKey)!=trueSet.end()){
                                        trueSet.erase(aggrKey);
                                        actualSum[0][{}]-=aggrKey[0];
                                        auto& reas = positiveAggrReason[0][{}];
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
                                                reas.erase(it->second,starter_level);
                                            }
                                        }
                                    }
                                }
                                if(undefSet.find(aggrKey)==undefSet.end()){
                                    if(trueSet.find(aggrKey)==trueSet.end()){
                                        undefSet.insert(aggrKey);
                                        possibleSum[0][{}]+=aggrKey[0];
                                    }
                                }
                            }else{
                                if(nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.find(Tuple(t))==NULL){
                                    const auto& insertResult = nuc_W_U_c_V_X_not_b_X_WGTEV_VGTX_.insert(Tuple(t));
                                    if (insertResult.second) {
                                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_]){
                                            auxMap -> insert2(*insertResult.first);
                                        }
                                        auto& trueSet = trueNegativeAggrVars[0][{}];
                                        auto& undefSet = undefNegativeAggrVars[0][{}];
                                        aggrKey[0]*=-1;
                                        if(undefSet.find(aggrKey)==undefSet.end()){
                                            if(trueSet.find(aggrKey)==trueSet.end()){
                                                undefSet.insert(aggrKey);
                                                possibleNegativeSum[0][{}]+=aggrKey[0];
                                                int sum = possibleNegativeSum[0][{}];
                                                if(sum > maxPossibleNegativeSum[0][{}])
                                                    maxPossibleNegativeSum[0][{}]=sum;
                                            }
                                        }
                                        if(var > 0 && !undef0 && !undef1){
                                            auto& reas = negativeAggrReason[0][{}];
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
                                                    reas.erase(it->second,starter_level);
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
        for(auto& pair : negativeAggrReason[0]){
            pair.second.erase(var,pair.second.level(var));
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
    predicateWSetMap[&_c]=&wc;
    predicateFSetMap[&_c]=&fc;
    predicateUSetMap[&_c]=&uc;
    stringToUniqueStringPointer["c"] = &_c;
    predicateWSetMap[&_c]=&wc;
    predicateFSetMap[&_c]=&fc;
    predicateUSetMap[&_c]=&uc;
    stringToUniqueStringPointer["c"] = &_c;
    predicateWSetMap[&_b]=&wb;
    predicateFSetMap[&_b]=&fb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_);
    predicateToAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&p_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_0_1_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_1_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_);
    predicateToNegativeAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&np_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_);
    predicateToUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_0_1_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_0_1_1_2_0_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_2_3_1_2_0_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_);
    predicateToNegativeUndefAuxiliaryMaps[&_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_].push_back(&nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_4_1_2_0_3_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_0_1_);
    predicateToFalseAuxiliaryMaps[&_c].push_back(&fc_1_);
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
                if(actualSum[0][{}]+actualNegativeSum[0][{}]>=4+maxPossibleNegativeSum[0][{}]){
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
                        for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                            if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 4+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({undefKey->at(0),undefKey->at(1),undefKey->at(2),undefKey->at(3)});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                    bool found=false;
                                    if(!found){
                                        const Tuple* aggrTupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                        const Tuple* tuple1 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                        const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                        const Tuple* tuple2 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                        const Tuple* tupleU2 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                        const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(4)},&_b,true);
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
                                        const Tuple* aggrTupleU1 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                        const Tuple* tuple0 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                        const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                        const Tuple* tuple2 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                        const Tuple* tupleU2 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                        const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(4)},&_b,true);
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
                                        const Tuple* aggrTupleU2 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                        const Tuple* tuple0 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                        const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                        const Tuple* tuple1 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                        const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
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
                            int U = undefKey->at(0);
                            U*=-1;
                            int V = undefKey->at(1);
                            int W = undefKey->at(2);
                            int X = undefKey->at(3);
                            if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 4+maxPossibleNegativeSum[0][{}])
                                break;
                            else{
                                const std::vector<const Tuple*>* undefinedTuples = &nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({U,V,W,X});
                                for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                    {
                                        Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c);
                                        if(uc.find(tuple0)!=NULL){
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
                                        Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c);
                                        if(uc.find(tuple1)!=NULL){
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
                                        Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_b);
                                        if(ub.find(tuple2)!=NULL){
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
            if(starter.getPredicateName()== &_c || starter.getPredicateName()== &_c || starter.getPredicateName()== &_b){
                {
                    if(actualSum[0][{}]+actualNegativeSum[0][{}]>=4+maxPossibleNegativeSum[0][{}]){
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
                                propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(local_reason)}).first->second;
                            }
                        }
                    }//close aggr true if
                    bool propagated=false;
                    {
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),positiveAggrReason[0][{}].begin(), positiveAggrReason[0][{}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            for(auto undefKey = undefAggrVars[0][{}].rbegin();undefKey!=undefAggrVars[0][{}].rend();undefKey++){
                                if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 4+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &u_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({undefKey->at(0),undefKey->at(1),undefKey->at(2),undefKey->at(3)});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                            const Tuple* tuple1 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                            const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                            const Tuple* tuple2 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                            const Tuple* tupleU2 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                            const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(4)},&_b,true);
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
                                                    std::cout<<"Propagation positive 0 ";aggrTupleU0->print();std::cout<<std::endl;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU1 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                            const Tuple* tuple0 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                            const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                            const Tuple* tuple2 = wb.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                            const Tuple* tupleU2 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                            const Tuple negativeTuple2 ({undefinedTuples->at(iUndef)->at(4)},&_b,true);
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
                                                    std::cout<<"Propagation positive 0 ";aggrTupleU1->print();std::cout<<std::endl;
                                                    found=true;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU2 = ub.find(Tuple({undefinedTuples->at(iUndef)->at(4)},&_b));
                                            const Tuple* tuple0 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                            const Tuple* tupleU0 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c));
                                            const Tuple* tuple1 = wc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
                                            const Tuple* tupleU1 = uc.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c));
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
                                int U = undefKey->at(0);
                                U*=-1;
                                int V = undefKey->at(1);
                                int W = undefKey->at(2);
                                int X = undefKey->at(3);
                                if(actualSum[0][{}]+actualNegativeSum[0][{}]+undefKey->at(0) < 4+maxPossibleNegativeSum[0][{}])
                                    break;
                                else{
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_c_W_U_c_V_X_not_b_X_WGTEV_VGTX_1_2_0_3_.getValues({U,V,W,X});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        {
                                            Tuple tuple0 ({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_c);
                                            if(uc.find(tuple0)!=NULL){
                                                std::vector<int> propagationReason(local_reason);
                                                const auto & it = tupleToVar.find(tuple0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    std::cout<<"Propagation positive negative join0 ";tuple0.print();std::cout<<std::endl;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple1 ({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_c);
                                            if(uc.find(tuple1)!=NULL){
                                                std::vector<int> propagationReason(local_reason);
                                                const auto & it = tupleToVar.find(tuple1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    std::cout<<"Propagation positive negative join0 ";tuple1.print();std::cout<<std::endl;
                                                    propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>(propagationReason)}).first->second;
                                                }
                                            }
                                        }
                                        {
                                            Tuple tuple2 ({undefinedTuples->at(iUndef)->at(4)},&_b);
                                            if(ub.find(tuple2)!=NULL){
                                                std::vector<int> propagationReason(local_reason);
                                                const auto & it = tupleToVar.find(tuple2);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
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
