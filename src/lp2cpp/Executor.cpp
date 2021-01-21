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
PredicateWSet wb(1);
PredicateWSet ub(1);
PredicateWSet fb(1);
const std::string _a_X_Y_b_Y_ = "a_X_Y_b_Y_";
PredicateWSet wa_X_Y_b_Y_(3);
PredicateWSet ua_X_Y_b_Y_(3);
PredicateWSet nwa_X_Y_b_Y_(3);
PredicateWSet nua_X_Y_b_Y_(3);
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
AuxMap pa_0_1_({0,1});
AuxMap ua_0_1_({0,1});
AuxMap fa_0_1_({0,1});
AuxMap pa_({});
AuxMap ua_({});
AuxMap fa_({});
AuxMap pb_0_({0});
AuxMap ub_0_({0});
AuxMap fb_0_({0});
AuxMap pb_({});
AuxMap ub_({});
AuxMap fb_({});
AuxMap pa_1_({1});
AuxMap ua_1_({1});
AuxMap fa_1_({1});
AuxMap p_a_X_Y_b_Y_0_({0});
AuxMap u_a_X_Y_b_Y_0_({0});
AuxMap np_a_X_Y_b_Y_0_({0});
AuxMap nu_a_X_Y_b_Y_0_({0});
AuxMap p_a_X_Y_b_Y_({});
AuxMap u_a_X_Y_b_Y_({});
AuxMap np_a_X_Y_b_Y_({});
AuxMap nu_a_X_Y_b_Y_({});
AuxMap p_a_X_Y_b_Y_0_1_({0,1});
AuxMap u_a_X_Y_b_Y_0_1_({0,1});
AuxMap np_a_X_Y_b_Y_0_1_({0,1});
AuxMap nu_a_X_Y_b_Y_0_1_({0,1});
AuxMap p_a_X_Y_b_Y_2_({2});
AuxMap u_a_X_Y_b_Y_2_({2});
AuxMap np_a_X_Y_b_Y_2_({2});
AuxMap nu_a_X_Y_b_Y_2_({2});
AuxMap p_a_X_Y_b_Y_0_1_0_({0,1,0});
AuxMap u_a_X_Y_b_Y_0_1_0_({0,1,0});
AuxMap np_a_X_Y_b_Y_0_1_0_({0,1,0});
AuxMap nu_a_X_Y_b_Y_0_1_0_({0,1,0});
AuxMap p_a_X_Y_b_Y_2_0_({2,0});
AuxMap u_a_X_Y_b_Y_2_0_({2,0});
AuxMap np_a_X_Y_b_Y_2_0_({2,0});
AuxMap nu_a_X_Y_b_Y_2_0_({2,0});
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
    if(tuple.getPredicateName() == &_a){
        int X = tuple[0];
        int Y = tuple[1];
        if(var > 0){
            const Tuple* tuple1 = wb.find(Tuple({Y},&_b));
            bool undef1 = false;
            if(tuple1==NULL){
                tuple1 = ub.find(Tuple({Y},&_b));
                undef1 = true;
            }
            if(tuple1!=NULL){
                if(!undef1){
                    Tuple t({X,Y,Y},&_a_X_Y_b_Y_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]>0){
                            if(wa_X_Y_b_Y_.find(t)==NULL){
                                if(ua_X_Y_b_Y_.find(t))
                                    ua_X_Y_b_Y_.erase(t);
                                const auto& insertResult = wa_X_Y_b_Y_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                            }
                        }else{
                            if(nua_X_Y_b_Y_.find(t)){
                                nua_X_Y_b_Y_.erase(t);
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                aggrKey[0]*=-1;
                                if(nu_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                }
                            }
                        }
                    }
                }else{
                    Tuple t({X,Y,Y},&_a_X_Y_b_Y_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]<0){
                            if(nua_X_Y_b_Y_.find(t)==NULL){
                                const auto& insertResult = nua_X_Y_b_Y_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            aggrKey[0]*=-1;
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }else{
                            if(ua_X_Y_b_Y_.find(t)==NULL){
                                if(wa_X_Y_b_Y_.find(t))
                                    wa_X_Y_b_Y_.erase(t);
                                const auto& insertResult = ua_X_Y_b_Y_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
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
        }else{
            const std::vector<const Tuple*>& tuplesU = u_a_X_Y_b_Y_0_1_.getValues({X,Y});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ua_X_Y_b_Y_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                        }
                    }
                    negativeAggrReason[0][{}].insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_a_X_Y_b_Y_0_1_.getValues({X,Y});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nua_X_Y_b_Y_.erase(t);
                const auto& insertResult = nwa_X_Y_b_Y_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                    }
                }
            }
        }
    }
    if(tuple.getPredicateName() == &_b){
        int Y = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>* tuples0 = &pa_1_.getValues({Y});
            const std::vector<const Tuple*>* tuplesU0 = &ua_1_.getValues({Y});
            for(int i_0=0;i_0<tuples0->size()+tuplesU0->size();i_0++){
                const Tuple* tuple0;
                bool undef0=false;
                if(i_0<tuples0->size())
                    tuple0=tuples0->at(i_0);
                else{
                    tuple0=tuplesU0->at(i_0-tuples0->size());
                    undef0=true;
                }
                int X = tuple0->at(0);
                if(!undef0){
                    Tuple t({X,Y,Y},&_a_X_Y_b_Y_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]>0){
                            if(wa_X_Y_b_Y_.find(t)==NULL){
                                if(ua_X_Y_b_Y_.find(t))
                                    ua_X_Y_b_Y_.erase(t);
                                const auto& insertResult = wa_X_Y_b_Y_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(undefSet.find(aggrKey)!=undefSet.end()){
                                undefSet.erase(aggrKey);
                            }
                            if(trueSet.find(aggrKey)==trueSet.end()){
                                trueSet.insert(aggrKey);
                            }
                        }else{
                            if(nua_X_Y_b_Y_.find(t)){
                                nua_X_Y_b_Y_.erase(t);
                                auto& undefSet = undefNegativeAggrVars[0][{}];
                                aggrKey[0]*=-1;
                                if(nu_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
                                    if(undefSet.find(aggrKey)!=undefSet.end()){
                                        undefSet.erase(aggrKey);
                                    }
                                }
                            }
                        }
                    }
                }else{
                    Tuple t({X,Y,Y},&_a_X_Y_b_Y_);
                    {
                        std::vector<int> aggrKey({t[0]});
                        if(aggrKey[0]<0){
                            if(nua_X_Y_b_Y_.find(t)==NULL){
                                const auto& insertResult = nua_X_Y_b_Y_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            aggrKey[0]*=-1;
                            if(undefSet.find(aggrKey)==undefSet.end()){
                                if(trueSet.find(aggrKey)==trueSet.end()){
                                    undefSet.insert(aggrKey);
                                }
                            }
                        }else{
                            if(ua_X_Y_b_Y_.find(t)==NULL){
                                if(wa_X_Y_b_Y_.find(t))
                                    wa_X_Y_b_Y_.erase(t);
                                const auto& insertResult = ua_X_Y_b_Y_.insert(Tuple(t));
                                if (insertResult.second) {
                                    for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                        auxMap -> insert2(*insertResult.first);
                                    }
                                }
                            }
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
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
        }else{
            const std::vector<const Tuple*>& tuplesU = u_a_X_Y_b_Y_2_.getValues({Y});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                ua_X_Y_b_Y_.erase(*tuplesU.back());
                {
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefAggrVars[0][{}];
                    if(u_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
                        if(undefSet.find(aggrKey)!=undefSet.end()){
                            undefSet.erase(aggrKey);
                        }
                    }
                    negativeAggrReason[0][{}].insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNegativeU = nu_a_X_Y_b_Y_2_.getValues({Y});
            while(!tuplesNegativeU.empty()){
                Tuple t(*tuplesNegativeU.back());
                nua_X_Y_b_Y_.erase(t);
                const auto& insertResult = nwa_X_Y_b_Y_.insert(Tuple(t));
                if (insertResult.second) {
                    for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_]){
                        auxMap -> insert2(*insertResult.first);
                    }
                }
                {
                    std::vector<int> aggrKey({t[0]});
                    auto& undefSet = undefNegativeAggrVars[0][{}];
                    auto& trueSet = trueNegativeAggrVars[0][{}];
                    aggrKey[0]*=-1;
                    if(undefSet.find(aggrKey)!=undefSet.end()){
                        undefSet.erase(aggrKey);
                    }
                    if(trueSet.find(aggrKey)==trueSet.end()){
                        trueSet.insert(aggrKey);
                    }
                }
            }
        }
    }
    std::cout<<"True join tuple"<<std::endl;
    for(const Tuple* t : wa_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"Undef join tuple"<<std::endl;
    for(const Tuple* t : ua_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"Negative True join tuple"<<std::endl;
    for(const Tuple* t : nwa_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"Negative Undef join tuple"<<std::endl;
    for(const Tuple* t : nua_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"ActualSum: "<<actualSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : trueAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"PossibleSum: "<<possibleSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : undefAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"NegativeActualSum: "<<actualNegativeSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : trueNegativeAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"NegativPossibleSum: "<<possibleNegativeSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : undefNegativeAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"MaxNegativPossibleSum: "<<maxPossibleNegativeSum[0][{}]<<std::endl;
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    const Tuple & tuple = atomsTable[uVar];
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    std::cout<<"Undef "<<minus;tuple.print();std::cout<<std::endl;
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
    if(tuple.getPredicateName() == &_a && tuple.size()==2){
        int X = tuple[0];
        int Y = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_a_X_Y_b_Y_0_1_.getValues({X,Y});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wa_X_Y_b_Y_.erase(*tuples.back());
                if(ua_X_Y_b_Y_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ua_X_Y_b_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
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
        }else{
            for(auto& pair : negativeAggrReason[0]){
                pair.second.erase(var);
            }
            const std::vector<const Tuple*>& tuplesNegative = np_a_X_Y_b_Y_0_1_.getValues({X,Y});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[2]},&_b);
                if(ub.find(literal)!=NULL || wb.find(literal)!=NULL){
                    nwa_X_Y_b_Y_.erase(t);
                    if(nua_X_Y_b_Y_.find(t)==NULL){
                        const auto& insertResult = nua_X_Y_b_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        aggrKey[0]*=-1;
                        if(np_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
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
        const Tuple* tuple1 = wb.find(Tuple({Y},&_b));
        bool undef1 = false;
        if(tuple1==NULL){
            tuple1 = ub.find(Tuple({Y},&_b));
            undef1 = true;
        }
        if(tuple1!=NULL){
            Tuple t({X,Y,Y},&_a_X_Y_b_Y_);
            {
                std::vector<int> aggrKey({t[0]});
                if(aggrKey[0]>0){
                    if(ua_X_Y_b_Y_.find(Tuple(t))==NULL){
                        if(wa_X_Y_b_Y_.find(t))
                            wa_X_Y_b_Y_.erase(t);
                        const auto& insertResult = ua_X_Y_b_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    auto& trueSet = trueAggrVars[0][{}];
                    auto& undefSet = undefAggrVars[0][{}];
                    if(p_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
                        if(trueSet.find(aggrKey)!=trueSet.end()){
                            trueSet.erase(aggrKey);
                        }
                    }
                    if(undefSet.find(aggrKey)==undefSet.end()){
                        if(trueSet.find(aggrKey)==trueSet.end()){
                            undefSet.insert(aggrKey);
                        }
                    }
                }else{
                    if(nua_X_Y_b_Y_.find(Tuple(t))==NULL){
                        const auto& insertResult = nua_X_Y_b_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            aggrKey[0]*=-1;
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
    if(tuple.getPredicateName() == &_b && tuple.size()==1){
        int Y = tuple[0];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_a_X_Y_b_Y_2_.getValues({Y});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                wa_X_Y_b_Y_.erase(*tuples.back());
                if(ua_X_Y_b_Y_.find(Tuple(t)) == NULL){
                    const auto& insertResult = ua_X_Y_b_Y_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                        {
                            std::vector<int> aggrKey({t[0]});
                            auto& trueSet = trueAggrVars[0][{}];
                            auto& undefSet = undefAggrVars[0][{}];
                            if(p_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
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
        }else{
            for(auto& pair : negativeAggrReason[0]){
                pair.second.erase(var);
            }
            const std::vector<const Tuple*>& tuplesNegative = np_a_X_Y_b_Y_2_.getValues({Y});
            for(const Tuple* tt : tuplesNegative){
                Tuple t(*tt);
                Tuple literal({t[0],t[1]},&_a);
                if(ua.find(literal)!=NULL || wa.find(literal)!=NULL){
                    nwa_X_Y_b_Y_.erase(t);
                    if(nua_X_Y_b_Y_.find(t)==NULL){
                        const auto& insertResult = nua_X_Y_b_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        auto& trueSet = trueNegativeAggrVars[0][{}];
                        auto& undefSet = undefNegativeAggrVars[0][{}];
                        aggrKey[0]*=-1;
                        if(np_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
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
        const std::vector<const Tuple*>& tuples0 = pa_1_.getValues({Y});
        const std::vector<const Tuple*>& tuplesU0 = ua_1_.getValues({Y});
        for(int i_0=0;i_0<tuples0.size()+tuplesU0.size();i_0++){
            const Tuple* tuple0;
            bool undef0=false;
            if(i_0<tuples0.size())                tuple0=tuples0[i_0];
            else{
                tuple0=tuplesU0[i_0-tuples0.size()];
                undef0=true;
            }
            int X = tuple0->at(0);
            Tuple t({X,Y,Y},&_a_X_Y_b_Y_);
            {
                std::vector<int> aggrKey({t[0]});
                if(aggrKey[0]>0){
                    if(ua_X_Y_b_Y_.find(Tuple(t))==NULL){
                        if(wa_X_Y_b_Y_.find(t))
                            wa_X_Y_b_Y_.erase(t);
                        const auto& insertResult = ua_X_Y_b_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    auto& trueSet = trueAggrVars[0][{}];
                    auto& undefSet = undefAggrVars[0][{}];
                    if(p_a_X_Y_b_Y_0_.getValues({aggrKey}).size()<=0){
                        if(trueSet.find(aggrKey)!=trueSet.end()){
                            trueSet.erase(aggrKey);
                        }
                    }
                    if(undefSet.find(aggrKey)==undefSet.end()){
                        if(trueSet.find(aggrKey)==trueSet.end()){
                            undefSet.insert(aggrKey);
                        }
                    }
                }else{
                    if(nua_X_Y_b_Y_.find(Tuple(t))==NULL){
                        const auto& insertResult = nua_X_Y_b_Y_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                            auto& trueSet = trueNegativeAggrVars[0][{}];
                            auto& undefSet = undefNegativeAggrVars[0][{}];
                            aggrKey[0]*=-1;
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
    std::cout<<"True join tuple"<<std::endl;
    for(const Tuple* t : wa_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"Undef join tuple"<<std::endl;
    for(const Tuple* t : ua_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"Negative True join tuple"<<std::endl;
    for(const Tuple* t : nwa_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"Negative Undef join tuple"<<std::endl;
    for(const Tuple* t : nua_X_Y_b_Y_.getTuples()){t->print();std::cout<<std::endl;}
    std::cout<<"ActualSum: "<<actualSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : trueAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"PossibleSum: "<<possibleSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : undefAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"NegativeActualSum: "<<actualNegativeSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : trueNegativeAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"NegativPossibleSum: "<<possibleNegativeSum[0][{}]<<std::endl;
    for(const std::vector<int>& key : undefNegativeAggrVars[0][{}])std::cout<<key[0]<<std::endl;
    std::cout<<"MaxNegativPossibleSum: "<<maxPossibleNegativeSum[0][{}]<<std::endl;
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
    predicateWSetMap[&_b]=&wb;
    predicateFSetMap[&_b]=&fb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateToAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&p_a_X_Y_b_Y_);
    predicateToAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&p_a_X_Y_b_Y_0_);
    predicateToAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&p_a_X_Y_b_Y_0_1_);
    predicateToAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&p_a_X_Y_b_Y_0_1_0_);
    predicateToAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&p_a_X_Y_b_Y_2_);
    predicateToAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&p_a_X_Y_b_Y_2_0_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_0_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_0_1_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_1_);
    predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&np_a_X_Y_b_Y_);
    predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&np_a_X_Y_b_Y_0_);
    predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&np_a_X_Y_b_Y_0_1_);
    predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&np_a_X_Y_b_Y_0_1_0_);
    predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&np_a_X_Y_b_Y_2_);
    predicateToNegativeAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&np_a_X_Y_b_Y_2_0_);
    predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&u_a_X_Y_b_Y_);
    predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&u_a_X_Y_b_Y_0_);
    predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&u_a_X_Y_b_Y_0_1_);
    predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&u_a_X_Y_b_Y_0_1_0_);
    predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&u_a_X_Y_b_Y_2_);
    predicateToUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&u_a_X_Y_b_Y_2_0_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_0_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_0_1_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&nu_a_X_Y_b_Y_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&nu_a_X_Y_b_Y_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&nu_a_X_Y_b_Y_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&nu_a_X_Y_b_Y_0_1_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&nu_a_X_Y_b_Y_2_);
    predicateToNegativeUndefAuxiliaryMaps[&_a_X_Y_b_Y_].push_back(&nu_a_X_Y_b_Y_2_0_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_0_);
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
                int undefPlusTrue = trueAggrVars[0][{}].size()+undefAggrVars[0][{}].size()+trueNegativeAggrVars[0][{}].size()+undefNegativeAggrVars[0][{}].size();
                //1
                if(!(undefPlusTrue>=1+maxPossibleNegativeSum[0][{}])){
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
                if(undefPlusTrue == 1){
                    tupleU=NULL;
                    if(tupleU == NULL){
                        for(auto undefKey = undefAggrVars[0][{}].begin();undefKey!=undefAggrVars[0][{}].end();undefKey++){
                            const std::vector<const Tuple*>* undefinedTuples = &u_a_X_Y_b_Y_0_.getValues(*undefKey);
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
                                const Tuple* tuple1 = ub.find(Tuple({undefinedTuples->at(0)->at(2)},&_b));
                                if(tuple1!=NULL){
                                    const auto & it1 = tupleToVar.find(*tuple1);
                                    if(it1 != tupleToVar.end()) {
                                        propagated=true;
                                        std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                        int sign = -1;
                                        propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>()}).first->second;
                                    }
                                }
                            }
                        }
                        for(auto undefKey = undefNegativeAggrVars[0][{}].begin();undefKey!=undefNegativeAggrVars[0][{}].end();undefKey++){
                            int X = undefKey->at(0);
                            X*=-1;
                            const std::vector<const Tuple*>* undefinedTuples = &nu_a_X_Y_b_Y_0_.getValues({X});
                            if(undefinedTuples->size()==1){

                                bool negativeJoinPropagated=false;
                                const Tuple* tupleU0 = ua.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a));
                                if(tupleU0!=NULL && !negativeJoinPropagated){
                                    Tuple tuple1 ({undefinedTuples->at(0)->at(2)},&_b);
                                    if(wb.find(tuple1)!=NULL){
                                        const auto & it0 = tupleToVar.find(*tupleU0);
                                        if(it0 != tupleToVar.end()) {
                                            negativeJoinPropagated=true;
                                            std::cout<<"Propagation Negated Negative join";tupleU0->print();std::cout<<std::endl;
                                            int sign = 1;
                                            propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>()}).first->second;
                                        }
                                    }
                                }
                                const Tuple* tupleU1 = ub.find(Tuple({undefinedTuples->at(0)->at(2)},&_b));
                                if(tupleU1!=NULL && !negativeJoinPropagated){
                                    Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a);
                                    if(wa.find(tuple0)!=NULL){
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
                    }
                }//close can prop if
                else{
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
            if(starter.getPredicateName()== &_a || starter.getPredicateName()== &_b){
                {
                    int undefPlusTrue = trueAggrVars[0][{}].size()+undefAggrVars[0][{}].size()+trueNegativeAggrVars[0][{}].size()+undefNegativeAggrVars[0][{}].size();
                    //1
                    if(!(undefPlusTrue>=1+maxPossibleNegativeSum[0][{}])){
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
                    if(undefPlusTrue == 1){
                        tupleU=NULL;
                        if(tupleU == NULL){
                            std::vector<int> local_reason;
                            local_reason.insert(local_reason.end(),negativeAggrReason[0][{}].begin(), negativeAggrReason[0][{}].end());
                            const auto & it = tupleToVar.find(Tuple(starter));
                            if(it!=tupleToVar.end()){
                                local_reason.push_back(it->second * (starter.isNegated() ? -1:1));
                            }
                            for(auto undefKey = undefAggrVars[0][{}].begin();undefKey!=undefAggrVars[0][{}].end();undefKey++){
                                const std::vector<const Tuple*>* undefinedTuples = &u_a_X_Y_b_Y_0_.getValues(*undefKey);
                                if(undefinedTuples->size()==1){

                                    const Tuple* tuple0 = ua.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a));
                                    if(tuple0!=NULL){
                                        const auto & it0 = tupleToVar.find(*tuple0);
                                        if(it0 != tupleToVar.end()) {
                                            propagated=true;
                                            std::cout<<"Propagation Negated";tuple0->print();std::cout<<std::endl;
                                            int sign = -1;
                                            propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                        }
                                    }
                                    const Tuple* tuple1 = ub.find(Tuple({undefinedTuples->at(0)->at(2)},&_b));
                                    if(tuple1!=NULL){
                                        const auto & it1 = tupleToVar.find(*tuple1);
                                        if(it1 != tupleToVar.end()) {
                                            propagated=true;
                                            std::cout<<"Propagation Negated";tuple1->print();std::cout<<std::endl;
                                            int sign = -1;
                                            propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                        }
                                    }
                                }
                            }
                            for(auto undefKey = undefNegativeAggrVars[0][{}].begin();undefKey!=undefNegativeAggrVars[0][{}].end();undefKey++){
                                int X = undefKey->at(0);
                                X*=-1;
                                const std::vector<const Tuple*>* undefinedTuples = &nu_a_X_Y_b_Y_0_.getValues({X});
                                if(undefinedTuples->size()==1){

                                    bool negativeJoinPropagated=false;
                                    const Tuple* tupleU0 = ua.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a));
                                    if(tupleU0!=NULL && !negativeJoinPropagated){
                                        Tuple tuple1 ({undefinedTuples->at(0)->at(2)},&_b);
                                        if(wb.find(tuple1)!=NULL){
                                            const auto & it0 = tupleToVar.find(*tupleU0);
                                            if(it0 != tupleToVar.end()) {
                                                negativeJoinPropagated=true;
                                                std::cout<<"Propagation Negated Negative join";tupleU0->print();std::cout<<std::endl;
                                                int sign = 1;
                                                propagatedLiteralsAndReasons.insert({it0->second*sign, std::vector<int>(local_reason)}).first->second;
                                            }
                                        }
                                    }
                                    const Tuple* tupleU1 = ub.find(Tuple({undefinedTuples->at(0)->at(2)},&_b));
                                    if(tupleU1!=NULL && !negativeJoinPropagated){
                                        Tuple tuple0 ({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_a);
                                        if(wa.find(tuple0)!=NULL){
                                            const auto & it1 = tupleToVar.find(*tupleU1);
                                            if(it1 != tupleToVar.end()) {
                                                negativeJoinPropagated=true;
                                                std::cout<<"Propagation Negated Negative join";tupleU1->print();std::cout<<std::endl;
                                                int sign = 1;
                                                propagatedLiteralsAndReasons.insert({it1->second*sign, std::vector<int>(local_reason)}).first->second;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }//close can prop if
                    else{
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
