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
const std::string _max = "max";
PredicateWSet wmax(1);
PredicateWSet umax(1);
const std::string _min = "min";
PredicateWSet wmin(1);
PredicateWSet umin(1);
const std::string _node = "node";
PredicateWSet wnode(1);
PredicateWSet unode(1);
const std::string _arc = "arc";
PredicateWSet warc(2);
PredicateWSet uarc(2);
const std::string _removed = "removed";
PredicateWSet wremoved(2);
PredicateWSet uremoved(2);
const std::string _arc_Y_X_not_removed_Y_X_ = "arc_Y_X_not_removed_Y_X_";
PredicateWSet warc_Y_X_not_removed_Y_X_(4);
PredicateWSet uarc_Y_X_not_removed_Y_X_(4);
PredicateWSet nwarc_Y_X_not_removed_Y_X_(4);
PredicateWSet nuarc_Y_X_not_removed_Y_X_(4);
std::unordered_map < DynamicCompilationVector*, std::set < VarsIndex > > trueAggrVars[1];
std::unordered_map < DynamicCompilationVector*, std::set < VarsIndex > > undefAggrVars[1];
std::unordered_map < DynamicCompilationVector*, std::set < VarsIndex > > trueNegativeAggrVars[1];
std::unordered_map < DynamicCompilationVector*, std::set < VarsIndex > > undefNegativeAggrVars[1];
DynamicTrie aggrVariable[1];
DynamicTrie sharedVariable[1];
std::unordered_map < DynamicCompilationVector*, ReasonTable > positiveAggrReason[1];
std::unordered_map < DynamicCompilationVector*, ReasonTable > negativeAggrReason[1];
std::unordered_map < DynamicCompilationVector*, int > actualSum[1];
std::unordered_map < DynamicCompilationVector*, int > possibleSum[1];
std::unordered_map < DynamicCompilationVector*, int > actualNegativeSum[1];
std::unordered_map < DynamicCompilationVector*, int > possibleNegativeSum[1];
std::unordered_map < DynamicCompilationVector*, int > maxPossibleNegativeSum[1];
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
AuxMap premoved_0_1_({0,1});
AuxMap uremoved_0_1_({0,1});
AuxMap parc_0_1_({0,1});
AuxMap uarc_0_1_({0,1});
AuxMap p_arc_Y_X_not_removed_Y_X_1_3_({1,3});
AuxMap u_arc_Y_X_not_removed_Y_X_1_3_({1,3});
AuxMap np_arc_Y_X_not_removed_Y_X_1_3_({1,3});
AuxMap nu_arc_Y_X_not_removed_Y_X_1_3_({1,3});
AuxMap p_arc_Y_X_not_removed_Y_X_0_({0});
AuxMap u_arc_Y_X_not_removed_Y_X_0_({0});
AuxMap np_arc_Y_X_not_removed_Y_X_0_({0});
AuxMap nu_arc_Y_X_not_removed_Y_X_0_({0});
AuxMap p_arc_Y_X_not_removed_Y_X_1_3_0_({1,3,0});
AuxMap u_arc_Y_X_not_removed_Y_X_1_3_0_({1,3,0});
AuxMap np_arc_Y_X_not_removed_Y_X_1_3_0_({1,3,0});
AuxMap nu_arc_Y_X_not_removed_Y_X_1_3_0_({1,3,0});
AuxMap p_arc_Y_X_not_removed_Y_X_0_1_({0,1});
AuxMap u_arc_Y_X_not_removed_Y_X_0_1_({0,1});
AuxMap np_arc_Y_X_not_removed_Y_X_0_1_({0,1});
AuxMap nu_arc_Y_X_not_removed_Y_X_0_1_({0,1});
AuxMap p_arc_Y_X_not_removed_Y_X_2_3_({2,3});
AuxMap u_arc_Y_X_not_removed_Y_X_2_3_({2,3});
AuxMap np_arc_Y_X_not_removed_Y_X_2_3_({2,3});
AuxMap nu_arc_Y_X_not_removed_Y_X_2_3_({2,3});
AuxMap pnode_0_({0});
AuxMap unode_0_({0});
AuxMap pmin_({});
AuxMap umin_({});
AuxMap pnode_({});
AuxMap unode_({});
AuxMap pmax_({});
AuxMap umax_({});
//printing aux maps needed for reasons of negative literals;
void Executor::explainAggrLiteral(int var,std::unordered_set<int>& reas){
    int v = var==-1?var:-var;
    std::cout << "Explain " << v << std::endl;
    PostponedReasonData* data = reasonMapping.getAt(v);
    if(data == nullptr || data->getPropagationLevel() == -1) return;
    const std::vector<int>* aggregates_id = &data->getAggregateId();
    for(int i=0; i < aggregates_id->size();i++){
        int aggr_index=aggregates_id->at(i);
        std::vector<int> sharedVars(data->getSharedVariables());
        DynamicCompilationVector* varsIndex=sharedVariable[aggr_index].addElements(sharedVars);
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
    if(tuple.getPredicateName() == &_arc){
        int Y = tuple[0];
        int X = tuple[1];
        if(var > 0){
            const Tuple negativeTuple1({Y,X},&_removed,true);
            const Tuple* tuple1 = uremoved.find(Tuple({Y,X},&_removed));
            if(wremoved.find(negativeTuple1)==NULL && tuple1==NULL){
                tuple1=&negativeTuple1;
                Tuple t({Y,X,Y,X},&_arc_Y_X_not_removed_Y_X_);
                {
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    if(firstVar>=0){
                        if(warc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(uarc_Y_X_not_removed_Y_X_.find(t))
                                uarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = warc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }
                    }else{
                        if(nwarc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(nuarc_Y_X_not_removed_Y_X_.find(t))
                                nuarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = nwarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                            {
                                const auto & it = tupleToVar.find(*tuple1);
                                if(it != tupleToVar.end()) {
                                    reas.insert(it->second*-1);
                                }
                            }
                        }
                    }
                }
                {
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    if(firstVar>=0){
                        if(warc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(uarc_Y_X_not_removed_Y_X_.find(t))
                                uarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = warc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                                {
                                    const auto & it = tupleToVar.find(*tuple1);
                                    if(it != tupleToVar.end()) {
                                        reas.insert(it->second*-1);
                                    }
                                }
                            }
                        }
                    }else{
                        if(nwarc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(nuarc_Y_X_not_removed_Y_X_.find(t))
                                nuarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = nwarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                            {
                                const auto & it = tupleToVar.find(*tuple1);
                                if(it != tupleToVar.end()) {
                                    reas.insert(it->second*-1);
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_arc_Y_X_not_removed_Y_X_0_1_.getValues({Y,X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uarc_Y_X_not_removed_Y_X_.erase(*tuplesU.back());
                {
                    //bound var1
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_arc_Y_X_not_removed_Y_X_0_1_.getValues({Y,X});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nuarc_Y_X_not_removed_Y_X_.erase(*tuplesNU.back());
                {
                    //bound var1
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
            }
        }
    }
    if(tuple.getPredicateName() == &_removed){
        int Y = tuple[0];
        int X = tuple[1];
        if(var < 0){
            const Tuple* tuple0 = warc.find(Tuple({Y,X},&_arc));
            if(tuple0!=NULL){
                Tuple t({Y,X,Y,X},&_arc_Y_X_not_removed_Y_X_);
                {
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    if(firstVar>=0){
                        if(warc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(uarc_Y_X_not_removed_Y_X_.find(t))
                                uarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = warc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                                {
                                    const auto & it = tupleToVar.find(*tuple0);
                                    if(it != tupleToVar.end()) {
                                        reas.insert(it->second);
                                    }
                                }
                            }
                        }
                    }else{
                        if(nwarc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(nuarc_Y_X_not_removed_Y_X_.find(t))
                                nuarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = nwarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                            {
                                const auto & it = tupleToVar.find(*tuple0);
                                if(it != tupleToVar.end()) {
                                    reas.insert(it->second);
                                }
                            }
                        }
                    }
                }
                {
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    if(firstVar>=0){
                        if(warc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(uarc_Y_X_not_removed_Y_X_.find(t))
                                uarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = warc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                                {
                                    const auto & it = tupleToVar.find(*tuple0);
                                    if(it != tupleToVar.end()) {
                                        reas.insert(it->second);
                                    }
                                }
                            }
                        }
                    }else{
                        if(nwarc_Y_X_not_removed_Y_X_.find(t)==NULL){
                            if(nuarc_Y_X_not_removed_Y_X_.find(t))
                                nuarc_Y_X_not_removed_Y_X_.erase(t);
                            const auto& insertResult = nwarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                            if (insertResult.second) {
                                for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex=sharedVariable[0].addElements(sharedBodyVars);
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
                            {
                                const auto & it = tupleToVar.find(*tuple0);
                                if(it != tupleToVar.end()) {
                                    reas.insert(it->second);
                                }
                            }
                        }
                    }
                }
            }
        }else{
            const std::vector<const Tuple*>& tuplesU = u_arc_Y_X_not_removed_Y_X_2_3_.getValues({Y,X});
            while(!tuplesU.empty()){
                Tuple t(*tuplesU.back());
                uarc_Y_X_not_removed_Y_X_.erase(*tuplesU.back());
                {
                    //bound var1
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                        if(undefSet.find(aggrVarsIndex)!=undefSet.end()){
                            undefSet.erase(aggrVarsIndex);
                        }
                    }
                    auto& reas = negativeAggrReason[0][varsIndex];
                    while(reas.getCurrentLevel()<currentReasonLevel)
                        reas.addLevel();
                    reas.insert(var);
                }
            }
            const std::vector<const Tuple*>& tuplesNU = nu_arc_Y_X_not_removed_Y_X_2_3_.getValues({Y,X});
            while(!tuplesNU.empty()){
                Tuple t(*tuplesNU.back());
                nuarc_Y_X_not_removed_Y_X_.erase(*tuplesNU.back());
                {
                    //bound var1
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    //bound var3
                    std::vector<int> aggrKey({t[0]});
                    DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                    int firstVar=aggrKeyIndex->operator[](0);
                    VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    if(nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
        std::cout<<"Pending prop "<<*propagatedLiterals.begin()<<std::endl;
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
    if(tuple.getPredicateName() == &_arc && tuple.size()==2){
        int Y = tuple[0];
        int X = tuple[1];
        if(var > 0){
            const std::vector<const Tuple*>& tuples = p_arc_Y_X_not_removed_Y_X_0_1_.getValues({Y,X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                warc_Y_X_not_removed_Y_X_.erase(*tuples.back());
                if(uarc_Y_X_not_removed_Y_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_arc_Y_X_not_removed_Y_X_0_1_.getValues({Y,X});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwarc_Y_X_not_removed_Y_X_.erase(*tuplesN.back());
                if(nuarc_Y_X_not_removed_Y_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nuarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
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
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
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
                }
            }
        }
        const Tuple negativeTuple1({Y,X},&_removed,true);
        const Tuple* tuple1 = uremoved.find(Tuple({Y,X},&_removed));
        bool undef1 = false;
        if(tuple1!=NULL){
            undef1 = true;
        }else if(wremoved.find(negativeTuple1)==NULL){
            tuple1=&negativeTuple1;
        }
        if(tuple1!=NULL){
            Tuple t({Y,X,Y,X},&_arc_Y_X_not_removed_Y_X_);
            {
                std::vector<int> aggrKey({t[0]});
                DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                int firstVar=aggrKeyIndex->operator[](0);
                VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(uarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(warc_Y_X_not_removed_Y_X_.find(t))
                            warc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = uarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueAggrVars[0][varsIndex];
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    if(nuarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(nwarc_Y_X_not_removed_Y_X_.find(t))
                            nwarc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = nuarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                int firstVar=aggrKeyIndex->operator[](0);
                VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(uarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(warc_Y_X_not_removed_Y_X_.find(t))
                            warc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = uarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueAggrVars[0][varsIndex];
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    if(nuarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(nwarc_Y_X_not_removed_Y_X_.find(t))
                            nwarc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = nuarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
    if(tuple.getPredicateName() == &_removed && tuple.size()==2){
        int Y = tuple[0];
        int X = tuple[1];
        if(var < 0){
            const std::vector<const Tuple*>& tuples = p_arc_Y_X_not_removed_Y_X_2_3_.getValues({Y,X});
            while(!tuples.empty()){
                Tuple t(*tuples.back());
                warc_Y_X_not_removed_Y_X_.erase(*tuples.back());
                if(uarc_Y_X_not_removed_Y_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = uarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        std::vector<int>sharedBodyVars({X,X});
                        DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                        auto& trueSet = trueAggrVars[0][varsIndex];
                        auto& undefSet = undefAggrVars[0][varsIndex];
                        if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
            const std::vector<const Tuple*>& tuplesN = np_arc_Y_X_not_removed_Y_X_2_3_.getValues({Y,X});
            while(!tuplesN.empty()){
                Tuple t(*tuplesN.back());
                nwarc_Y_X_not_removed_Y_X_.erase(*tuplesN.back());
                if(nuarc_Y_X_not_removed_Y_X_.find(Tuple(t)) == NULL){
                    const auto& insertResult = nuarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                    if (insertResult.second) {
                        for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    {
                        std::vector<int> aggrKey({t[0]});
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
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
                        DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                        int firstVar = aggrKeyIndex->operator[](0);
                        VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);
                        if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
                            std::vector<int>sharedBodyVars({X,X});
                            DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
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
                }
            }
        }
        const Tuple* tuple0 = warc.find(Tuple({Y,X},&_arc));
        bool undef0 = false;
        if(tuple0==NULL){
            tuple0 = uarc.find(Tuple({Y,X},&_arc));
            undef0 = true;
        }
        if(tuple0!=NULL){
            Tuple t({Y,X,Y,X},&_arc_Y_X_not_removed_Y_X_);
            {
                std::vector<int> aggrKey({t[0]});
                DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                int firstVar=aggrKeyIndex->operator[](0);
                VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(uarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(warc_Y_X_not_removed_Y_X_.find(t))
                            warc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = uarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueAggrVars[0][varsIndex];
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    if(nuarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(nwarc_Y_X_not_removed_Y_X_.find(t))
                            nwarc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = nuarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                DynamicCompilationVector* aggrKeyIndex = aggrVariable[0].addElements(aggrKey);
                int firstVar=aggrKeyIndex->operator[](0);
                VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);
                if(firstVar>=0){
                    if(uarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(warc_Y_X_not_removed_Y_X_.find(t))
                            warc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = uarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueAggrVars[0][varsIndex];
                    auto& undefSet = undefAggrVars[0][varsIndex];
                    if(p_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
                    if(nuarc_Y_X_not_removed_Y_X_.find(Tuple(t))==NULL){
                        if(nwarc_Y_X_not_removed_Y_X_.find(t))
                            nwarc_Y_X_not_removed_Y_X_.erase(t);
                        const auto& insertResult = nuarc_Y_X_not_removed_Y_X_.insert(Tuple(t));
                        if (insertResult.second) {
                            for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_]){
                                auxMap -> insert2(*insertResult.first);
                            }
                        }
                    }
                    std::vector<int>sharedBodyVars({X,X});
                    DynamicCompilationVector* varsIndex = sharedVariable[0].addElements(sharedBodyVars);
                    auto& trueSet = trueNegativeAggrVars[0][varsIndex];
                    auto& undefSet = undefNegativeAggrVars[0][varsIndex];
                    if(np_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,t[0]}).size()<=0){
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
    predicateWSetMap[&_max]=&wmax;
    predicateUSetMap[&_max]=&umax;
    stringToUniqueStringPointer["max"] = &_max;
    predicateWSetMap[&_min]=&wmin;
    predicateUSetMap[&_min]=&umin;
    stringToUniqueStringPointer["min"] = &_min;
    predicateWSetMap[&_node]=&wnode;
    predicateUSetMap[&_node]=&unode;
    stringToUniqueStringPointer["node"] = &_node;
    predicateWSetMap[&_arc]=&warc;
    predicateUSetMap[&_arc]=&uarc;
    stringToUniqueStringPointer["arc"] = &_arc;
    predicateWSetMap[&_removed]=&wremoved;
    predicateUSetMap[&_removed]=&uremoved;
    stringToUniqueStringPointer["removed"] = &_removed;
    predicateWSetMap[&_arc]=&warc;
    predicateUSetMap[&_arc]=&uarc;
    stringToUniqueStringPointer["arc"] = &_arc;
    predicateWSetMap[&_removed]=&wremoved;
    predicateUSetMap[&_removed]=&uremoved;
    stringToUniqueStringPointer["removed"] = &_removed;
    predicateToAuxiliaryMaps[&_min].push_back(&pmin_);
    predicateToAuxiliaryMaps[&_node].push_back(&pnode_);
    predicateToAuxiliaryMaps[&_node].push_back(&pnode_0_);
    predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&p_arc_Y_X_not_removed_Y_X_0_);
    predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&p_arc_Y_X_not_removed_Y_X_0_1_);
    predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&p_arc_Y_X_not_removed_Y_X_1_3_);
    predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&p_arc_Y_X_not_removed_Y_X_1_3_0_);
    predicateToAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&p_arc_Y_X_not_removed_Y_X_2_3_);
    predicateToAuxiliaryMaps[&_max].push_back(&pmax_);
    predicateToAuxiliaryMaps[&_arc].push_back(&parc_0_1_);
    predicateToAuxiliaryMaps[&_removed].push_back(&premoved_0_1_);
    predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&np_arc_Y_X_not_removed_Y_X_0_);
    predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&np_arc_Y_X_not_removed_Y_X_0_1_);
    predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&np_arc_Y_X_not_removed_Y_X_1_3_);
    predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&np_arc_Y_X_not_removed_Y_X_1_3_0_);
    predicateToNegativeAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&np_arc_Y_X_not_removed_Y_X_2_3_);
    predicateToUndefAuxiliaryMaps[&_min].push_back(&umin_);
    predicateToUndefAuxiliaryMaps[&_node].push_back(&unode_);
    predicateToUndefAuxiliaryMaps[&_node].push_back(&unode_0_);
    predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&u_arc_Y_X_not_removed_Y_X_0_);
    predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&u_arc_Y_X_not_removed_Y_X_0_1_);
    predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&u_arc_Y_X_not_removed_Y_X_1_3_);
    predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&u_arc_Y_X_not_removed_Y_X_1_3_0_);
    predicateToUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&u_arc_Y_X_not_removed_Y_X_2_3_);
    predicateToUndefAuxiliaryMaps[&_max].push_back(&umax_);
    predicateToUndefAuxiliaryMaps[&_arc].push_back(&uarc_0_1_);
    predicateToUndefAuxiliaryMaps[&_removed].push_back(&uremoved_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&nu_arc_Y_X_not_removed_Y_X_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&nu_arc_Y_X_not_removed_Y_X_0_1_);
    predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&nu_arc_Y_X_not_removed_Y_X_1_3_);
    predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&nu_arc_Y_X_not_removed_Y_X_1_3_0_);
    predicateToNegativeUndefAuxiliaryMaps[&_arc_Y_X_not_removed_Y_X_].push_back(&nu_arc_Y_X_not_removed_Y_X_2_3_);
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
            tuples = &pnode_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &unode_.getValues({});
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
                const std::vector<const Tuple* >* tuples;
                tuples = &pmin_.getValues({});
                const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                if(tupleU == NULL){
                    tuplesU = &umin_.getValues({});
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
                    int M = (*tuple1)[0];
                    std::vector<int>sharedBodyV({X,X});
                    DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                    int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                    //M
                    if(!(undefPlusTrue>=M)){
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
                            std::vector<int>bodyV({X,X});
                            DynamicCompilationVector* bodyVarsIndex = sharedVariable[0].addElements(bodyV);
                            int undefPlusTrue = trueAggrVars[0][bodyVarsIndex].size()+undefAggrVars[0][bodyVarsIndex].size()+trueNegativeAggrVars[0][bodyVarsIndex].size()+undefNegativeAggrVars[0][bodyVarsIndex].size();
                            bool propagated=false;
                            if(undefPlusTrue == M){
                                std::vector<int>sharedVars({X,X});
                                DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                    const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                    if(undefinedTuples->size()==1){

                                        const Tuple* aggrTuple0 = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
                                        if(aggrTuple0!=NULL){
                                            const auto & it0 = tupleToVar.find(*aggrTuple0);
                                            if(it0 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = -1;
                                                propagatedLiterals.insert(it0->second*sign);
                                            }
                                        }
                                        const Tuple* aggrTuple1 = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                        if(aggrTuple1!=NULL){
                                            const auto & it1 = tupleToVar.find(*aggrTuple1);
                                            if(it1 != tupleToVar.end()) {
                                                propagated=true;
                                                int sign = 1;
                                                propagatedLiterals.insert(it1->second*sign);
                                            }
                                        }
                                    }
                                }
                                for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                    if(undefinedTuples->size()==1){

                                        {
                                            const Tuple* aggrTupleU = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
                                            if(aggrTupleU!=NULL){
                                                const auto & it = tupleToVar.find(*aggrTupleU);
                                                if(it != tupleToVar.end()) {
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it->second*sign);
                                                }
                                            }
                                        }
                                        {
                                            const Tuple* aggrTupleU = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                            if(aggrTupleU!=NULL){
                                                const auto & it = tupleToVar.find(*aggrTupleU);
                                                if(it != tupleToVar.end()) {
                                                    int sign = 1;
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
            }
        }//close local scope
        {
            const Tuple * tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple* >* tuples;
            tuples = &pnode_.getValues({});
            const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
            if(tupleU == NULL){
                tuplesU = &unode_.getValues({});
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
                const std::vector<const Tuple* >* tuples;
                tuples = &pmax_.getValues({});
                const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                if(tupleU == NULL){
                    tuplesU = &umax_.getValues({});
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
                    int M = (*tuple1)[0];
                    std::vector<int>sharedBodyV({X,X});
                    DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                    if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=M+1){
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
                            std::vector<int>sharedV({X,X});
                            DynamicCompilationVector* sharedIndex = sharedVariable[0].addElements(sharedV);
                            if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == M){
                                std::vector<int>sharedVars({X,X});
                                DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                    const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                        bool found=false;
                                        if(!found){
                                            const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                            const Tuple* aggrTuple1 = wremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                            const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                            const Tuple negativeTuple1 ({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed,true);
                                            if(aggrTupleU0!=NULL && (aggrTuple1==NULL && aggrTupleU1==NULL)){
                                                const auto & it = tupleToVar.find(*aggrTupleU0);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = 1;
                                                    found=true;
                                                    propagatedLiterals.insert(it->second*sign);
                                                }
                                            }
                                        }
                                        if(!found){
                                            const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                            const Tuple* aggrTuple0 = warc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                            const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                            if(aggrTupleU1!=NULL && aggrTuple0!=NULL ){
                                                const auto & it = tupleToVar.find(*aggrTupleU1);
                                                if(it != tupleToVar.end()) {
                                                    propagated=true;
                                                    int sign = -1;
                                                    found=true;
                                                    propagatedLiterals.insert(it->second*sign);
                                                }
                                            }
                                        }
                                    }
                                }
                                for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                    const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                    for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                        bool negativeJoinPropagated=false;
                                        const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc));
                                        if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                            Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed);
                                            if((wremoved.find(aggrTuple1)==NULL && uremoved.find(aggrTuple1)==NULL) ){
                                                const auto & it0 = tupleToVar.find(*aggrTupleU0);
                                                if(it0 != tupleToVar.end()) {
                                                    negativeJoinPropagated=true;
                                                    int sign = 1;
                                                    propagatedLiterals.insert(it0->second*sign);
                                                }
                                            }
                                        }
                                        const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed));
                                        if(aggrTupleU1!=NULL && !negativeJoinPropagated){
                                            Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc);
                                            if((warc.find(aggrTuple0)!=NULL) ){
                                                const auto & it1 = tupleToVar.find(*aggrTupleU1);
                                                if(it1 != tupleToVar.end()) {
                                                    negativeJoinPropagated=true;
                                                    int sign = -1;
                                                    propagatedLiterals.insert(it1->second*sign);
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
        if(starter.getPredicateName() == &_max) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int M = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pnode_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &unode_.getValues({});
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
                        int X = (*tuple1)[0];
                        std::vector<int>sharedBodyV({X,X});
                        DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                        if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=M+1){
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
                                    if(tuple1!=tupleU){
                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(-1,itr->second);
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(-1,X);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                    }
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                bool propagated=false;
                                std::vector<int>sharedV({X,X});
                                DynamicCompilationVector* sharedIndex = sharedVariable[0].addElements(sharedV);
                                if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == M){
                                    std::vector<int>sharedVars({X,X});
                                    DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                const Tuple* aggrTuple1 = wremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                const Tuple negativeTuple1 ({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed,true);
                                                if(aggrTupleU0!=NULL && (aggrTuple1==NULL && aggrTupleU1==NULL)){
                                                    std::vector<int> reas;
                                                    if(aggrTupleU1 == NULL){
                                                        const auto & it_negativeTuple1 = tupleToVar.find(negativeTuple1);
                                                        if(it_negativeTuple1!=tupleToVar.end()){
                                                            reas.push_back(it_negativeTuple1->second * -1);
                                                        }//closing if
                                                    }//closing if
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                const Tuple* aggrTuple0 = warc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                if(aggrTupleU1!=NULL && aggrTuple0!=NULL ){
                                                    std::vector<int> reas;
                                                    if(aggrTuple0!=NULL){
                                                        const auto & it_aggrTuple0 = tupleToVar.find(*aggrTuple0);
                                                        if(it_aggrTuple0!=tupleToVar.end()){
                                                            reas.push_back(it_aggrTuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = -1;
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                            bool negativeJoinPropagated=false;
                                            const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc));
                                            if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed);
                                                if((wremoved.find(aggrTuple1)==NULL && uremoved.find(aggrTuple1)==NULL) ){
                                                    const auto & it1 = tupleToVar.find(aggrTuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second*-1);
                                                    }
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
                                                            reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed));
                                            if(aggrTupleU1!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc);
                                                if((warc.find(aggrTuple0)!=NULL) ){
                                                    const auto & it0 = tupleToVar.find(aggrTuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        reas.push_back(it0->second);
                                                    }
                                                    const auto & it1 = tupleToVar.find(*aggrTupleU1);
                                                    if(it1 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.insert(it1->second*sign);
                                                        bool added = reasonMapping.addPropagation(it1->second*sign);
                                                        if(added){
                                                            reasonMapping.setPropLevelToLit(it1->second*sign,currentReasonLevel);
                                                            reasonMapping.addAggrToLit(it1->second*sign,0,true);
                                                            {
                                                                const auto & itr = tupleToVar.find(Tuple(starter));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                }
                                                            }
                                                            if(tuple1!=tupleU){
                                                                const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                                }
                                                            }
                                                            reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it1->second*sign,v);
                                                            }
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
                    }
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_arc || starter.getPredicateName()== &_removed){
                for(auto sharedVarsIt = undefAggrVars[0].begin();sharedVarsIt != undefAggrVars[0].end();sharedVarsIt++){
                    int X = sharedVarsIt->first->operator[](0);
                    tupleU=NULL;
                    const Tuple * tuple1 = (wnode.find(Tuple({X},&_node)));
                    if(!tuple1 && !tupleU ){
                        tuple1 = tupleU = (unode.find(Tuple({X},&_node)));
                        tupleUNegated = false;
                    }
                    if(tuple1){
                        const std::vector<const Tuple* >* tuples;
                        tuples = &pmax_.getValues({});
                        const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                        if(tupleU == NULL){
                            tuplesU = &umax_.getValues({});
                        }
                        for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){
                            const Tuple * tuple2 = NULL;
                            if(i<tuples->size()){
                                tuple2 = tuples->at(i);
                                if(tuplesU != &EMPTY_TUPLES) {
                                    tupleU = NULL;
                                }
                            }
                            else {
                                tuple2 = tuplesU->at(i-tuples->size());
                                tupleU = tuple2;
                                tupleUNegated = false;
                            }
                            int M = (*tuple2)[0];
                            std::vector<int>sharedBodyV({X,X});
                            DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                            if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=M+1){
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
                                        if(tuple2!=tupleU){
                                            const auto & it = tupleToVar.find(Tuple(*tuple2));
                                            if(it!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,it->second);
                                            }
                                        }
                                        reasonMapping.addSharedVarToLit(-1,X);
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
                                            if(tuple2!=tupleU){
                                                const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                if(itr!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                }
                                            }
                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                        }
                                    }
                                }
                            }else{
                                bool propagated=false;
                                std::vector<int>sharedV({X,X});
                                DynamicCompilationVector* sharedIndex = sharedVariable[0].addElements(sharedV);
                                if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == M){
                                    if(tupleU == NULL){
                                        std::vector<int>sharedVars({X,X});
                                        DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                        for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                            const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                            for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                                bool found=false;
                                                if(!found){
                                                    const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                    const Tuple* aggrTuple1 = wremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                    const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                    const Tuple negativeTuple1 ({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed,true);
                                                    if(aggrTupleU0!=NULL && (aggrTuple1==NULL && aggrTupleU1==NULL)){
                                                        std::vector<int> reas;
                                                        if(aggrTupleU1 == NULL){
                                                            const auto & it_negativeTuple1 = tupleToVar.find(negativeTuple1);
                                                            if(it_negativeTuple1!=tupleToVar.end()){
                                                                reas.push_back(it_negativeTuple1->second * -1);
                                                            }//closing if
                                                        }//closing if
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
                                                                if(tuple2!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                    }
                                                                }
                                                                reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                                reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                                for(int v : reas){
                                                                    reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                                if(!found){
                                                    const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                    const Tuple* aggrTuple0 = warc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                    const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                    if(aggrTupleU1!=NULL && aggrTuple0!=NULL ){
                                                        std::vector<int> reas;
                                                        if(aggrTuple0!=NULL){
                                                            const auto & it_aggrTuple0 = tupleToVar.find(*aggrTuple0);
                                                            if(it_aggrTuple0!=tupleToVar.end()){
                                                                reas.push_back(it_aggrTuple0->second * 1);
                                                            }//closing if
                                                        }//closing if
                                                        const auto & it = tupleToVar.find(*aggrTupleU1);
                                                        if(it != tupleToVar.end()) {
                                                            propagated=true;
                                                            int sign = -1;
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
                                                                if(tuple2!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                    }
                                                                }
                                                                reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                            const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                            for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                                bool negativeJoinPropagated=false;
                                                const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                    std::vector<int> reas;
                                                    Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed);
                                                    if((wremoved.find(aggrTuple1)==NULL && uremoved.find(aggrTuple1)==NULL) ){
                                                        const auto & it1 = tupleToVar.find(aggrTuple1);
                                                        if(it1 != tupleToVar.end()) {
                                                            reas.push_back(it1->second*-1);
                                                        }
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
                                                                if(tuple2!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                    }
                                                                }
                                                                reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                                reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                                for(int v : reas){
                                                                    reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                                const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                if(aggrTupleU1!=NULL && !negativeJoinPropagated){
                                                    std::vector<int> reas;
                                                    Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc);
                                                    if((warc.find(aggrTuple0)!=NULL) ){
                                                        const auto & it0 = tupleToVar.find(aggrTuple0);
                                                        if(it0 != tupleToVar.end()) {
                                                            reas.push_back(it0->second);
                                                        }
                                                        const auto & it1 = tupleToVar.find(*aggrTupleU1);
                                                        if(it1 != tupleToVar.end()) {
                                                            negativeJoinPropagated=true;
                                                            int sign = -1;
                                                            propagatedLiterals.insert(it1->second*sign);
                                                            bool added = reasonMapping.addPropagation(it1->second*sign);
                                                            if(added){
                                                                reasonMapping.setPropLevelToLit(it1->second*sign,currentReasonLevel);
                                                                reasonMapping.addAggrToLit(it1->second*sign,0,true);
                                                                {
                                                                    const auto & itr = tupleToVar.find(Tuple(starter));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it1->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                    }
                                                                }
                                                                if(tuple1!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                                    }
                                                                }
                                                                if(tuple2!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                                    }
                                                                }
                                                                reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                                reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                                for(int v : reas){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,v);
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
                    }
                    //nested join closed
                }
            }
        }//local scope
        if(starter.getPredicateName() == &_node) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int X = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pmin_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &umin_.getValues({});
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
                        int M = (*tuple1)[0];
                        std::vector<int>sharedBodyV({X,X});
                        DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                        int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                        //M
                        if(!(undefPlusTrue>=M)){
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
                                    if(tuple1!=tupleU){
                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(-1,itr->second);
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(-1,X);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                    }
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                std::vector<int>bodyV({X,X});
                                DynamicCompilationVector* bodyVarsIndex = sharedVariable[0].addElements(bodyV);
                                int undefPlusTrue = trueAggrVars[0][bodyVarsIndex].size()+undefAggrVars[0][bodyVarsIndex].size()+trueNegativeAggrVars[0][bodyVarsIndex].size()+undefNegativeAggrVars[0][bodyVarsIndex].size();
                                bool propagated=false;
                                if(undefPlusTrue == M){
                                    std::vector<int>sharedVars({X,X});
                                    DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* aggrTuple0 = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
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
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                    }
                                                }
                                            }
                                            const Tuple* aggrTuple1 = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                            if(aggrTuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*aggrTuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
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
                                                        if(tuple1!=tupleU){
                                                            const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                            if(itr!=tupleToVar.end()){
                                                                reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                            }
                                                        }
                                                        reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                        reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        if(undefinedTuples->size()==1){

                                            {
                                                const Tuple* aggrTupleU = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                        }
                                                    }
                                                }
                                            }
                                            {
                                                const Tuple* aggrTupleU = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                                if(aggrTupleU!=NULL){
                                                    const auto & it = tupleToVar.find(*aggrTupleU);
                                                    if(it != tupleToVar.end()) {
                                                        int sign = 1;
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                    }
                }//close loop nested join
            }//close loop nested join
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int X = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pmax_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &umax_.getValues({});
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
                        int M = (*tuple1)[0];
                        std::vector<int>sharedBodyV({X,X});
                        DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                        if((int)(trueAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size())>=M+1){
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
                                    if(tuple1!=tupleU){
                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(-1,itr->second);
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(-1,X);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                    }
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                bool propagated=false;
                                std::vector<int>sharedV({X,X});
                                DynamicCompilationVector* sharedIndex = sharedVariable[0].addElements(sharedV);
                                if((int)(trueAggrVars[0][sharedIndex].size()+trueNegativeAggrVars[0][sharedIndex].size()) == M){
                                    std::vector<int>sharedVars({X,X});
                                    DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){
                                            bool found=false;
                                            if(!found){
                                                const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                const Tuple* aggrTuple1 = wremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                const Tuple negativeTuple1 ({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed,true);
                                                if(aggrTupleU0!=NULL && (aggrTuple1==NULL && aggrTupleU1==NULL)){
                                                    std::vector<int> reas;
                                                    if(aggrTupleU1 == NULL){
                                                        const auto & it_negativeTuple1 = tupleToVar.find(negativeTuple1);
                                                        if(it_negativeTuple1!=tupleToVar.end()){
                                                            reas.push_back(it_negativeTuple1->second * -1);
                                                        }//closing if
                                                    }//closing if
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            if(!found){
                                                const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2), undefinedTuples->at(iUndef)->at(3)},&_removed));
                                                const Tuple* aggrTuple0 = warc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0), undefinedTuples->at(iUndef)->at(1)},&_arc));
                                                if(aggrTupleU1!=NULL && aggrTuple0!=NULL ){
                                                    std::vector<int> reas;
                                                    if(aggrTuple0!=NULL){
                                                        const auto & it_aggrTuple0 = tupleToVar.find(*aggrTuple0);
                                                        if(it_aggrTuple0!=tupleToVar.end()){
                                                            reas.push_back(it_aggrTuple0->second * 1);
                                                        }//closing if
                                                    }//closing if
                                                    const auto & it = tupleToVar.find(*aggrTupleU1);
                                                    if(it != tupleToVar.end()) {
                                                        propagated=true;
                                                        int sign = -1;
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){

                                            bool negativeJoinPropagated=false;
                                            const Tuple* aggrTupleU0 = uarc.find(Tuple({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc));
                                            if(aggrTupleU0!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple aggrTuple1 ({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed);
                                                if((wremoved.find(aggrTuple1)==NULL && uremoved.find(aggrTuple1)==NULL) ){
                                                    const auto & it1 = tupleToVar.find(aggrTuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        reas.push_back(it1->second*-1);
                                                    }
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
                                                            reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it0->second*sign,v);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                            const Tuple* aggrTupleU1 = uremoved.find(Tuple({undefinedTuples->at(iUndef)->at(2),undefinedTuples->at(iUndef)->at(3)},&_removed));
                                            if(aggrTupleU1!=NULL && !negativeJoinPropagated){
                                                std::vector<int> reas;
                                                Tuple aggrTuple0 ({undefinedTuples->at(iUndef)->at(0),undefinedTuples->at(iUndef)->at(1)},&_arc);
                                                if((warc.find(aggrTuple0)!=NULL) ){
                                                    const auto & it0 = tupleToVar.find(aggrTuple0);
                                                    if(it0 != tupleToVar.end()) {
                                                        reas.push_back(it0->second);
                                                    }
                                                    const auto & it1 = tupleToVar.find(*aggrTupleU1);
                                                    if(it1 != tupleToVar.end()) {
                                                        negativeJoinPropagated=true;
                                                        int sign = -1;
                                                        propagatedLiterals.insert(it1->second*sign);
                                                        bool added = reasonMapping.addPropagation(it1->second*sign);
                                                        if(added){
                                                            reasonMapping.setPropLevelToLit(it1->second*sign,currentReasonLevel);
                                                            reasonMapping.addAggrToLit(it1->second*sign,0,true);
                                                            {
                                                                const auto & itr = tupleToVar.find(Tuple(starter));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second * (starter.isNegated() ? -1:1));
                                                                }
                                                            }
                                                            if(tuple1!=tupleU){
                                                                const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                                }
                                                            }
                                                            reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                            for(int v : reas){
                                                                reasonMapping.addBodyLitToLit(it1->second*sign,v);
                                                            }
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
                    }
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        if(starter.getPredicateName() == &_min) { 
            const Tuple * tuple0 = &starter;
            if(facts[i] > 0){
                {
                    const Tuple * tupleU = NULL;
                    bool tupleUNegated = false;
                    int M = (*tuple0)[0];
                    const std::vector<const Tuple* >* tuples;
                    tuples = &pnode_.getValues({});
                    const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                    if(tupleU == NULL){
                        tuplesU = &unode_.getValues({});
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
                        int X = (*tuple1)[0];
                        std::vector<int>sharedBodyV({X,X});
                        DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                        int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                        //M
                        if(!(undefPlusTrue>=M)){
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
                                    if(tuple1!=tupleU){
                                        const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                        if(itr!=tupleToVar.end()){
                                            reasonMapping.addBodyLitToLit(-1,itr->second);
                                        }
                                    }
                                    reasonMapping.addSharedVarToLit(-1,X);
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
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                        reasonMapping.addSharedVarToLit(it->second*sign,X);
                                    }
                                }
                            }
                        }
                        if(tupleU == NULL){
                            {
                                std::vector<int>bodyV({X,X});
                                DynamicCompilationVector* bodyVarsIndex = sharedVariable[0].addElements(bodyV);
                                int undefPlusTrue = trueAggrVars[0][bodyVarsIndex].size()+undefAggrVars[0][bodyVarsIndex].size()+trueNegativeAggrVars[0][bodyVarsIndex].size()+undefNegativeAggrVars[0][bodyVarsIndex].size();
                                bool propagated=false;
                                if(undefPlusTrue == M){
                                    std::vector<int>sharedVars({X,X});
                                    DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                    for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        if(undefinedTuples->size()==1){

                                            const Tuple* aggrTuple0 = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
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
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                        reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                    }
                                                }
                                            }
                                            const Tuple* aggrTuple1 = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                            if(aggrTuple1!=NULL){
                                                const auto & it1 = tupleToVar.find(*aggrTuple1);
                                                if(it1 != tupleToVar.end()) {
                                                    propagated=true;
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
                                                        if(tuple1!=tupleU){
                                                            const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                            if(itr!=tupleToVar.end()){
                                                                reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                            }
                                                        }
                                                        reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                        reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                        const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                        if(undefinedTuples->size()==1){

                                            {
                                                const Tuple* aggrTupleU = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                        }
                                                    }
                                                }
                                            }
                                            {
                                                const Tuple* aggrTupleU = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                                if(aggrTupleU!=NULL){
                                                    const auto & it = tupleToVar.find(*aggrTupleU);
                                                    if(it != tupleToVar.end()) {
                                                        int sign = 1;
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
                                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                    }
                }//close loop nested join
            }//close loop nested join
        }//close predicate joins
        {
            bool tupleUNegated = false;
            const Tuple * tupleU = NULL;
            if(starter.getPredicateName()== &_arc || starter.getPredicateName()== &_removed){
                for(auto sharedVarsIt = undefAggrVars[0].begin();sharedVarsIt != undefAggrVars[0].end();sharedVarsIt++){
                    int X = sharedVarsIt->first->operator[](0);
                    tupleU=NULL;
                    const Tuple * tuple1 = (wnode.find(Tuple({X},&_node)));
                    if(!tuple1 && !tupleU ){
                        tuple1 = tupleU = (unode.find(Tuple({X},&_node)));
                        tupleUNegated = false;
                    }
                    if(tuple1){
                        const std::vector<const Tuple* >* tuples;
                        tuples = &pmin_.getValues({});
                        const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;
                        if(tupleU == NULL){
                            tuplesU = &umin_.getValues({});
                        }
                        for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){
                            const Tuple * tuple2 = NULL;
                            if(i<tuples->size()){
                                tuple2 = tuples->at(i);
                                if(tuplesU != &EMPTY_TUPLES) {
                                    tupleU = NULL;
                                }
                            }
                            else {
                                tuple2 = tuplesU->at(i-tuples->size());
                                tupleU = tuple2;
                                tupleUNegated = false;
                            }
                            int M = (*tuple2)[0];
                            std::vector<int>sharedBodyV({X,X});
                            DynamicCompilationVector* sharedVarsIndex=sharedVariable[0].addElements(sharedBodyV);
                            int undefPlusTrue = trueAggrVars[0][sharedVarsIndex].size()+undefAggrVars[0][sharedVarsIndex].size()+trueNegativeAggrVars[0][sharedVarsIndex].size()+undefNegativeAggrVars[0][sharedVarsIndex].size();
                            //M
                            if(!(undefPlusTrue>=M)){
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
                                        if(tuple2!=tupleU){
                                            const auto & it = tupleToVar.find(Tuple(*tuple2));
                                            if(it!=tupleToVar.end()){
                                                reasonMapping.addBodyLitToLit(-1,it->second);
                                            }
                                        }
                                        reasonMapping.addSharedVarToLit(-1,X);
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
                                            if(tuple2!=tupleU){
                                                const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                if(itr!=tupleToVar.end()){
                                                    reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                }
                                            }
                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                            reasonMapping.addSharedVarToLit(it->second*sign,X);
                                        }
                                    }
                                }
                            }else{
                                bool propagated=false;
                                if(undefPlusTrue == M){
                                    if(tupleU == NULL){
                                        std::vector<int>sharedVars({X,X});
                                        DynamicCompilationVector* vIndex = sharedVariable[0].addElements(sharedVars);
                                        for(auto undefKeyIt = undefAggrVars[0][vIndex].begin();undefKeyIt!=undefAggrVars[0][vIndex].end();undefKeyIt++){
                                            const std::vector<const Tuple*>* undefinedTuples = &u_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                            if(undefinedTuples->size()==1){

                                                const Tuple* aggrTuple0 = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
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
                                                            if(tuple2!=tupleU){
                                                                const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it0->second*sign,itr->second);
                                                                }
                                                            }
                                                            reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it0->second*sign,X);
                                                        }
                                                    }
                                                }
                                                const Tuple* aggrTuple1 = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                                if(aggrTuple1!=NULL){
                                                    const auto & it1 = tupleToVar.find(*aggrTuple1);
                                                    if(it1 != tupleToVar.end()) {
                                                        propagated=true;
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
                                                            if(tuple1!=tupleU){
                                                                const auto & itr = tupleToVar.find(Tuple(*tuple1));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                                }
                                                            }
                                                            if(tuple2!=tupleU){
                                                                const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                if(itr!=tupleToVar.end()){
                                                                    reasonMapping.addBodyLitToLit(it1->second*sign,itr->second);
                                                                }
                                                            }
                                                            reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                            reasonMapping.addSharedVarToLit(it1->second*sign,X);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        for(auto undefKeyIt = undefNegativeAggrVars[0][vIndex].begin();undefKeyIt!=undefNegativeAggrVars[0][vIndex].end();undefKeyIt++){
                                            const std::vector<const Tuple*>* undefinedTuples = &nu_arc_Y_X_not_removed_Y_X_1_3_0_.getValues({X,X,(*undefKeyIt->getIndex())[0]});
                                            if(undefinedTuples->size()==1){

                                                {
                                                    const Tuple* aggrTupleU = uarc.find(Tuple({undefinedTuples->at(0)->at(0),undefinedTuples->at(0)->at(1)},&_arc));
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
                                                                if(tuple2!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                    }
                                                                }
                                                                reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                                reasonMapping.addSharedVarToLit(it->second*sign,X);
                                                            }
                                                        }
                                                    }
                                                }
                                                {
                                                    const Tuple* aggrTupleU = uremoved.find(Tuple({undefinedTuples->at(0)->at(2),undefinedTuples->at(0)->at(3)},&_removed));
                                                    if(aggrTupleU!=NULL){
                                                        const auto & it = tupleToVar.find(*aggrTupleU);
                                                        if(it != tupleToVar.end()) {
                                                            int sign = 1;
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
                                                                if(tuple2!=tupleU){
                                                                    const auto & itr = tupleToVar.find(Tuple(*tuple2));
                                                                    if(itr!=tupleToVar.end()){
                                                                        reasonMapping.addBodyLitToLit(it->second*sign,itr->second);
                                                                    }
                                                                }
                                                                reasonMapping.addSharedVarToLit(it->second*sign,X);
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
                    }
                    //nested join closed
                }
            }
        }//local scope
    }
}
}
