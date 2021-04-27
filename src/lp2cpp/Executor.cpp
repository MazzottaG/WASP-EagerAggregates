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
std::unordered_map<const std::string*, DynamicTrie*> sharedVariables;
std::unordered_map<const std::string*, std::unordered_map<DynamicCompilationVector*,DynamicTrie>*> sharedVarWAggr;
std::unordered_map<const std::string*, std::unordered_map<DynamicCompilationVector*,DynamicTrie>*> sharedVarUAggr;
std::unordered_map<const std::string*, std::unordered_map<DynamicCompilationVector*,DynamicTrie>*> sharedVarFAggr;
const std::string _a = "a";
PredicateWSet wa(2);
PredicateWSet ua(2);
PredicateWSet fa(2);
const std::string _aggr_id0_0 = "aggr_id0_0";
PredicateWSet waggr_id0_0(0);
PredicateWSet uaggr_id0_0(0);
PredicateWSet faggr_id0_0(0);
const std::string _aggr_id0_0_2 = "aggr_id0_0_2";
PredicateWSet waggr_id0_0_2(0);
PredicateWSet uaggr_id0_0_2(0);
PredicateWSet faggr_id0_0_2(0);
const std::string _aggr_set0_0 = "aggr_set0_0";
PredicateWSet waggr_set0_0(1);
PredicateWSet uaggr_set0_0(1);
PredicateWSet faggr_set0_0(1);
const std::string _aux0 = "aux0";
PredicateWSet waux0(1);
PredicateWSet uaux0(1);
PredicateWSet faux0(1);
const std::string _aux3 = "aux3";
PredicateWSet waux3(2);
PredicateWSet uaux3(2);
PredicateWSet faux3(2);
const std::string _b = "b";
PredicateWSet wb(1);
PredicateWSet ub(1);
PredicateWSet fb(1);
const std::string _body0 = "body0";
PredicateWSet wbody0(0);
PredicateWSet ubody0(0);
PredicateWSet fbody0(0);
std::map<int,int> externalLiteralsLevel;
std::map<int,std::vector<int>> levelToIntLiterals;
std::map<int,UnorderedSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
bool unRoll=false;
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
AuxMap pb_({});
AuxMap ub_({});
AuxMap fb_({});
AuxMap pa_({});
AuxMap ua_({});
AuxMap fa_({});
AuxMap paux0_({});
AuxMap uaux0_({});
AuxMap faux0_({});
AuxMap paux3_0_({0});
AuxMap uaux3_0_({0});
AuxMap faux3_0_({0});
AuxMap paggr_set0_0_({});
AuxMap uaggr_set0_0_({});
AuxMap faggr_set0_0_({});
AuxMap paux3_({});
AuxMap uaux3_({});
AuxMap faux3_({});
AuxMap paux3_1_({1});
AuxMap uaux3_1_({1});
AuxMap faux3_1_({1});
AuxMap paggr_id0_0_({});
AuxMap uaggr_id0_0_({});
AuxMap faggr_id0_0_({});
AuxMap pbody0_({});
AuxMap ubody0_({});
AuxMap fbody0_({});
AuxMap paggr_id0_0_2_({});
AuxMap uaggr_id0_0_2_({});
AuxMap faggr_id0_0_2_({});
void Executor::handleConflict(int literal){
    if(currentDecisionLevel == -1){
        propagatedLiterals.insert(-1);
        return;
    }

    explainExternalLiteral(literal,conflictReason);
    explainExternalLiteral(-literal,conflictReason);
    propagatedLiterals.insert(-1);
    reasonForLiteral.erase(literal);
    for(unsigned i =0; i<conflictReason.size();i++){
        Tuple var = conflictReason[i] > 0 ?atomsTable[conflictReason[i]] : atomsTable[-conflictReason[i]];
        if(conflictReason[i]<0)
            std::cout<<"~";
        var.print();
        std::cout<<std::endl;
    }
}
int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,bool getExternalLit){
    std::unordered_set<int> visitedLiteral;
    std::vector<int> stack;
    stack.push_back(var);
    while(!stack.empty()){
        int lit = stack.back();
        stack.pop_back();
        for(unsigned i = 0; i<reasonForLiteral[lit].size(); i++){
            int reasonLiteral=reasonForLiteral[lit][i];
            Tuple literal = reasonLiteral>0 ? atomsTable[reasonLiteral]:atomsTable[-reasonLiteral];
            if(visitedLiteral.count(reasonLiteral) == 0){
                visitedLiteral.insert(reasonLiteral);
                if(externalLiteralsLevel.count(reasonLiteral)==0){
                    stack.push_back(reasonLiteral);
                }else{
                    reas.insert(reasonLiteral);
                }
            }
        }
    }
    return 0;
}
void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){
    return;
}
void explainPositiveLiteral(const Tuple * tuple, std::unordered_set<std::string> & open_set, std::vector<const Tuple*> & outputReasons) {
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

inline void Executor::onLiteralTrue(const aspc::Literal* l) {
}
inline void Executor::onLiteralUndef(const aspc::Literal* l) {
}
inline void Executor::onLiteralTrue(int var) {
    unsigned uVar = var > 0 ? var : -var;
    const Tuple & tuple = atomsTable[uVar];
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    unRoll=false;
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
    std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple.getPredicateName());
    if (fSetIt == predicateFSetMap.end()) {
        } else {
        if (var < 0) {
            const auto& insertResult = fSetIt->second->insert(Tuple(tuple));
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[fSetIt->first]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
}
inline void Executor::onLiteralUndef(int var) {
    reasonForLiteral.erase(var);
    externalLiteralsLevel.erase(var);
    
//Only for debug
    reasonForLiteral.erase(-var);

    unRoll=true;
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
}
void Executor::undefLiteralsReceived()const{
    std::cout<<"Undef received"<<std::endl;
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    std::cout<<"Undef generation"<<std::endl;
    {//Generating aux3
        const std::vector<const Tuple*>* tuples = &pb_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ub_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int V = tuple0->at(0);
            int X = X = V;
            bool undef1=false;
            const Tuple* tuple1=wa.find(Tuple({X,X},&_a));
            if(tuple1 == NULL){
                tuple1=ua.find(Tuple({X,X},&_a));
                if(tuple1 != NULL){
                    undef1=true;
                }
            }
            if(tuple1 != NULL){
                Tuple aux({X,V}, &_aux3);
                if(uaux3.find(aux) == NULL){
                    const auto& insertResult = uaux3.insert(Tuple({X,V},&_aux3));
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux3]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                        atomsTable.push_back(aux);
                        tupleToVar[aux]=atomsTable.size()-1;
                        Tuple head({X},&_aggr_set0_0);
                        if(uaggr_set0_0.find(head)==NULL){
                            const auto& headInsertResult = uaggr_set0_0.insert(Tuple({X},&_aggr_set0_0));
                            if (headInsertResult.second) {
                                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set0_0]) {
                                    auxMap -> insert2(*headInsertResult.first);
                                }
                                atomsTable.push_back(head);
                                tupleToVar[head]=atomsTable.size()-1;
                            }
                        }
                    }
                }
            }
        }
    }//closing aux generation
    {//Generating aux0
        const std::vector<const Tuple*>* tuples = &pa_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ua_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int W = tuple0->at(0);
            if(tuple0->at(0)==tuple0->at(1)){
                Tuple aux({W}, &_aux0);
                if(uaux0.find(aux) == NULL){
                    const auto& insertResult = uaux0.insert(Tuple({W},&_aux0));
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux0]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                        atomsTable.push_back(aux);
                        tupleToVar[aux]=atomsTable.size()-1;
                        Tuple head({},&_body0);
                        if(ubody0.find(head)==NULL){
                            const auto& headInsertResult = ubody0.insert(Tuple({},&_body0));
                            if (headInsertResult.second) {
                                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_body0]) {
                                    auxMap -> insert2(*headInsertResult.first);
                                }
                                atomsTable.push_back(head);
                                tupleToVar[head]=atomsTable.size()-1;
                            }
                        }
                        Tuple aggr_id7({},&_aggr_id0_0);
                        if(uaggr_id0_0.find(aggr_id7)==NULL){
                            const auto& aggrIdInsertResult = uaggr_id0_0.insert(Tuple({},&_aggr_id0_0));
                            if (aggrIdInsertResult.second) {
                                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id0_0]) {
                                    auxMap -> insert2(*aggrIdInsertResult.first);
                                }
                                atomsTable.push_back(aggr_id7);
                                tupleToVar[aggr_id7]=atomsTable.size()-1;
                            }
                        }
                        Tuple aggr_id8({},&_aggr_id0_0_2);
                        if(uaggr_id0_0_2.find(aggr_id8)==NULL){
                            const auto& aggrIdInsertResult = uaggr_id0_0_2.insert(Tuple({},&_aggr_id0_0_2));
                            if (aggrIdInsertResult.second) {
                                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id0_0_2]) {
                                    auxMap -> insert2(*aggrIdInsertResult.first);
                                }
                                atomsTable.push_back(aggr_id8);
                                tupleToVar[aggr_id8]=atomsTable.size()-1;
                            }
                        }
                    }
                }
            }
        }
    }//closing aux generation
    for(auto atom : tupleToVar){
        atom.first.print();std::cout<<" "<<atom.second<<std::endl;
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
    waggr_id0_0.clear();
    waggr_id0_0_2.clear();
    waggr_set0_0.clear();
    wbody0.clear();
    paggr_id0_0_2_.clear();
    pbody0_.clear();
    paggr_id0_0_.clear();
    paggr_set0_0_.clear();
    faggr_id0_0_2_.clear();
    fbody0_.clear();
    faggr_id0_0_.clear();
    faggr_set0_0_.clear();
}
void Executor::init() {
    std::cout<<"Init"<<std::endl;
    predicateWSetMap[&_a]=&wa;
    predicateUSetMap[&_a]=&ua;
    predicateFSetMap[&_a]=&fa;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_aggr_id0_0]=&waggr_id0_0;
    predicateUSetMap[&_aggr_id0_0]=&uaggr_id0_0;
    predicateFSetMap[&_aggr_id0_0]=&faggr_id0_0;
    stringToUniqueStringPointer["aggr_id0_0"] = &_aggr_id0_0;
    predicateWSetMap[&_aggr_id0_0_2]=&waggr_id0_0_2;
    predicateUSetMap[&_aggr_id0_0_2]=&uaggr_id0_0_2;
    predicateFSetMap[&_aggr_id0_0_2]=&faggr_id0_0_2;
    stringToUniqueStringPointer["aggr_id0_0_2"] = &_aggr_id0_0_2;
    predicateWSetMap[&_aggr_set0_0]=&waggr_set0_0;
    predicateUSetMap[&_aggr_set0_0]=&uaggr_set0_0;
    predicateFSetMap[&_aggr_set0_0]=&faggr_set0_0;
    stringToUniqueStringPointer["aggr_set0_0"] = &_aggr_set0_0;
    predicateWSetMap[&_aux0]=&waux0;
    predicateUSetMap[&_aux0]=&uaux0;
    predicateFSetMap[&_aux0]=&faux0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    predicateWSetMap[&_aux3]=&waux3;
    predicateUSetMap[&_aux3]=&uaux3;
    predicateFSetMap[&_aux3]=&faux3;
    stringToUniqueStringPointer["aux3"] = &_aux3;
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    predicateFSetMap[&_b]=&fb;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_body0]=&wbody0;
    predicateUSetMap[&_body0]=&ubody0;
    predicateFSetMap[&_body0]=&fbody0;
    stringToUniqueStringPointer["body0"] = &_body0;
    predicateToAuxiliaryMaps[&_aggr_id0_0_2].push_back(&paggr_id0_0_2_);
    predicateToAuxiliaryMaps[&_body0].push_back(&pbody0_);
    predicateToAuxiliaryMaps[&_aggr_id0_0].push_back(&paggr_id0_0_);
    predicateToAuxiliaryMaps[&_aggr_set0_0].push_back(&paggr_set0_0_);
    predicateToAuxiliaryMaps[&_aux3].push_back(&paux3_);
    predicateToAuxiliaryMaps[&_aux3].push_back(&paux3_0_);
    predicateToAuxiliaryMaps[&_aux3].push_back(&paux3_1_);
    predicateToAuxiliaryMaps[&_aux0].push_back(&paux0_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0_0_2].push_back(&uaggr_id0_0_2_);
    predicateToUndefAuxiliaryMaps[&_body0].push_back(&ubody0_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0_0].push_back(&uaggr_id0_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0_0].push_back(&uaggr_set0_0_);
    predicateToUndefAuxiliaryMaps[&_aux3].push_back(&uaux3_);
    predicateToUndefAuxiliaryMaps[&_aux3].push_back(&uaux3_0_);
    predicateToUndefAuxiliaryMaps[&_aux3].push_back(&uaux3_1_);
    predicateToUndefAuxiliaryMaps[&_aux0].push_back(&uaux0_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0_0_2].push_back(&faggr_id0_0_2_);
    predicateToFalseAuxiliaryMaps[&_body0].push_back(&fbody0_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0_0].push_back(&faggr_id0_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0_0].push_back(&faggr_set0_0_);
    predicateToFalseAuxiliaryMaps[&_aux3].push_back(&faux3_);
    predicateToFalseAuxiliaryMaps[&_aux3].push_back(&faux3_0_);
    predicateToFalseAuxiliaryMaps[&_aux3].push_back(&faux3_1_);
    predicateToFalseAuxiliaryMaps[&_aux0].push_back(&faux0_);
    predicateToFalseAuxiliaryMaps[&_a].push_back(&fa_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){
    if(tupleU->getPredicateName() == &_aggr_id0_0_2 || tupleU->getPredicateName() == &_aux3 || tupleU->getPredicateName() == &_aggr_id0_0 || tupleU->getPredicateName() == &_aggr_set0_0 || tupleU->getPredicateName() == &_aux0 || tupleU->getPredicateName() == &_body0){
        bool propagated=false;
        std::unordered_map<const std::string*,PredicateWSet*>::iterator falseSet = predicateFSetMap.find(tupleU->getPredicateName());
        std::unordered_map<const std::string*,PredicateWSet*>::iterator undefSet = predicateUSetMap.find(tupleU->getPredicateName());
        std::unordered_map<const std::string*,PredicateWSet*>::iterator trueSet = predicateWSetMap.find(tupleU->getPredicateName());
        if(falseSet==predicateFSetMap.end()){
            std::cout<<"Unable to find false set for: "<<tupleU->getPredicateName()<<std::endl;
            exit(180);
        }
        if(undefSet==predicateUSetMap.end()){
            std::cout<<"Unable to find undef set for: "<<tupleU->getPredicateName()<<std::endl;
            exit(180);
        }
        if(trueSet==predicateWSetMap.end()){
            std::cout<<"Unable to find true set for: "<<tupleU->getPredicateName()<<std::endl;
            exit(180);
        }
        if(isNegated == asNegative){
            if(falseSet->second->find(*tupleU)!=NULL){
                std::cout<<"Conflict: Literal is already false"<<std::endl;
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                const auto& insertResult = trueSet->second->insert(Tuple(*tupleU));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToAuxiliaryMaps[trueSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    propagated = true;
                }
            }
        }else{
            if(trueSet->second->find(*tupleU)!=NULL){
                std::cout<<"Conflict: Literal is already true ";tupleU->print();std::cout<<std::endl;
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                const auto& insertResult = falseSet->second->insert(Tuple(*tupleU));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[falseSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    propagated = true;
                }
            }
        }
        if(propagated){
            auto it = tupleToVar.find(*tupleU);
            int sign = isNegated != asNegative ? -1 : 1;
            if(it!=tupleToVar.end()){
                stack.push_back(sign*it->second);
                levelToIntLiterals[currentDecisionLevel].push_back(sign*it->second);
            }
            undefSet->second->erase(*tupleU);
        }
    }else{
        auto it = tupleToVar.find(*tupleU);
        int sign = isNegated == asNegative ? -1 : 1;
        if(it!=tupleToVar.end()){
            propagatedLiterals.insert(it->second*sign);
        }
    }
    return false;
}
void Executor::unRollToLevel(int decisionLevel){
    std::cout<<"Unrolling to level: "<<decisionLevel << " " <<currentDecisionLevel<<std::endl;
    for(unsigned i = 0; i<propagatedLiterals.size(); i++)
        reasonForLiteral.erase(-propagatedLiterals[i]);
    propagatedLiterals.clear();
    while(currentDecisionLevel > decisionLevel){
        while(!levelToIntLiterals[currentDecisionLevel].empty()){
            int var = levelToIntLiterals[currentDecisionLevel].back();
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral.erase(var);
            int uVar = var>0 ? var : -var;
            Tuple tuple = atomsTable[uVar];
            if (var > 0) {
                std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple.getPredicateName());
                if (wSetIt != predicateWSetMap.end()) {
                    wSetIt->second->erase(tuple);
                }
            } //true removing
            if (var < 0) {
                std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple.getPredicateName());
                if (fSetIt != predicateFSetMap.end()) {
                    fSetIt->second->erase(tuple);
                }
            }//false removing
            std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple.getPredicateName());
            if (it == predicateUSetMap.end()) {
                } else {
                const auto& insertResult = it->second->insert(Tuple(tuple));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[it->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                }
            } // close undef insert 
        }
        levelToIntLiterals.erase(currentDecisionLevel);
        currentDecisionLevel--;
    }
    clearConflictReason();
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts) {
    int decisionLevel = facts[0];
    currentDecisionLevel=decisionLevel;
    clearPropagations();
    std::vector<int> propagationStack;
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
        propagationStack.push_back(facts[i]);
        externalLiteralsLevel[facts[i]]=currentDecisionLevel;
        if(propagatedLiterals.contains(-facts[i])) propagatedLiterals.erase(-facts[i]);
        }
        if(decisionLevel==-1) {
            if(!undefinedLoaded)
                undefLiteralsReceived();
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple positiveTuple({},&_aggr_id0_0);
                    const Tuple* tuple0 = waggr_id0_0.find(positiveTuple);
                    if(tuple0 == tupleU && tupleU == NULL){
                        tuple0 = tupleU = uaggr_id0_0.find(positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple0==NULL && tupleU->getPredicateName() == &_aggr_id0_0 && ! tupleUNegated){
                        if(tupleU == uaggr_id0_0.find(positiveTuple)){
                            tuple0=tupleU;
                        }
                    }
                    if(tuple0!=NULL){
                        Tuple negativeTuple({},&_aggr_id0_0_2);
                        const Tuple* tuple1 = waggr_id0_0_2.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaggr_id0_0_2.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id0_0_2 && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            Tuple positiveTuple({},&_body0);
                            const Tuple* tuple2 = wbody0.find(positiveTuple);
                            if(tuple2 == tupleU && tupleU == NULL){
                                tuple2 = tupleU = ubody0.find(positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                                if(tupleU == ubody0.find(positiveTuple)){
                                    tuple2=tupleU;
                                }
                            }
                            if(tuple2!=NULL){
                                if(tupleU != NULL){
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    propagatedLiterals.insert(-1);
                                }
                            }
                        }
                    }
                }
            }
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &pb_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ub_.getValues({});
                    else if(tupleU->getPredicateName() == &_b && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                    for(unsigned i = 0; i<totalSize; i++){
                        unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                        if(totalSize>currentSize){
                            i-=totalSize-currentSize;
                            totalSize=currentSize;
                        }
                        if(tuplesU!=&EMPTY_TUPLES)
                            tupleU = NULL;
                        const Tuple* tuple0 = NULL;
                        if(i<tuples->size())
                            tuple0 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple0 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            tuple0 = tupleU;
                        }
                        if(tuple0!=NULL){
                            int V = tuple0->at(0);
                            int X = V;
                            Tuple positiveTuple({X,X},&_a);
                            const Tuple* tuple2 = wa.find(positiveTuple);
                            if(tuple2 == tupleU && tupleU == NULL){
                                tuple2 = tupleU = ua.find(positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                                if(tupleU == ua.find(positiveTuple)){
                                    tuple2=tupleU;
                                }
                            }
                            if(tuple2!=NULL){
                                Tuple negativeTuple({X,V},&_aux3);
                                const Tuple* tuple3 = waux3.find(negativeTuple);
                                const Tuple* tupleUndef3 = uaux3.find(negativeTuple);
                                if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                    tuple3 = &negativeTuple;
                                else if(tupleU == NULL & tupleUndef3 != NULL){
                                    tupleU = tuple3 = tupleUndef3;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux3 && tupleUNegated && tupleU==tupleUndef3){
                                    tuple3=tupleU;
                                }else if(tuple3!=NULL){
                                    tuple3=NULL;
                                }
                                if(tuple3!=NULL){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                    }else{
                                        propagatedLiterals.insert(-1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &paux3_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux3_.getValues({});
                    else if(tupleU->getPredicateName() == &_aux3 && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                    for(unsigned i = 0; i<totalSize; i++){
                        unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                        if(totalSize>currentSize){
                            i-=totalSize-currentSize;
                            totalSize=currentSize;
                        }
                        if(tuplesU!=&EMPTY_TUPLES)
                            tupleU = NULL;
                        const Tuple* tuple0 = NULL;
                        if(i<tuples->size())
                            tuple0 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple0 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            tuple0 = tupleU;
                        }
                        if(tuple0!=NULL){
                            int X = tuple0->at(0);
                            int V = tuple0->at(1);
                            Tuple negativeTuple({X,X},&_a);
                            const Tuple* tuple1 = wa.find(negativeTuple);
                            const Tuple* tupleUndef1 = ua.find(negativeTuple);
                            if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                                tuple1 = &negativeTuple;
                            else if(tupleU == NULL & tupleUndef1 != NULL){
                                tupleU = tuple1 = tupleUndef1;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef1){
                                tuple1=tupleU;
                            }else if(tuple1!=NULL){
                                tuple1=NULL;
                            }
                            if(tuple1!=NULL){
                                if(tupleU != NULL){
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    propagatedLiterals.insert(-1);
                                }
                            }
                        }
                    }
                }
            }
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &paux3_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux3_.getValues({});
                    else if(tupleU->getPredicateName() == &_aux3 && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                    for(unsigned i = 0; i<totalSize; i++){
                        unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                        if(totalSize>currentSize){
                            i-=totalSize-currentSize;
                            totalSize=currentSize;
                        }
                        if(tuplesU!=&EMPTY_TUPLES)
                            tupleU = NULL;
                        const Tuple* tuple0 = NULL;
                        if(i<tuples->size())
                            tuple0 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple0 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            tuple0 = tupleU;
                        }
                        if(tuple0!=NULL){
                            int X = tuple0->at(0);
                            int V = tuple0->at(1);
                            Tuple negativeTuple({V},&_b);
                            const Tuple* tuple1 = wb.find(negativeTuple);
                            const Tuple* tupleUndef1 = ub.find(negativeTuple);
                            if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                                tuple1 = &negativeTuple;
                            else if(tupleU == NULL & tupleUndef1 != NULL){
                                tupleU = tuple1 = tupleUndef1;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_b && tupleUNegated && tupleU==tupleUndef1){
                                tuple1=tupleU;
                            }else if(tuple1!=NULL){
                                tuple1=NULL;
                            }
                            if(tuple1!=NULL){
                                if(tupleU != NULL){
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    propagatedLiterals.insert(-1);
                                }
                            }
                        }
                    }
                }
            }
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &pa_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ua_.getValues({});
                    else if(tupleU->getPredicateName() == &_a && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                    for(unsigned i = 0; i<totalSize; i++){
                        unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                        if(totalSize>currentSize){
                            i-=totalSize-currentSize;
                            totalSize=currentSize;
                        }
                        if(tuplesU!=&EMPTY_TUPLES)
                            tupleU = NULL;
                        const Tuple* tuple0 = NULL;
                        if(i<tuples->size())
                            tuple0 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple0 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            tuple0 = tupleU;
                        }
                        if(tuple0!=NULL){
                            if(tuple0->at(0)==tuple0->at(1)){
                                int W = tuple0->at(0);
                                Tuple negativeTuple({W},&_aux0);
                                const Tuple* tuple1 = waux0.find(negativeTuple);
                                const Tuple* tupleUndef1 = uaux0.find(negativeTuple);
                                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                                    tuple1 = &negativeTuple;
                                else if(tupleU == NULL & tupleUndef1 != NULL){
                                    tupleU = tuple1 = tupleUndef1;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef1){
                                    tuple1=tupleU;
                                }else if(tuple1!=NULL){
                                    tuple1=NULL;
                                }
                                if(tuple1!=NULL){
                                    if(tupleU != NULL){
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                    }else{
                                        propagatedLiterals.insert(-1);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            {
                {
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux0_.getValues({});
                    else if(tupleU->getPredicateName() == &_aux0 && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                    for(unsigned i = 0; i<totalSize; i++){
                        unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                        if(totalSize>currentSize){
                            i-=totalSize-currentSize;
                            totalSize=currentSize;
                        }
                        if(tuplesU!=&EMPTY_TUPLES)
                            tupleU = NULL;
                        const Tuple* tuple0 = NULL;
                        if(i<tuples->size())
                            tuple0 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple0 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            tuple0 = tupleU;
                        }
                        if(tuple0!=NULL){
                            int W = tuple0->at(0);
                            Tuple negativeTuple({W,W},&_a);
                            const Tuple* tuple1 = wa.find(negativeTuple);
                            const Tuple* tupleUndef1 = ua.find(negativeTuple);
                            if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                                tuple1 = &negativeTuple;
                            else if(tupleU == NULL & tupleUndef1 != NULL){
                                tupleU = tuple1 = tupleUndef1;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef1){
                                tuple1=tupleU;
                            }else if(tuple1!=NULL){
                                tuple1=NULL;
                            }
                            if(tuple1!=NULL){
                                if(tupleU != NULL){
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    propagatedLiterals.insert(-1);
                                }
                            }
                        }
                    }
                }
            }
            {
                const std::vector<const Tuple*>* trueHeads = &pbody0_.getValues({});
                for(unsigned i = 0; i < trueHeads->size(); i++){
                    const Tuple* head = trueHeads->at(i);
                    const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
                    if(tuples->size() == 0){
                        if(tuplesU->size() == 0){
                            propagatedLiterals.insert(-1);
                        }else if(tuplesU->size() == 1){
                            propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            const auto & it = tupleToVar.find(*head);
                            if(it != tupleToVar.end()){
                            }
                        }
                    }else{
                        const auto & it = tupleToVar.find(*head);
                        if(it != tupleToVar.end()){
                        }
                    }
                }
                const std::vector<const Tuple*>* undefHeads = &ubody0_.getValues({});
                for(unsigned i = 0; i < undefHeads->size(); i++){
                    const Tuple* head = undefHeads->at(i);
                    const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                    if(tuples->size() == 0){
                        const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
                        if(tuplesU->size() == 0){
                            propUndefined(head,false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        propUndefined(head,false,propagationStack,false,propagatedLiterals);
                        const auto& it = tupleToVar.find(*head);
                        if(it!=tupleToVar.end()){
                        }
                    }
                }
                const std::vector<const Tuple*>* falseHeads = &fbody0_.getValues({});
                for(unsigned i = 0; i < falseHeads->size(); i++){
                    const Tuple* head = falseHeads->at(i);
                    const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                    if(tuples->size() == 0){
                        const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
                        for(unsigned j = 0; j < tuplesU->size();){
                            propUndefined(tuplesU->at(j),false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        propagatedLiterals.insert(-1);
                    }
                }
            }
            {
                const std::vector<const Tuple*>* trueHeads = &paggr_set0_0_.getValues({});
                for(unsigned i = 0; i < trueHeads->size(); i++){
                    const Tuple* head = trueHeads->at(i);
                    int X = head->at(0);
                    const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                    const std::vector<const Tuple*>* tuplesU = &uaux3_0_.getValues({X});
                    if(tuples->size() == 0){
                        if(tuplesU->size() == 0){
                            propagatedLiterals.insert(-1);
                        }else if(tuplesU->size() == 1){
                            propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            const auto & it = tupleToVar.find(*head);
                            if(it != tupleToVar.end()){
                            }
                        }
                    }else{
                        const auto & it = tupleToVar.find(*head);
                        if(it != tupleToVar.end()){
                        }
                    }
                }
                const std::vector<const Tuple*>* undefHeads = &uaggr_set0_0_.getValues({});
                for(unsigned i = 0; i < undefHeads->size(); i++){
                    const Tuple* head = undefHeads->at(i);
                    int X = head->at(0);
                    const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                    if(tuples->size() == 0){
                        const std::vector<const Tuple*>* tuplesU = &uaux3_0_.getValues({X});
                        if(tuplesU->size() == 0){
                            propUndefined(head,false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        propUndefined(head,false,propagationStack,false,propagatedLiterals);
                        const auto& it = tupleToVar.find(*head);
                        if(it!=tupleToVar.end()){
                        }
                    }
                }
                const std::vector<const Tuple*>* falseHeads = &faggr_set0_0_.getValues({});
                for(unsigned i = 0; i < falseHeads->size(); i++){
                    const Tuple* head = falseHeads->at(i);
                    int X = head->at(0);
                    const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                    if(tuples->size() == 0){
                        const std::vector<const Tuple*>* tuplesU = &uaux3_0_.getValues({X});
                        for(unsigned j = 0; j < tuplesU->size();){
                            propUndefined(tuplesU->at(j),false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        propagatedLiterals.insert(-1);
                    }
                }
            }
            {
                const std::vector<const Tuple*>* tuples = &paggr_id0_0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &uaggr_id0_0_.getValues({});
                const std::vector<const Tuple*>* tuplesF = &faggr_id0_0_.getValues({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() + joinTuplesU->size() < 4){
                        propagatedLiterals.insert(-1);
                    }else if(joinTuples->size() + joinTuplesU->size() == 4){
                        while(joinTuplesU->size()>0){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0 ){
                                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                    for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                        auto it = tupleToVar.find(*joinTuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    auto itAggrId = tupleToVar.find(*tuples->at(i));
                                    if(itAggrId!= tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(itAggrId->second);
                                    }
                                }
                                propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size()>=4){
                        propagatedLiterals.insert(-1);
                    }else if(joinTuples->size() == 4 -1){
                        std::vector<int> reason;
                        for(unsigned i =0; i< joinTuples->size(); i++){
                            auto it = tupleToVar.find(*joinTuples->at(i));
                            if(it != tupleToVar.end()){
                                reason.push_back(it->second);
                            }
                        }
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!= tupleToVar.end()){
                            reason.push_back(-it->second);
                        }
                        while(!joinTuplesU->empty()){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second) == 0 ){
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                            propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() >= 4){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                for(unsigned j = 0; j < joinTuples->size(); j++){
                                    auto it = tupleToVar.find(*joinTuples->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                        }
                    }else if(joinTuples->size() + joinTuplesU->size() < 4){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(-itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                    auto it = tupleToVar.find(*joinTuplesF->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-itProp->second].insert(-it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        i++;
                    }
                }//close undef for
            }//close aggr set starter
            {
                const std::vector<const Tuple*>* tuples = &paggr_id0_0_2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &uaggr_id0_0_2_.getValues({});
                const std::vector<const Tuple*>* tuplesF = &faggr_id0_0_2_.getValues({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() + joinTuplesU->size() < 4+1){
                        propagatedLiterals.insert(-1);
                    }else if(joinTuples->size() + joinTuplesU->size() == 4+1){
                        while(joinTuplesU->size()>0){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0 ){
                                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                    for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                        auto it = tupleToVar.find(*joinTuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    auto itAggrId = tupleToVar.find(*tuples->at(i));
                                    if(itAggrId!= tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(itAggrId->second);
                                    }
                                }
                                propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size()>=4+1){
                        propagatedLiterals.insert(-1);
                    }else if(joinTuples->size() == 4+1 -1){
                        std::vector<int> reason;
                        for(unsigned i =0; i< joinTuples->size(); i++){
                            auto it = tupleToVar.find(*joinTuples->at(i));
                            if(it != tupleToVar.end()){
                                reason.push_back(it->second);
                            }
                        }
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!= tupleToVar.end()){
                            reason.push_back(-it->second);
                        }
                        while(!joinTuplesU->empty()){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second) == 0 ){
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                            propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() >= 4+1){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                for(unsigned j = 0; j < joinTuples->size(); j++){
                                    auto it = tupleToVar.find(*joinTuples->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                        }
                    }else if(joinTuples->size() + joinTuplesU->size() < 4+1){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(-itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                    auto it = tupleToVar.find(*joinTuplesF->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-itProp->second].insert(-it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        i++;
                    }
                }//close undef for
            }//close aggr set starter
        }//close decision level == -1
        while(!propagationStack.empty()){
            int startVar = propagationStack.back();
            int uStartVar = startVar<0 ? -startVar : startVar;
            Tuple starter = atomsTable[uStartVar];
            starter.setNegated(startVar<0);
            propagationStack.pop_back();
            if(starter.getPredicateName() == &_body0){
                const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
                if(!starter.isNegated()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            const auto& it = tupleToVar.find(*tuplesF->at(i));
                            if(it!=tupleToVar.end())
                                reasonForLiteral[-startVar].insert(-it->second);
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size()==1){
                        const auto& itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp!=tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                                for(unsigned i=0; i<tuplesF->size(); i++){
                                    const auto& it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end())
                                        reasonForLiteral[itProp->second].insert(-it->second);
                                }
                                reasonForLiteral[itProp->second].insert(startVar);
                            }
                            propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }else{
                    if(tuples->size()>0){
                        const auto& it = tupleToVar.find(*tuples->at(0));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-it->second].insert(startVar);
                            handleConflict(-it->second);
                            return;
                        }
                    }else{
                        while(!tuplesU->empty()){
                            const auto& it = tupleToVar.find(*tuplesU->back());
                            unsigned size = tuplesU->size();
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }//close if starter
            if(starter.getPredicateName() == &_aux0){
                int W = starter[0];
                if(!starter.isNegated()){
                    Tuple head({}, &_body0);
                    const Tuple* tupleU = ubody0.find(head);
                    if(wbody0.find(head) == tupleU && tupleU==NULL){
                        const auto& it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[it->second].insert(startVar);
                            handleConflict(it->second);
                            return;
                        }
                    }else if(tupleU != NULL){
                        const auto& it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }else{
                    Tuple head({}, &_body0);
                    const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                    const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
                    if(wbody0.find(head) != NULL){
                        if(tuples->size()==0 && tuplesU->size()==0){
                            const auto itHead = tupleToVar.find(head);
                            if(itHead!=tupleToVar.end()){
                                const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                                for(unsigned i=0;i<tuplesF->size();i++){
                                    const auto& it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-itHead->second].insert(-it->second);
                                    }
                                }
                                handleConflict(-itHead->second);
                                return;
                            }
                        }else if(tuples->size() == 0 && tuplesU->size() == 1){
                            const auto itProp = tupleToVar.find(*tuplesU->at(0));
                            if(itProp!=tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0 ){
                                    const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                                    for(unsigned i=0;i<tuplesF->size();i++){
                                        const auto& it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    const auto& it = tupleToVar.find(head);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(it->second);
                                    }
                                }
                                propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }else{
                        const Tuple* tupleU = ubody0.find(head);
                        if(tupleU != NULL && tuples->size() == 0 && tuplesU->size() == 0){
                            const auto itHead = tupleToVar.find(head);
                            if(itHead!=tupleToVar.end()){
                                if(reasonForLiteral.count(-itHead->second) == 0 ){
                                    const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                                    for(unsigned i=0;i<tuplesF->size();i++){
                                        const auto& it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-itHead->second].insert(-it->second);
                                        }
                                    }
                                }
                                propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_body0){
                const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
                if(!starter.isNegated()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            const auto& it = tupleToVar.find(*tuplesF->at(i));
                            if(it!=tupleToVar.end())
                                reasonForLiteral[-startVar].insert(-it->second);
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size()==1){
                        const auto& itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp!=tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faux0_.getValues({});
                                for(unsigned i=0; i<tuplesF->size(); i++){
                                    const auto& it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end())
                                        reasonForLiteral[itProp->second].insert(-it->second);
                                }
                                reasonForLiteral[itProp->second].insert(startVar);
                            }
                            propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }else{
                    if(tuples->size()>0){
                        const auto& it = tupleToVar.find(*tuples->at(0));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-it->second].insert(startVar);
                            handleConflict(-it->second);
                            return;
                        }
                    }else{
                        while(!tuplesU->empty()){
                            const auto& it = tupleToVar.find(*tuplesU->back());
                            unsigned size = tuplesU->size();
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }//close if starter
            {
                if(starter.getPredicateName() == &_a && starter.isNegated()){
                    if(starter.at(0)==starter.at(1)){
                        int W = starter[0];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        Tuple positiveTuple({W},&_aux0);
                        const Tuple* tuple1 = waux0.find(positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaux0.find(positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aux0 && ! tupleUNegated){
                            if(tupleU == uaux0.find(positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple1);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    const auto& it = tupleToVar.find(*tuple1);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_aux0 && !starter.isNegated()){
                    int W = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple negativeTuple({W,W},&_a);
                    const Tuple* tuple1 = wa.find(negativeTuple);
                    const Tuple* tupleUndef1 = ua.find(negativeTuple);
                    if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                        tuple1 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef1 != NULL){
                        tupleU = tuple1 = tupleUndef1;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef1){
                        tuple1=tupleU;
                    }else if(tuple1!=NULL){
                        tuple1=NULL;
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            const auto& itUndef = tupleToVar.find(*tupleU);
                            if(itUndef!=tupleToVar.end()){
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef->second;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        const auto& it = tupleToVar.find(starter);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*1);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto& it = tupleToVar.find(*tuple1);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*-1);
                                        }
                                    }
                                }
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                const auto& it = tupleToVar.find(*tuple1);
                                if(it!=tupleToVar.end()){
                                    reasonForLiteral[-startVar].insert(it->second*-1);
                                }
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            {
                if(starter.getPredicateName() == &_aux0 && starter.isNegated()){
                    int W = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple positiveTuple({W,W},&_a);
                    const Tuple* tuple1 = wa.find(positiveTuple);
                    if(tuple1 == tupleU && tupleU == NULL){
                        tuple1 = tupleU = ua.find(positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                        if(tupleU == ua.find(positiveTuple)){
                            tuple1=tupleU;
                        }
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            const auto& itUndef = tupleToVar.find(*tupleU);
                            if(itUndef!=tupleToVar.end()){
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef->second;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        const auto& it = tupleToVar.find(starter);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*-1);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto& it = tupleToVar.find(*tuple1);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*1);
                                        }
                                    }
                                }
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                const auto& it = tupleToVar.find(*tuple1);
                                if(it!=tupleToVar.end()){
                                    reasonForLiteral[-startVar].insert(it->second*1);
                                }
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
                if(starter.getPredicateName() == &_a && !starter.isNegated()){
                    if(starter.at(0)==starter.at(1)){
                        int W = starter[0];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        Tuple negativeTuple({W},&_aux0);
                        const Tuple* tuple1 = waux0.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaux0.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef1){
                            tuple1=tupleU;
                        }else if(tuple1!=NULL){
                            tuple1=NULL;
                        }
                        if(tuple1!=NULL){
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple1);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    const auto& it = tupleToVar.find(*tuple1);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*-1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aggr_set0_0){
                int X = starter[0];
                const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &uaux3_0_.getValues({X});
                if(!starter.isNegated()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            const auto& it = tupleToVar.find(*tuplesF->at(i));
                            if(it!=tupleToVar.end())
                                reasonForLiteral[-startVar].insert(-it->second);
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size()==1){
                        const auto& itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp!=tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                                for(unsigned i=0; i<tuplesF->size(); i++){
                                    const auto& it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end())
                                        reasonForLiteral[itProp->second].insert(-it->second);
                                }
                                reasonForLiteral[itProp->second].insert(startVar);
                            }
                            propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }else{
                    if(tuples->size()>0){
                        const auto& it = tupleToVar.find(*tuples->at(0));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-it->second].insert(startVar);
                            handleConflict(-it->second);
                            return;
                        }
                    }else{
                        while(!tuplesU->empty()){
                            const auto& it = tupleToVar.find(*tuplesU->back());
                            unsigned size = tuplesU->size();
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }//close if starter
            if(starter.getPredicateName() == &_aux3){
                int X = starter[0];
                int V = starter[1];
                if(!starter.isNegated()){
                    Tuple head({X}, &_aggr_set0_0);
                    const Tuple* tupleU = uaggr_set0_0.find(head);
                    if(waggr_set0_0.find(head) == tupleU && tupleU==NULL){
                        const auto& it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[it->second].insert(startVar);
                            handleConflict(it->second);
                            return;
                        }
                    }else if(tupleU != NULL){
                        const auto& it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }else{
                    Tuple head({X}, &_aggr_set0_0);
                    const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                    const std::vector<const Tuple*>* tuplesU = &uaux3_0_.getValues({X});
                    if(waggr_set0_0.find(head) != NULL){
                        if(tuples->size()==0 && tuplesU->size()==0){
                            const auto itHead = tupleToVar.find(head);
                            if(itHead!=tupleToVar.end()){
                                const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                                for(unsigned i=0;i<tuplesF->size();i++){
                                    const auto& it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-itHead->second].insert(-it->second);
                                    }
                                }
                                handleConflict(-itHead->second);
                                return;
                            }
                        }else if(tuples->size() == 0 && tuplesU->size() == 1){
                            const auto itProp = tupleToVar.find(*tuplesU->at(0));
                            if(itProp!=tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0 ){
                                    const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                                    for(unsigned i=0;i<tuplesF->size();i++){
                                        const auto& it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    const auto& it = tupleToVar.find(head);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(it->second);
                                    }
                                }
                                propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }else{
                        const Tuple* tupleU = uaggr_set0_0.find(head);
                        if(tupleU != NULL && tuples->size() == 0 && tuplesU->size() == 0){
                            const auto itHead = tupleToVar.find(head);
                            if(itHead!=tupleToVar.end()){
                                if(reasonForLiteral.count(-itHead->second) == 0 ){
                                    const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                                    for(unsigned i=0;i<tuplesF->size();i++){
                                        const auto& it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-itHead->second].insert(-it->second);
                                        }
                                    }
                                }
                                propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aggr_set0_0){
                int X = starter[0];
                const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                const std::vector<const Tuple*>* tuplesU = &uaux3_0_.getValues({X});
                if(!starter.isNegated()){
                    if(tuples->size() == 0 && tuplesU->size() == 0){
                        const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                        for(unsigned i=0; i<tuplesF->size(); i++){
                            const auto& it = tupleToVar.find(*tuplesF->at(i));
                            if(it!=tupleToVar.end())
                                reasonForLiteral[-startVar].insert(-it->second);
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() == 0 && tuplesU->size()==1){
                        const auto& itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp!=tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faux3_0_.getValues({X});
                                for(unsigned i=0; i<tuplesF->size(); i++){
                                    const auto& it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end())
                                        reasonForLiteral[itProp->second].insert(-it->second);
                                }
                                reasonForLiteral[itProp->second].insert(startVar);
                            }
                            propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }else{
                    if(tuples->size()>0){
                        const auto& it = tupleToVar.find(*tuples->at(0));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-it->second].insert(startVar);
                            handleConflict(-it->second);
                            return;
                        }
                    }else{
                        while(!tuplesU->empty()){
                            const auto& it = tupleToVar.find(*tuplesU->back());
                            unsigned size = tuplesU->size();
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }//close if starter
            {
                if(starter.getPredicateName() == &_b && starter.isNegated()){
                    int V = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    const std::vector<const Tuple*>* tuples = &paux3_1_.getValues({V});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uaux3_1_.getValues({V});
                    else if(tupleU->getPredicateName() == &_aux3 && !tupleUNegated)
                        undeRepeated.push_back(tupleU);
                    unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                    for(unsigned i = 0; i<totalSize; i++){
                        unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                        if(totalSize>currentSize){
                            i-=totalSize-currentSize;
                            totalSize=currentSize;
                        }
                        if(tuplesU!=&EMPTY_TUPLES)
                            tupleU = NULL;
                        const Tuple* tuple1 = NULL;
                        if(i<tuples->size())
                            tuple1 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple1 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            if(tupleU->at(1) == V)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int X = tuple1->at(0);
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple1);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    const auto& it = tupleToVar.find(*tuple1);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_aux3 && !starter.isNegated()){
                    int X = starter[0];
                    int V = starter[1];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple negativeTuple({V},&_b);
                    const Tuple* tuple1 = wb.find(negativeTuple);
                    const Tuple* tupleUndef1 = ub.find(negativeTuple);
                    if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                        tuple1 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef1 != NULL){
                        tupleU = tuple1 = tupleUndef1;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_b && tupleUNegated && tupleU==tupleUndef1){
                        tuple1=tupleU;
                    }else if(tuple1!=NULL){
                        tuple1=NULL;
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            const auto& itUndef = tupleToVar.find(*tupleU);
                            if(itUndef!=tupleToVar.end()){
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef->second;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        const auto& it = tupleToVar.find(starter);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*1);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto& it = tupleToVar.find(*tuple1);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*-1);
                                        }
                                    }
                                }
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                const auto& it = tupleToVar.find(*tuple1);
                                if(it!=tupleToVar.end()){
                                    reasonForLiteral[-startVar].insert(it->second*-1);
                                }
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            {
                if(starter.getPredicateName() == &_a && starter.isNegated()){
                    if(starter.at(0)==starter.at(1)){
                        int X = starter[0];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        const std::vector<const Tuple*>* tuples = &paux3_0_.getValues({X});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &uaux3_0_.getValues({X});
                        else if(tupleU->getPredicateName() == &_aux3 && !tupleUNegated)
                            undeRepeated.push_back(tupleU);
                        unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();
                        for(unsigned i = 0; i<totalSize; i++){
                            unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();
                            if(totalSize>currentSize){
                                i-=totalSize-currentSize;
                                totalSize=currentSize;
                            }
                            if(tuplesU!=&EMPTY_TUPLES)
                                tupleU = NULL;
                            const Tuple* tuple1 = NULL;
                            if(i<tuples->size())
                                tuple1 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple1 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == X)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int V = tuple1->at(1);
                                if(tupleU != NULL){
                                    const auto& itUndef = tupleToVar.find(*tupleU);
                                    if(itUndef!=tupleToVar.end()){
                                        int var = tupleUNegated ? 1 : -1;
                                        var*=itUndef->second;
                                        if(reasonForLiteral.count(var) == 0){
                                            {
                                                const auto& it = tupleToVar.find(starter);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*-1);
                                                }
                                            }
                                            if(tuple1!=tupleU){
                                                const auto& it = tupleToVar.find(*tuple1);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*1);
                                                }
                                            }
                                        }
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        const auto& it = tupleToVar.find(*tuple1);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-startVar].insert(it->second*1);
                                        }
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_aux3 && !starter.isNegated()){
                    int X = starter[0];
                    int V = starter[1];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple negativeTuple({X,X},&_a);
                    const Tuple* tuple1 = wa.find(negativeTuple);
                    const Tuple* tupleUndef1 = ua.find(negativeTuple);
                    if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                        tuple1 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef1 != NULL){
                        tupleU = tuple1 = tupleUndef1;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_a && tupleUNegated && tupleU==tupleUndef1){
                        tuple1=tupleU;
                    }else if(tuple1!=NULL){
                        tuple1=NULL;
                    }
                    if(tuple1!=NULL){
                        if(tupleU != NULL){
                            const auto& itUndef = tupleToVar.find(*tupleU);
                            if(itUndef!=tupleToVar.end()){
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef->second;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        const auto& it = tupleToVar.find(starter);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*1);
                                        }
                                    }
                                    if(tuple1!=tupleU){
                                        const auto& it = tupleToVar.find(*tuple1);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[var].insert(it->second*-1);
                                        }
                                    }
                                }
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                const auto& it = tupleToVar.find(*tuple1);
                                if(it!=tupleToVar.end()){
                                    reasonForLiteral[-startVar].insert(it->second*-1);
                                }
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            {
                if(starter.getPredicateName() == &_aux3 && starter.isNegated()){
                    int X = starter[0];
                    int V = starter[1];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    if(V == X){
                        Tuple positiveTuple({V},&_b);
                        const Tuple* tuple2 = wb.find(positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = ub.find(positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_b && ! tupleUNegated){
                            if(tupleU == ub.find(positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple positiveTuple({X,X},&_a);
                            const Tuple* tuple3 = wa.find(positiveTuple);
                            if(tuple3 == tupleU && tupleU == NULL){
                                tuple3 = tupleU = ua.find(positiveTuple);
                                tupleUNegated=false;
                            }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                                if(tupleU == ua.find(positiveTuple)){
                                    tuple3=tupleU;
                                }
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    const auto& itUndef = tupleToVar.find(*tupleU);
                                    if(itUndef!=tupleToVar.end()){
                                        int var = tupleUNegated ? 1 : -1;
                                        var*=itUndef->second;
                                        if(reasonForLiteral.count(var) == 0){
                                            {
                                                const auto& it = tupleToVar.find(starter);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*-1);
                                                }
                                            }
                                            if(tuple2!=tupleU){
                                                const auto& it = tupleToVar.find(*tuple2);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*1);
                                                }
                                            }
                                            if(tuple3!=tupleU){
                                                const auto& it = tupleToVar.find(*tuple3);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*1);
                                                }
                                            }
                                        }
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple2!=NULL){
                                        const auto& it = tupleToVar.find(*tuple2);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-startVar].insert(it->second*1);
                                        }
                                    }
                                    if(tuple3!=NULL){
                                        const auto& it = tupleToVar.find(*tuple3);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-startVar].insert(it->second*1);
                                        }
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_a && !starter.isNegated()){
                    if(starter.at(0)==starter.at(1)){
                        int X = starter[0];
                        const Tuple* tupleU = NULL;
                        bool tupleUNegated = false;
                        int V = X;
                        Tuple positiveTuple({V},&_b);
                        const Tuple* tuple2 = wb.find(positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = ub.find(positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_b && ! tupleUNegated){
                            if(tupleU == ub.find(positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            Tuple negativeTuple({X,V},&_aux3);
                            const Tuple* tuple3 = waux3.find(negativeTuple);
                            const Tuple* tupleUndef3 = uaux3.find(negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = &negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux3 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
                                if(tupleU != NULL){
                                    const auto& itUndef = tupleToVar.find(*tupleU);
                                    if(itUndef!=tupleToVar.end()){
                                        int var = tupleUNegated ? 1 : -1;
                                        var*=itUndef->second;
                                        if(reasonForLiteral.count(var) == 0){
                                            {
                                                const auto& it = tupleToVar.find(starter);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*1);
                                                }
                                            }
                                            if(tuple2!=tupleU){
                                                const auto& it = tupleToVar.find(*tuple2);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*1);
                                                }
                                            }
                                            if(tuple3!=tupleU){
                                                const auto& it = tupleToVar.find(*tuple3);
                                                if(it!=tupleToVar.end()){
                                                    reasonForLiteral[var].insert(it->second*-1);
                                                }
                                            }
                                        }
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple2!=NULL){
                                        const auto& it = tupleToVar.find(*tuple2);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-startVar].insert(it->second*1);
                                        }
                                    }
                                    if(tuple3!=NULL){
                                        const auto& it = tupleToVar.find(*tuple3);
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[-startVar].insert(it->second*-1);
                                        }
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_b && !starter.isNegated()){
                    int V = starter[0];
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    int X = V;
                    Tuple positiveTuple({X,X},&_a);
                    const Tuple* tuple2 = wa.find(positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = ua.find(positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_a && ! tupleUNegated){
                        if(tupleU == ua.find(positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple negativeTuple({X,V},&_aux3);
                        const Tuple* tuple3 = waux3.find(negativeTuple);
                        const Tuple* tupleUndef3 = uaux3.find(negativeTuple);
                        if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                            tuple3 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef3 != NULL){
                            tupleU = tuple3 = tupleUndef3;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux3 && tupleUNegated && tupleU==tupleUndef3){
                            tuple3=tupleU;
                        }else if(tuple3!=NULL){
                            tuple3=NULL;
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple2!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple2);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple3!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple3);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple2!=NULL){
                                    const auto& it = tupleToVar.find(*tuple2);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                if(tuple3!=NULL){
                                    const auto& it = tupleToVar.find(*tuple3);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*-1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_aggr_id0_0){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* tuples = &paggr_set0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* tuplesU = &uaggr_set0_0_.getValues(sharedVar);
                if(starter.isNegated()){
                    if(tuples->size()>=4){
                        for(unsigned i =0; i< tuples->size(); i++){
                            auto it = tupleToVar.find(*tuples->at(i));
                            if(it != tupleToVar.end()){
                                reasonForLiteral[-startVar].insert(it->second);
                            }
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() == 4 -1){
                        std::vector<int> reason;
                        for(unsigned i =0; i< tuples->size(); i++){
                            auto it = tupleToVar.find(*tuples->at(i));
                            if(it != tupleToVar.end()){
                                reason.push_back(it->second);
                            }
                        }
                        reason.push_back(startVar);
                        while(!tuplesU->empty()){
                            auto itProp = tupleToVar.find(*tuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second)==0){
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                            propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }else{
                    if(tuples->size()+tuplesU->size() < 4){
                        const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_.getValues(sharedVar);
                        for(unsigned i = 0; i < tuplesF->size(); i++){
                            auto it = tupleToVar.find(*tuplesF->at(i));
                            if(it!=tupleToVar.end()){
                                reasonForLiteral[-startVar].insert(-it->second);
                            }
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() + tuplesU->size() == 4){
                        while(tuplesU->size()>0){
                            auto itProp = tupleToVar.find(*tuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0){
                                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_.getValues(sharedVar);
                                    for(unsigned i = 0; i < tuplesF->size(); i++){
                                        auto it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    reasonForLiteral[itProp->second].insert(startVar);
                                }
                                propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }
                }
            }//close aggr id starter
            if(starter.getPredicateName() == &_aggr_set0_0){
                const std::vector<const Tuple*>* tuples = &paggr_id0_0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &uaggr_id0_0_.getValues({});
                const std::vector<const Tuple*>* tuplesF = &faggr_id0_0_.getValues({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() + joinTuplesU->size() < 4){
                        auto itProp = tupleToVar.find(*tuples->at(i));
                        if(itProp!=tupleToVar.end()){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                            for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                auto it = tupleToVar.find(*joinTuplesF->at(j));
                                if(it!=tupleToVar.end()){
                                    reasonForLiteral[-itProp->second].insert(-it->second);
                                }
                            }
                            handleConflict(-itProp->second);
                            return;
                        }
                    }else if(joinTuples->size() + joinTuplesU->size() == 4){
                        while(joinTuplesU->size()>0){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0 ){
                                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                    for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                        auto it = tupleToVar.find(*joinTuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    auto itAggrId = tupleToVar.find(*tuples->at(i));
                                    if(itAggrId!= tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(itAggrId->second);
                                    }
                                }
                                propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size()>=4){
                        auto itProp = tupleToVar.find(*tuplesF->at(i));
                        if(itProp != tupleToVar.end()){
                            for(unsigned j =0; j< joinTuples->size(); j++){
                                auto it = tupleToVar.find(*joinTuples->at(j));
                                if(it != tupleToVar.end()){
                                    reasonForLiteral[itProp->second].insert(it->second);
                                }
                            }
                            handleConflict(itProp->second);
                            return;
                        }
                    }else if(joinTuples->size() == 4 -1){
                        std::vector<int> reason;
                        for(unsigned i =0; i< joinTuples->size(); i++){
                            auto it = tupleToVar.find(*joinTuples->at(i));
                            if(it != tupleToVar.end()){
                                reason.push_back(it->second);
                            }
                        }
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!= tupleToVar.end()){
                            reason.push_back(-it->second);
                        }
                        while(!joinTuplesU->empty()){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second) == 0 ){
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                            propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() >= 4){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                for(unsigned j = 0; j < joinTuples->size(); j++){
                                    auto it = tupleToVar.find(*joinTuples->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                        }
                    }else if(joinTuples->size() + joinTuplesU->size() < 4){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(-itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                    auto it = tupleToVar.find(*joinTuplesF->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-itProp->second].insert(-it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        i++;
                    }
                }//close undef for
            }//close aggr set starter
            if(starter.getPredicateName() == &_aggr_id0_0_2){
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* tuples = &paggr_set0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* tuplesU = &uaggr_set0_0_.getValues(sharedVar);
                if(starter.isNegated()){
                    if(tuples->size()>=4+1){
                        for(unsigned i =0; i< tuples->size(); i++){
                            auto it = tupleToVar.find(*tuples->at(i));
                            if(it != tupleToVar.end()){
                                reasonForLiteral[-startVar].insert(it->second);
                            }
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() == 4+1 -1){
                        std::vector<int> reason;
                        for(unsigned i =0; i< tuples->size(); i++){
                            auto it = tupleToVar.find(*tuples->at(i));
                            if(it != tupleToVar.end()){
                                reason.push_back(it->second);
                            }
                        }
                        reason.push_back(startVar);
                        while(!tuplesU->empty()){
                            auto itProp = tupleToVar.find(*tuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second)==0){
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                            propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }else{
                    if(tuples->size()+tuplesU->size() < 4+1){
                        const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_.getValues(sharedVar);
                        for(unsigned i = 0; i < tuplesF->size(); i++){
                            auto it = tupleToVar.find(*tuplesF->at(i));
                            if(it!=tupleToVar.end()){
                                reasonForLiteral[-startVar].insert(-it->second);
                            }
                        }
                        handleConflict(-startVar);
                        return;
                    }else if(tuples->size() + tuplesU->size() == 4+1){
                        while(tuplesU->size()>0){
                            auto itProp = tupleToVar.find(*tuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0){
                                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_.getValues(sharedVar);
                                    for(unsigned i = 0; i < tuplesF->size(); i++){
                                        auto it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    reasonForLiteral[itProp->second].insert(startVar);
                                }
                                propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }
                }
            }//close aggr id starter
            if(starter.getPredicateName() == &_aggr_set0_0){
                const std::vector<const Tuple*>* tuples = &paggr_id0_0_2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &uaggr_id0_0_2_.getValues({});
                const std::vector<const Tuple*>* tuplesF = &faggr_id0_0_2_.getValues({});
                for(unsigned i = 0; i<tuples->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() + joinTuplesU->size() < 4+1){
                        auto itProp = tupleToVar.find(*tuples->at(i));
                        if(itProp!=tupleToVar.end()){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                            for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                auto it = tupleToVar.find(*joinTuplesF->at(j));
                                if(it!=tupleToVar.end()){
                                    reasonForLiteral[-itProp->second].insert(-it->second);
                                }
                            }
                            handleConflict(-itProp->second);
                            return;
                        }
                    }else if(joinTuples->size() + joinTuplesU->size() == 4+1){
                        while(joinTuplesU->size()>0){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(itProp->second) == 0 ){
                                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                    for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                        auto it = tupleToVar.find(*joinTuplesF->at(i));
                                        if(it!=tupleToVar.end()){
                                            reasonForLiteral[itProp->second].insert(-it->second);
                                        }
                                    }
                                    auto itAggrId = tupleToVar.find(*tuples->at(i));
                                    if(itAggrId!= tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(itAggrId->second);
                                    }
                                }
                                propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                            }
                        }
                    }
                }//close true for
                for(unsigned i = 0; i<tuplesF->size(); i++){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size()>=4+1){
                        auto itProp = tupleToVar.find(*tuplesF->at(i));
                        if(itProp != tupleToVar.end()){
                            for(unsigned j =0; j< joinTuples->size(); j++){
                                auto it = tupleToVar.find(*joinTuples->at(j));
                                if(it != tupleToVar.end()){
                                    reasonForLiteral[itProp->second].insert(it->second);
                                }
                            }
                            handleConflict(itProp->second);
                            return;
                        }
                    }else if(joinTuples->size() == 4+1 -1){
                        std::vector<int> reason;
                        for(unsigned i =0; i< joinTuples->size(); i++){
                            auto it = tupleToVar.find(*joinTuples->at(i));
                            if(it != tupleToVar.end()){
                                reason.push_back(it->second);
                            }
                        }
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!= tupleToVar.end()){
                            reason.push_back(-it->second);
                        }
                        while(!joinTuplesU->empty()){
                            auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second) == 0 ){
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                            propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }//close false for
                for(unsigned i = 0; i<tuplesU->size();){
                    std::vector<int> sharedVar({});
                    const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_.getValues(sharedVar);
                    const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_.getValues(sharedVar);
                    if(joinTuples->size() >= 4+1){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                for(unsigned j = 0; j < joinTuples->size(); j++){
                                    auto it = tupleToVar.find(*joinTuples->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                        }
                    }else if(joinTuples->size() + joinTuplesU->size() < 4+1){
                        auto itProp = tupleToVar.find(*tuplesU->at(i));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(-itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_.getValues(sharedVar);
                                for(unsigned j = 0; j < joinTuplesF->size(); j++){
                                    auto it = tupleToVar.find(*joinTuplesF->at(j));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-itProp->second].insert(-it->second);
                                    }
                                }
                            }
                            propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                        }
                    }else{
                        i++;
                    }
                }//close undef for
            }//close aggr set starter
            {
                if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple positiveTuple({},&_aggr_id0_0);
                    const Tuple* tuple1 = waggr_id0_0.find(positiveTuple);
                    if(tuple1 == tupleU && tupleU == NULL){
                        tuple1 = tupleU = uaggr_id0_0.find(positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0_0 && ! tupleUNegated){
                        if(tupleU == uaggr_id0_0.find(positiveTuple)){
                            tuple1=tupleU;
                        }
                    }
                    if(tuple1!=NULL){
                        Tuple negativeTuple({},&_aggr_id0_0_2);
                        const Tuple* tuple2 = waggr_id0_0_2.find(negativeTuple);
                        const Tuple* tupleUndef2 = uaggr_id0_0_2.find(negativeTuple);
                        if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                            tuple2 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef2 != NULL){
                            tupleU = tuple2 = tupleUndef2;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id0_0_2 && tupleUNegated && tupleU==tupleUndef2){
                            tuple2=tupleU;
                        }else if(tuple2!=NULL){
                            tuple2=NULL;
                        }
                        if(tuple2!=NULL){
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple1);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple2!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple2);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    const auto& it = tupleToVar.find(*tuple1);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                if(tuple2!=NULL){
                                    const auto& it = tupleToVar.find(*tuple2);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*-1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_aggr_id0_0_2 && starter.isNegated()){
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple positiveTuple({},&_aggr_id0_0);
                    const Tuple* tuple1 = waggr_id0_0.find(positiveTuple);
                    if(tuple1 == tupleU && tupleU == NULL){
                        tuple1 = tupleU = uaggr_id0_0.find(positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0_0 && ! tupleUNegated){
                        if(tupleU == uaggr_id0_0.find(positiveTuple)){
                            tuple1=tupleU;
                        }
                    }
                    if(tuple1!=NULL){
                        Tuple positiveTuple({},&_body0);
                        const Tuple* tuple2 = wbody0.find(positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = ubody0.find(positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                            if(tupleU == ubody0.find(positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple1);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple2!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple2);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    const auto& it = tupleToVar.find(*tuple1);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                if(tuple2!=NULL){
                                    const auto& it = tupleToVar.find(*tuple2);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
                if(starter.getPredicateName() == &_aggr_id0_0 && !starter.isNegated()){
                    const Tuple* tupleU = NULL;
                    bool tupleUNegated = false;
                    Tuple negativeTuple({},&_aggr_id0_0_2);
                    const Tuple* tuple1 = waggr_id0_0_2.find(negativeTuple);
                    const Tuple* tupleUndef1 = uaggr_id0_0_2.find(negativeTuple);
                    if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                        tuple1 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef1 != NULL){
                        tupleU = tuple1 = tupleUndef1;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id0_0_2 && tupleUNegated && tupleU==tupleUndef1){
                        tuple1=tupleU;
                    }else if(tuple1!=NULL){
                        tuple1=NULL;
                    }
                    if(tuple1!=NULL){
                        Tuple positiveTuple({},&_body0);
                        const Tuple* tuple2 = wbody0.find(positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = ubody0.find(positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                            if(tupleU == ubody0.find(positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            if(tupleU != NULL){
                                const auto& itUndef = tupleToVar.find(*tupleU);
                                if(itUndef!=tupleToVar.end()){
                                    int var = tupleUNegated ? 1 : -1;
                                    var*=itUndef->second;
                                    if(reasonForLiteral.count(var) == 0){
                                        {
                                            const auto& it = tupleToVar.find(starter);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                        if(tuple1!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple1);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*-1);
                                            }
                                        }
                                        if(tuple2!=tupleU){
                                            const auto& it = tupleToVar.find(*tuple2);
                                            if(it!=tupleToVar.end()){
                                                reasonForLiteral[var].insert(it->second*1);
                                            }
                                        }
                                    }
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    const auto& it = tupleToVar.find(*tuple1);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*-1);
                                    }
                                }
                                if(tuple2!=NULL){
                                    const auto& it = tupleToVar.find(*tuple2);
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[-startVar].insert(it->second*1);
                                    }
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
        }
    }
    }
