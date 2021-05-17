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
const std::string _aggr_id0 = "aggr_id0";
PredicateWSet waggr_id0(1);
PredicateWSet uaggr_id0(1);
PredicateWSet faggr_id0(1);
const std::string _aggr_set0 = "aggr_set0";
PredicateWSet waggr_set0(3);
PredicateWSet uaggr_set0(3);
PredicateWSet faggr_set0(3);
const std::string _aux0 = "aux0";
PredicateWSet waux0(4);
PredicateWSet uaux0(4);
PredicateWSet faux0(4);
const std::string _factor = "factor";
PredicateWSet wfactor(2);
PredicateWSet ufactor(2);
PredicateWSet ffactor(2);
const std::string _remain = "remain";
PredicateWSet wremain(1);
PredicateWSet uremain(1);
PredicateWSet fremain(1);
const std::string _td = "td";
PredicateWSet wtd(3);
PredicateWSet utd(3);
PredicateWSet ftd(3);
std::map<int,int> externalLiteralsLevel;
std::map<int,std::vector<int>> levelToIntLiterals;
std::map<int,UnorderedSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
std::unordered_set<const std::string*> aggr_setPredicate;
std::unordered_map<const std::string*,std::vector<AuxMap*>> sumAggrIdForAggrSetAuxMap;
std::unordered_map<const std::string*,std::vector<AuxMap*>> sumAggrIdForAggrSetUAuxMap;
std::unordered_map<const std::string*,std::vector<AuxMap*>> sumAggrIdForAggrSetFAuxMap;
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
AuxMap ptd_({});
AuxMap utd_({});
AuxMap ftd_({});
AuxMap pfactor_0_({0});
AuxMap ufactor_0_({0});
AuxMap ffactor_0_({0});
AuxMap paux0_0_1_2_({0,1,2});
AuxMap uaux0_0_1_2_({0,1,2});
AuxMap faux0_0_1_2_({0,1,2});
AuxMap paggr_set0_({});
AuxMap uaggr_set0_({});
AuxMap faggr_set0_({});
AuxMap paux0_({});
AuxMap uaux0_({});
AuxMap faux0_({});
AuxMap paux0_1_2_3_({1,2,3});
AuxMap uaux0_1_2_3_({1,2,3});
AuxMap faux0_1_2_3_({1,2,3});
AuxMap pfactor_({});
AuxMap ufactor_({});
AuxMap ffactor_({});
AuxMap paux0_0_1_({0,1});
AuxMap uaux0_0_1_({0,1});
AuxMap faux0_0_1_({0,1});
AuxMap ptd_0_({0});
AuxMap utd_0_({0});
AuxMap ftd_0_({0});
AuxMap paggr_id0_({});
AuxMap uaggr_id0_({});
AuxMap faggr_id0_({});
AuxMap premain_({});
AuxMap uremain_({});
AuxMap fremain_({});
void Executor::handleConflict(int literal){
    std::cout<<"handle conflict "<<literal<<std::endl;
    if(currentDecisionLevel == -1){
        propagatedLiterals.insert(-1);
        return;
    }

    explainExternalLiteral(literal,conflictReason);
    explainExternalLiteral(-literal,conflictReason);
    propagatedLiterals.insert(-1);
    reasonForLiteral.erase(literal);
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
    if (var < 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple.getPredicateName());
        if (fSetIt != predicateWSetMap.end()) {
            fSetIt->second->erase(tuple);
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
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {//Generating aux0
        const std::vector<const Tuple*>* tuples = &ptd_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &utd_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int J = tuple0->at(0);
            int T = tuple0->at(1);
            int N = tuple0->at(2);
            const std::vector<const Tuple*>* tuples = &pfactor_0_.getValues({J});
            const std::vector<const Tuple*>* tuplesU = &ufactor_0_.getValues({J});
            bool undef1=false;
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple1=NULL;
                if(i<tuples->size()){
                    tuple1=tuples->at(i);
                }else{
                    tuple1=tuplesU->at(i-tuples->size());
                    undef1=true;
                }
                int I = tuple1->at(1);
                Tuple aux({I,J,N,T}, &_aux0);
                if(uaux0.find(aux) == NULL){
                    const auto& insertResult = uaux0.insert(Tuple({I,J,N,T},&_aux0));
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux0]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                        atomsTable.push_back(aux);
                        tupleToVar[aux]=atomsTable.size()-1;
                        Tuple head({I,J,N},&_aggr_set0);
                        if(uaggr_set0.find(head)==NULL){
                            const auto& headInsertResult = uaggr_set0.insert(Tuple({I,J,N},&_aggr_set0));
                            if (headInsertResult.second) {
                                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set0]) {
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
    {
        const std::vector<const Tuple*>* tuples = &premain_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uremain_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=tuples->at(i);
            }else{
                tuple=tuplesU->at(i-tuples->size());
            }
            Tuple head({tuple->at(0)},&_aggr_id0);
            const auto& insertResult = uaggr_id0.insert(Tuple({tuple->at(0)},&_aggr_id0));
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id0]) {
                    auxMap -> insert2(*insertResult.first);
                }
                atomsTable.push_back(head);
                tupleToVar[head]=atomsTable.size()-1;
            }
        }
    }
    {
        const std::vector<const Tuple*>* aggregateIds = &uaggr_id0_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            auto it = tupleToVar.find(*aggregateIds->at(i));
            if(it!=tupleToVar.end()){
                const std::vector<const Tuple*>* aggrSetTuples = &uaggr_set0_.getValues({});
                for(unsigned j=0; j<aggrSetTuples->size(); j++)
                    possibleSum[it->second]+=aggrSetTuples->at(j)->at(0);
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
    waggr_id0.clear();
    waggr_set0.clear();
    paggr_id0_.clear();
    paggr_set0_.clear();
    faggr_id0_.clear();
    faggr_set0_.clear();
}
void Executor::init() {
    predicateWSetMap[&_aggr_id0]=&waggr_id0;
    predicateUSetMap[&_aggr_id0]=&uaggr_id0;
    predicateFSetMap[&_aggr_id0]=&faggr_id0;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    predicateWSetMap[&_aggr_set0]=&waggr_set0;
    predicateUSetMap[&_aggr_set0]=&uaggr_set0;
    predicateFSetMap[&_aggr_set0]=&faggr_set0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    predicateWSetMap[&_aux0]=&waux0;
    predicateUSetMap[&_aux0]=&uaux0;
    predicateFSetMap[&_aux0]=&faux0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    predicateWSetMap[&_factor]=&wfactor;
    predicateUSetMap[&_factor]=&ufactor;
    predicateFSetMap[&_factor]=&ffactor;
    stringToUniqueStringPointer["factor"] = &_factor;
    predicateWSetMap[&_remain]=&wremain;
    predicateUSetMap[&_remain]=&uremain;
    predicateFSetMap[&_remain]=&fremain;
    stringToUniqueStringPointer["remain"] = &_remain;
    predicateWSetMap[&_td]=&wtd;
    predicateUSetMap[&_td]=&utd;
    predicateFSetMap[&_td]=&ftd;
    stringToUniqueStringPointer["td"] = &_td;
    predicateToAuxiliaryMaps[&_remain].push_back(&premain_);
    predicateToAuxiliaryMaps[&_aggr_id0].push_back(&paggr_id0_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_);
    predicateToAuxiliaryMaps[&_aux0].push_back(&paux0_);
    predicateToAuxiliaryMaps[&_aux0].push_back(&paux0_0_1_);
    predicateToAuxiliaryMaps[&_aux0].push_back(&paux0_0_1_2_);
    predicateToAuxiliaryMaps[&_aux0].push_back(&paux0_1_2_3_);
    predicateToAuxiliaryMaps[&_factor].push_back(&pfactor_);
    predicateToAuxiliaryMaps[&_factor].push_back(&pfactor_0_);
    predicateToAuxiliaryMaps[&_td].push_back(&ptd_);
    predicateToAuxiliaryMaps[&_td].push_back(&ptd_0_);
    predicateToUndefAuxiliaryMaps[&_remain].push_back(&uremain_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0].push_back(&uaggr_id0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_);
    predicateToUndefAuxiliaryMaps[&_aux0].push_back(&uaux0_);
    predicateToUndefAuxiliaryMaps[&_aux0].push_back(&uaux0_0_1_);
    predicateToUndefAuxiliaryMaps[&_aux0].push_back(&uaux0_0_1_2_);
    predicateToUndefAuxiliaryMaps[&_aux0].push_back(&uaux0_1_2_3_);
    predicateToUndefAuxiliaryMaps[&_factor].push_back(&ufactor_);
    predicateToUndefAuxiliaryMaps[&_factor].push_back(&ufactor_0_);
    predicateToUndefAuxiliaryMaps[&_td].push_back(&utd_);
    predicateToUndefAuxiliaryMaps[&_td].push_back(&utd_0_);
    predicateToFalseAuxiliaryMaps[&_remain].push_back(&fremain_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0].push_back(&faggr_id0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_);
    predicateToFalseAuxiliaryMaps[&_aux0].push_back(&faux0_);
    predicateToFalseAuxiliaryMaps[&_aux0].push_back(&faux0_0_1_);
    predicateToFalseAuxiliaryMaps[&_aux0].push_back(&faux0_0_1_2_);
    predicateToFalseAuxiliaryMaps[&_aux0].push_back(&faux0_1_2_3_);
    predicateToFalseAuxiliaryMaps[&_factor].push_back(&ffactor_);
    predicateToFalseAuxiliaryMaps[&_factor].push_back(&ffactor_0_);
    predicateToFalseAuxiliaryMaps[&_td].push_back(&ftd_);
    predicateToFalseAuxiliaryMaps[&_td].push_back(&ftd_0_);
    aggr_setPredicate.insert(&_aggr_set0);
    sumAggrIdForAggrSetAuxMap[&_aggr_set0].push_back(&paggr_id0_);
    sumAggrIdForAggrSetUAuxMap[&_aggr_set0].push_back(&uaggr_id0_);
    sumAggrIdForAggrSetFAuxMap[&_aggr_set0].push_back(&faggr_id0_);
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){
    if(tupleU->getPredicateName() == &_aggr_id0 || tupleU->getPredicateName() == &_aux0 || tupleU->getPredicateName() == &_aggr_set0){
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
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                const auto& insertResult = trueSet->second->insert(Tuple(*tupleU));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToAuxiliaryMaps[trueSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                                if(itAggrId != tupleToVar.end()){
                                    actualSum[itAggrId->second]+=tupleU->at(0);
                                    possibleSum[itAggrId->second]-=tupleU->at(0);
                                }
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                                if(itAggrId != tupleToVar.end()){
                                    actualSum[itAggrId->second]+=tupleU->at(0);
                                    possibleSum[itAggrId->second]-=tupleU->at(0);
                                }
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                                if(itAggrId != tupleToVar.end()){
                                    actualSum[itAggrId->second]+=tupleU->at(0);
                                    possibleSum[itAggrId->second]-=tupleU->at(0);
                                }
                            }
                        }
                    }
                    propagated = true;
                }
            }
        }else{
            if(trueSet->second->find(*tupleU)!=NULL){
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                const auto& insertResult = falseSet->second->insert(Tuple(*tupleU));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[falseSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    if(tupleU->getPredicateName() == &_aggr_set0){
                        {
                            const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                                if(itAggrId != tupleToVar.end()){
                                    possibleSum[itAggrId->second]-=tupleU->at(0);
                                }
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                                if(itAggrId != tupleToVar.end()){
                                    possibleSum[itAggrId->second]-=tupleU->at(0);
                                }
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                                if(itAggrId != tupleToVar.end()){
                                    possibleSum[itAggrId->second]-=tupleU->at(0);
                                }
                            }
                        }
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
            if(tuple.getPredicateName() == &_aggr_set0){
                {
                    const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                        if(itAggrId != tupleToVar.end()){
                            if(var>0)
                                actualSum[itAggrId->second]-=tuple[0];
                            possibleSum[itAggrId->second]+=tuple[0];
                        }
                    }
                }
                {
                    const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                        if(itAggrId != tupleToVar.end()){
                            if(var>0)
                                actualSum[itAggrId->second]-=tuple[0];
                            possibleSum[itAggrId->second]+=tuple[0];
                        }
                    }
                }
                {
                    const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        auto itAggrId = tupleToVar.find(*aggrIds->at(i));
                        if(itAggrId != tupleToVar.end()){
                            if(var>0)
                                actualSum[itAggrId->second]-=tuple[0];
                            possibleSum[itAggrId->second]+=tuple[0];
                        }
                    }
                }
            }
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
    if(decisionLevel>-1) {
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int P = tuples->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                auto aggrIdIt=tupleToVar.find(*tuples->at(i));
                if(aggrIdIt == tupleToVar.end()) {std::cout<<"Unable to find aggr id"<<std::endl; continue;}
                if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second] < P+1){
                    std::cout<<"Conflitct on aggregate starting from true aggr id "<<std::endl;
                    propagatedLiterals.insert(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second]-joinTuplesU->at(index)->at(0) >= P+1) {index++; continue;}
                        auto itProp = tupleToVar.find(*joinTuplesU->at(index));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
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
                            propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int P = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
                auto aggrIdIt=tupleToVar.find(*tuplesF->at(i));
                if(aggrIdIt == tupleToVar.end()) {std::cout<<"Unable to find aggr id"<<std::endl; continue;}
                if(actualSum[aggrIdIt->second] >= P+1){
                    std::cout<<"Conflitct on aggregate starting from false aggr id "<<actualSum[aggrIdIt->second]<<std::endl;
                    propagatedLiterals.insert(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(index));
                        if(actualSum[aggrIdIt->second]+joinTuplesU->at(index)->at(0) >= P+1){
                            if(itProp != tupleToVar.end()){
                                if(reasonForLiteral.count(-itProp->second) == 0 ){
                                    if(reason.empty()){
                                        for(unsigned i =0; i< joinTuples->size(); i++){
                                            auto it = tupleToVar.find(*joinTuples->at(i));
                                            if(it != tupleToVar.end()){
                                                reason.push_back(it->second);
                                                reasonForLiteral[-itProp->second].insert(it->second);
                                            }
                                        }
                                        auto it = tupleToVar.find(*tuplesF->at(i));
                                        if(it!= tupleToVar.end()){
                                            reason.push_back(-it->second);
                                            reasonForLiteral[-itProp->second].insert(-it->second);
                                        }
                                    }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }//close false for
        for(unsigned i = 0; i<tuplesU->size();){
            int P = tuplesU->at(i)->at(0);
            std::vector<int> sharedVar({});
            const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
            auto aggrIdIt=tupleToVar.find(*tuplesU->at(i));
            if(aggrIdIt == tupleToVar.end()) {std::cout<<"Unable to find aggr id"<<std::endl; continue;}
            if(actualSum[aggrIdIt->second] >= P+1){
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
            }else if(actualSum[aggrIdIt->second] + possibleSum[aggrIdIt->second] < P+1){
                auto itProp = tupleToVar.find(*tuplesU->at(i));
                if(itProp != tupleToVar.end()){
                    if(reasonForLiteral.count(-itProp->second) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
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
        {
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple*>* tuples = &premain_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uremain_.getValues({});
            else if(tupleU->getPredicateName() == &_remain && !tupleUNegated)
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
                    int P = tuple0->at(0);
                    Tuple positiveTuple({P},&_aggr_id0);
                    const Tuple* tuple1 = waggr_id0.find(positiveTuple);
                    if(tuple1 == tupleU && tupleU == NULL){
                        tuple1 = tupleU = uaggr_id0.find(positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0 && ! tupleUNegated){
                        if(tupleU == uaggr_id0.find(positiveTuple)){
                            tuple1=tupleU;
                        }
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
            const std::vector<const Tuple*>* tuples = &ptd_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &utd_.getValues({});
            else if(tupleU->getPredicateName() == &_td && !tupleUNegated)
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
                    int J = tuple0->at(0);
                    int T = tuple0->at(1);
                    int N = tuple0->at(2);
                    const std::vector<const Tuple*>* tuples = &pfactor_0_.getValues({J});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ufactor_0_.getValues({J});
                    else if(tupleU->getPredicateName() == &_factor && !tupleUNegated)
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
                            if(tupleU->at(0) == J)
                                tuple1 = tupleU;
                        }
                        if(tuple1!=NULL){
                            int I = tuple1->at(1);
                            Tuple negativeTuple({I,J,N,T},&_aux0);
                            const Tuple* tuple2 = waux0.find(negativeTuple);
                            const Tuple* tupleUndef2 = uaux0.find(negativeTuple);
                            if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                                tuple2 = &negativeTuple;
                            else if(tupleU == NULL & tupleUndef2 != NULL){
                                tupleU = tuple2 = tupleUndef2;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef2){
                                tuple2=tupleU;
                            }else if(tuple2!=NULL){
                                tuple2=NULL;
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
                    int I = tuple0->at(0);
                    int J = tuple0->at(1);
                    int N = tuple0->at(2);
                    int T = tuple0->at(3);
                    Tuple negativeTuple({J,I},&_factor);
                    const Tuple* tuple1 = wfactor.find(negativeTuple);
                    const Tuple* tupleUndef1 = ufactor.find(negativeTuple);
                    if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                        tuple1 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef1 != NULL){
                        tupleU = tuple1 = tupleUndef1;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_factor && tupleUNegated && tupleU==tupleUndef1){
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
                    int I = tuple0->at(0);
                    int J = tuple0->at(1);
                    int N = tuple0->at(2);
                    int T = tuple0->at(3);
                    Tuple negativeTuple({J,T,N},&_td);
                    const Tuple* tuple1 = wtd.find(negativeTuple);
                    const Tuple* tupleUndef1 = utd.find(negativeTuple);
                    if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                        tuple1 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef1 != NULL){
                        tupleU = tuple1 = tupleUndef1;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_td && tupleUNegated && tupleU==tupleUndef1){
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
        const std::vector<const Tuple*>* trueHeads = &paggr_set0_.getValues({});
        for(unsigned i = 0; i < trueHeads->size(); i++){
            const Tuple* head = trueHeads->at(i);
            int I = head->at(0);
            int J = head->at(1);
            int N = head->at(2);
            const std::vector<const Tuple*>* tuples = &paux0_0_1_2_.getValues({I,J,N});
            const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
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
        const std::vector<const Tuple*>* undefHeads = &uaggr_set0_.getValues({});
        for(unsigned i = 0; i < undefHeads->size(); i++){
            const Tuple* head = undefHeads->at(i);
            int I = head->at(0);
            int J = head->at(1);
            int N = head->at(2);
            const std::vector<const Tuple*>* tuples = &paux0_0_1_2_.getValues({I,J,N});
            if(tuples->size() == 0){
                const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
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
        const std::vector<const Tuple*>* falseHeads = &faggr_set0_.getValues({});
        for(unsigned i = 0; i < falseHeads->size(); i++){
            const Tuple* head = falseHeads->at(i);
            int I = head->at(0);
            int J = head->at(1);
            int N = head->at(2);
            const std::vector<const Tuple*>* tuples = &paux0_0_1_2_.getValues({I,J,N});
            if(tuples->size() == 0){
                const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
                for(unsigned j = 0; j < tuplesU->size();){
                    propUndefined(tuplesU->at(j),false,propagationStack,true,propagatedLiterals);
                }
            }else{
                propagatedLiterals.insert(-1);
            }
        }
    }
}//close decision level == -1
while(!propagationStack.empty()){
    int startVar = propagationStack.back();
    int uStartVar = startVar<0 ? -startVar : startVar;
    Tuple starter = atomsTable[uStartVar];
    starter.setNegated(startVar<0);
    propagationStack.pop_back();
    if(starter.getPredicateName() == &_aggr_set0){
        int I = starter[0];
        int J = starter[1];
        int N = starter[2];
        const std::vector<const Tuple*>* tuples = &paux0_0_1_2_.getValues({I,J,N});
        const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
        if(!starter.isNegated()){
            if(tuples->size() == 0 && tuplesU->size() == 0){
                const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
                        const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
                    if(reasonForLiteral.count(-it->second) == 0 )
                        reasonForLiteral[-it->second].insert(startVar);
                    propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }//close if starter
    if(starter.getPredicateName() == &_aux0){
        int I = starter[0];
        int J = starter[1];
        int N = starter[2];
        int T = starter[3];
        if(!starter.isNegated()){
            Tuple head({I,J,N}, &_aggr_set0);
            const Tuple* tupleU = uaggr_set0.find(head);
            if(waggr_set0.find(head) == tupleU && tupleU==NULL){
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
            Tuple head({I,J,N}, &_aggr_set0);
            const std::vector<const Tuple*>* tuples = &paux0_0_1_2_.getValues({I,J,N});
            const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
            if(waggr_set0.find(head) != NULL){
                if(tuples->size()==0 && tuplesU->size()==0){
                    const auto itHead = tupleToVar.find(head);
                    if(itHead!=tupleToVar.end()){
                        const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
                            const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
                const Tuple* tupleU = uaggr_set0.find(head);
                if(tupleU != NULL && tuples->size() == 0 && tuplesU->size() == 0){
                    const auto itHead = tupleToVar.find(head);
                    if(itHead!=tupleToVar.end()){
                        if(reasonForLiteral.count(-itHead->second) == 0 ){
                            const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
    if(starter.getPredicateName() == &_aggr_set0){
        int I = starter[0];
        int J = starter[1];
        int N = starter[2];
        const std::vector<const Tuple*>* tuples = &paux0_0_1_2_.getValues({I,J,N});
        const std::vector<const Tuple*>* tuplesU = &uaux0_0_1_2_.getValues({I,J,N});
        if(!starter.isNegated()){
            if(tuples->size() == 0 && tuplesU->size() == 0){
                const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
                        const std::vector<const Tuple*>* tuplesF = &faux0_0_1_2_.getValues({I,J,N});
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
                    if(reasonForLiteral.count(-it->second) == 0 )
                        reasonForLiteral[-it->second].insert(startVar);
                    propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);
                }
            }
        }
    }//close if starter
    {
        if(starter.getPredicateName() == &_td && starter.isNegated()){
            int J = starter[0];
            int T = starter[1];
            int N = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple*>* tuples = &paux0_1_2_3_.getValues({J,N,T});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux0_1_2_3_.getValues({J,N,T});
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
                const Tuple* tuple1 = NULL;
                if(i<tuples->size())
                    tuple1 = tuples->at(i);
                else if(i<tuples->size()+tuplesU->size()){
                    tupleU = tuple1 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                }else if(!undeRepeated.empty()){
                    if(tupleU->at(1) == J && tupleU->at(2) == N && tupleU->at(3) == T)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int I = tuple1->at(0);
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
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            Tuple negativeTuple({J,T,N},&_td);
            const Tuple* tuple1 = wtd.find(negativeTuple);
            const Tuple* tupleUndef1 = utd.find(negativeTuple);
            if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                tuple1 = &negativeTuple;
            else if(tupleU == NULL & tupleUndef1 != NULL){
                tupleU = tuple1 = tupleUndef1;
                tupleUNegated=true;
            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_td && tupleUNegated && tupleU==tupleUndef1){
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
        if(starter.getPredicateName() == &_factor && starter.isNegated()){
            int J = starter[0];
            int I = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple*>* tuples = &paux0_0_1_.getValues({I,J});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &uaux0_0_1_.getValues({I,J});
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
                const Tuple* tuple1 = NULL;
                if(i<tuples->size())
                    tuple1 = tuples->at(i);
                else if(i<tuples->size()+tuplesU->size()){
                    tupleU = tuple1 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                }else if(!undeRepeated.empty()){
                    if(tupleU->at(0) == I && tupleU->at(1) == J)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int N = tuple1->at(2);
                    int T = tuple1->at(3);
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
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            Tuple negativeTuple({J,I},&_factor);
            const Tuple* tuple1 = wfactor.find(negativeTuple);
            const Tuple* tupleUndef1 = ufactor.find(negativeTuple);
            if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                tuple1 = &negativeTuple;
            else if(tupleU == NULL & tupleUndef1 != NULL){
                tupleU = tuple1 = tupleUndef1;
                tupleUNegated=true;
            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_factor && tupleUNegated && tupleU==tupleUndef1){
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
            int I = starter[0];
            int J = starter[1];
            int N = starter[2];
            int T = starter[3];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            Tuple positiveTuple({J,T,N},&_td);
            const Tuple* tuple1 = wtd.find(positiveTuple);
            if(tuple1 == tupleU && tupleU == NULL){
                tuple1 = tupleU = utd.find(positiveTuple);
                tupleUNegated=false;
            }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_td && ! tupleUNegated){
                if(tupleU == utd.find(positiveTuple)){
                    tuple1=tupleU;
                }
            }
            if(tuple1!=NULL){
                Tuple positiveTuple({J,I},&_factor);
                const Tuple* tuple2 = wfactor.find(positiveTuple);
                if(tuple2 == tupleU && tupleU == NULL){
                    tuple2 = tupleU = ufactor.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_factor && ! tupleUNegated){
                    if(tupleU == ufactor.find(positiveTuple)){
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
        if(starter.getPredicateName() == &_factor && !starter.isNegated()){
            int J = starter[0];
            int I = starter[1];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple*>* tuples = &ptd_0_.getValues({J});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &utd_0_.getValues({J});
            else if(tupleU->getPredicateName() == &_td && !tupleUNegated)
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
                    if(tupleU->at(0) == J)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int T = tuple1->at(1);
                    int N = tuple1->at(2);
                    Tuple negativeTuple({I,J,N,T},&_aux0);
                    const Tuple* tuple2 = waux0.find(negativeTuple);
                    const Tuple* tupleUndef2 = uaux0.find(negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef2){
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
        }
        if(starter.getPredicateName() == &_td && !starter.isNegated()){
            int J = starter[0];
            int T = starter[1];
            int N = starter[2];
            const Tuple* tupleU = NULL;
            bool tupleUNegated = false;
            const std::vector<const Tuple*>* tuples = &pfactor_0_.getValues({J});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            std::vector<const Tuple*> undeRepeated;
            if(tupleU == NULL)
                tuplesU = &ufactor_0_.getValues({J});
            else if(tupleU->getPredicateName() == &_factor && !tupleUNegated)
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
                    if(tupleU->at(0) == J)
                        tuple1 = tupleU;
                }
                if(tuple1!=NULL){
                    int I = tuple1->at(1);
                    Tuple negativeTuple({I,J,N,T},&_aux0);
                    const Tuple* tuple2 = waux0.find(negativeTuple);
                    const Tuple* tupleUndef2 = uaux0.find(negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = &negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux0 && tupleUNegated && tupleU==tupleUndef2){
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
        }
    }
    if(starter.getPredicateName() == &_aggr_id0){
        int P = starter[0];
        std::vector<int> sharedVar({});
        const std::vector<const Tuple*>* tuples = &paggr_set0_.getValues(sharedVar);
        const std::vector<const Tuple*>* tuplesU = &uaggr_set0_.getValues(sharedVar);
        if(starter.isNegated()){
            if(actualSum[uStartVar]>=P+1){
                std::cout<<"Conflitct on aggregate start from aggrId false"<<std::endl;
                for(unsigned i =0; i< tuples->size(); i++){
                    auto it = tupleToVar.find(*tuples->at(i));
                    if(it != tupleToVar.end()){
                        reasonForLiteral[-startVar].insert(it->second);
                    }
                }
                handleConflict(-startVar);
                return;
            }else{
                std::vector<int> reason;
                for(int index=0; index<tuplesU->size();){
                    if(actualSum[uStartVar]+tuplesU->at(index)->at(0) >= P+1){
                        auto itProp = tupleToVar.find(*tuplesU->at(index));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(-itProp->second)==0){
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        auto it = tupleToVar.find(*tuples->at(i));
                                        if(it != tupleToVar.end()){
                                            reason.push_back(it->second);
                                            reasonForLiteral[-itProp->second].insert(it->second);
                                        }
                                    }
                                    reason.push_back(startVar);
                                    reasonForLiteral[-itProp->second].insert(startVar);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp->second].insert(reasonLit);
                                }
                            }
                        }
                        propUndefined(tuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                    }else index++;
                }
            }
        }else{
            if(actualSum[uStartVar]+possibleSum[uStartVar] < P+1){
                std::cout<<"Conflitct on aggregate starting from aggrId true"<<std::endl;
                const std::vector<const Tuple*>* tuplesF = &faggr_set0_.getValues(sharedVar);
                for(unsigned i = 0; i < tuplesF->size(); i++){
                    auto it = tupleToVar.find(*tuplesF->at(i));
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-startVar].insert(-it->second);
                    }
                }
                handleConflict(-startVar);
                return;
            }else{
                for(unsigned index=0;index<tuplesU->size();){
                    if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at(0) < P+1){
                        auto itProp = tupleToVar.find(*tuplesU->at(index));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set0_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    auto it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!=tupleToVar.end()){
                                        reasonForLiteral[itProp->second].insert(-it->second);
                                    }
                                }
                                reasonForLiteral[itProp->second].insert(startVar);
                            }
                            propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                        }
                    }else index++;
                }
            }
        }
    }//close aggr id starter
    if(starter.getPredicateName() == &_aggr_set0){
        const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
        const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
        for(unsigned i = 0; i<tuples->size(); i++){
            int P = tuples->at(i)->at(0);
            std::vector<int> sharedVar({});
            const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
            auto aggrIdIt=tupleToVar.find(*tuples->at(i));
            if(aggrIdIt == tupleToVar.end()) {std::cout<<"Unable to find aggr id"<<std::endl; continue;}
            if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second] < P+1){
                std::cout<<"Conflitct on aggregate starting from true aggr id "<<std::endl;
                auto itProp = tupleToVar.find(*tuples->at(i));
                if(itProp!=tupleToVar.end()){
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        auto it = tupleToVar.find(*joinTuplesF->at(j));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-itProp->second].insert(-it->second);
                        }
                    }
                    handleConflict(-itProp->second);
                    return;
                }
            }else{
                for(unsigned index=0; index<joinTuplesU->size();){
                    if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second]-joinTuplesU->at(index)->at(0) >= P+1) {index++; continue;}
                    auto itProp = tupleToVar.find(*joinTuplesU->at(index));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
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
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close true for
        for(unsigned i = 0; i<tuplesF->size(); i++){
            int P = tuplesF->at(i)->at(0);
            std::vector<int> sharedVar({});
            const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
            const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
            auto aggrIdIt=tupleToVar.find(*tuplesF->at(i));
            if(aggrIdIt == tupleToVar.end()) {std::cout<<"Unable to find aggr id"<<std::endl; continue;}
            if(actualSum[aggrIdIt->second] >= P+1){
                std::cout<<"Conflitct on aggregate starting from false aggr id "<<actualSum[aggrIdIt->second]<<std::endl;
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
            }else{
                std::vector<int> reason;
                for(unsigned index=0;index<joinTuplesU->size();){
                    auto itProp = tupleToVar.find(*joinTuplesU->at(index));
                    if(actualSum[aggrIdIt->second]+joinTuplesU->at(index)->at(0) >= P+1){
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(-itProp->second) == 0 ){
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        auto it = tupleToVar.find(*joinTuples->at(i));
                                        if(it != tupleToVar.end()){
                                            reason.push_back(it->second);
                                            reasonForLiteral[-itProp->second].insert(it->second);
                                        }
                                    }
                                    auto it = tupleToVar.find(*tuplesF->at(i));
                                    if(it!= tupleToVar.end()){
                                        reason.push_back(-it->second);
                                        reasonForLiteral[-itProp->second].insert(-it->second);
                                    }
                                }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp->second].insert(reasonLit);
                            }
                        }
                    }
                    propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                }else index++;
            }
        }
    }//close false for
    for(unsigned i = 0; i<tuplesU->size();){
        int P = tuplesU->at(i)->at(0);
        std::vector<int> sharedVar({});
        const std::vector<const Tuple*>* joinTuples = &paggr_set0_.getValues(sharedVar);
        const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_.getValues(sharedVar);
        auto aggrIdIt=tupleToVar.find(*tuplesU->at(i));
        if(aggrIdIt == tupleToVar.end()) {std::cout<<"Unable to find aggr id"<<std::endl; continue;}
        if(actualSum[aggrIdIt->second] >= P+1){
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
        }else if(actualSum[aggrIdIt->second] + possibleSum[aggrIdIt->second] < P+1){
            auto itProp = tupleToVar.find(*tuplesU->at(i));
            if(itProp != tupleToVar.end()){
                if(reasonForLiteral.count(-itProp->second) == 0 ){
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_.getValues(sharedVar);
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
    if(starter.getPredicateName() == &_aggr_id0 && !starter.isNegated()){
        int P = starter[0];
        const Tuple* tupleU = NULL;
        bool tupleUNegated = false;
        Tuple positiveTuple({P},&_remain);
        const Tuple* tuple1 = wremain.find(positiveTuple);
        if(tuple1 == tupleU && tupleU == NULL){
            tuple1 = tupleU = uremain.find(positiveTuple);
            tupleUNegated=false;
        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_remain && ! tupleUNegated){
            if(tupleU == uremain.find(positiveTuple)){
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
                                reasonForLiteral[var].insert(it->second*1);
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
    if(starter.getPredicateName() == &_remain && !starter.isNegated()){
        int P = starter[0];
        const Tuple* tupleU = NULL;
        bool tupleUNegated = false;
        Tuple positiveTuple({P},&_aggr_id0);
        const Tuple* tuple1 = waggr_id0.find(positiveTuple);
        if(tuple1 == tupleU && tupleU == NULL){
            tuple1 = tupleU = uaggr_id0.find(positiveTuple);
            tupleUNegated=false;
        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0 && ! tupleUNegated){
            if(tupleU == uaggr_id0.find(positiveTuple)){
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
                                reasonForLiteral[var].insert(it->second*1);
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
}
}
