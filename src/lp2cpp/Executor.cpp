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

#include "datastructures/TupleFactory.h"

#include "datastructures/SmartPredicateSet.h"

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
using PredicateWSet = SmartPredicateSet;

std::unordered_map<const std::string*, PredicateWSet*> predicateWSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateFSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateUSetMap;
const std::string _bound = "bound";
PredicateWSet wbound(1);
PredicateWSet ubound(1);
PredicateWSet fbound(1);
const std::string _delete = "delete";
PredicateWSet wdelete(2);
PredicateWSet udelete(2);
PredicateWSet fdelete(2);
const std::string _edge = "edge";
PredicateWSet wedge(2);
PredicateWSet uedge(2);
PredicateWSet fedge(2);
const std::string _indeg = "indeg";
PredicateWSet windeg(2);
PredicateWSet uindeg(2);
PredicateWSet findeg(2);
const std::string _keep = "keep";
PredicateWSet wkeep(2);
PredicateWSet ukeep(2);
PredicateWSet fkeep(2);
const std::string _vertex = "vertex";
PredicateWSet wvertex(1);
PredicateWSet uvertex(1);
PredicateWSet fvertex(1);
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
std::unordered_map<int,UnorderedSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
bool undefinedLoaded=false;
std::unordered_map<int,int> actualSum;
std::unordered_map<int,int> possibleSum;
bool unRoll=false;
Executor::~Executor() {
}


const std::vector<const Tuple* > EMPTY_TUPLES;
std::unordered_map<std::string, const std::string * > stringToUniqueStringPointer;
typedef void (*ExplainNegative)(const std::vector<int> & lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output);

TupleFactory factory;
std::unordered_map<const std::string*, ExplainNegative> explainNegativeFunctionsMap;

const std::string* parseTuple(const std::string & literalString,std::vector<int>& terms) {
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
    return stringToUniqueStringPointer[predicateName];
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
AuxMap pvertex_({});
AuxMap uvertex_({});
AuxMap fvertex_({});
AuxMap pbound_({});
AuxMap ubound_({});
AuxMap fbound_({});
AuxMap pkeep_1_({1});
AuxMap ukeep_1_({1});
AuxMap fkeep_1_({1});
AuxMap pedge_({});
AuxMap uedge_({});
AuxMap fedge_({});
void Executor::handleConflict(int literal){
    if(currentDecisionLevel == -1){
        propagatedLiterals.insert(-1);
        return;
    }

    std::unordered_set<int> visitedLiterals;
    Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);
    explainExternalLiteral(literal,conflictReason,visitedLiterals,true);
    explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);
    propagatedLiterals.insert(-1);
    reasonForLiteral.erase(literal);
}
int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,std::unordered_set<int>& visitedLiteral,bool propagatorCall){
    if(!propagatorCall){
        int uVar = var>0 ? var : -var;
        int internalVar = factory.getTupleFromWASPID(uVar)->getId();
        var = var>0 ? internalVar : -internalVar;
    }
    std::vector<int> stack;
    stack.push_back(var);
    while(!stack.empty()){
        int lit = stack.back();
        stack.pop_back();
        for(unsigned i = 0; i<reasonForLiteral[lit].size(); i++){
            int reasonLiteral=reasonForLiteral[lit][i];
            Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);
            if(visitedLiteral.count(reasonLiteral) == 0){
                visitedLiteral.insert(reasonLiteral);
                if(literal->getWaspID()==0){
                    stack.push_back(reasonLiteral);
                }else{
                    int sign = reasonLiteral>0 ? 1 : -1;
                    reas.insert(sign * literal->getWaspID());
                }
            }
        }
    }
    return 0;
}
void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){
    return;
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
inline void Executor::onLiteralTrue(int var, const std::string& literalString) {
    std::vector<int> terms;
    const std::string* predicate = parseTuple(literalString,terms);
    Tuple* tuple = factory.addNewTuple(terms,predicate,var);
    std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple->getPredicateName());
    if(uSetIt!=predicateUSetMap.end()) {
        uSetIt->second->erase(*tuple);
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple->getPredicateName());
    if (it == predicateWSetMap.end()) {
        } else {
        if (var > 0) {
            const auto& insertResult = it->second->insert(tuple);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
    if (fSetIt == predicateFSetMap.end()) {
        } else {
        if (var < 0) {
            const auto& insertResult = fSetIt->second->insert(tuple);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[fSetIt->first]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
}
inline void Executor::onLiteralTrue(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    unRoll=false;
    std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple->getPredicateName());
    if(uSetIt!=predicateUSetMap.end()) {
        uSetIt->second->erase(*tuple);
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple->getPredicateName());
    if (it == predicateWSetMap.end()) {
        } else {
        if (var > 0) {
            const auto& insertResult = it->second->insert(tuple);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
    if (fSetIt == predicateFSetMap.end()) {
        } else {
        if (var < 0) {
            const auto& insertResult = fSetIt->second->insert(tuple);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[fSetIt->first]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    Tuple* tuple = factory.getTupleFromWASPID(uVar);
    int internalVar = var > 0 ? tuple->getId() : -tuple->getId();
    reasonForLiteral.erase(internalVar);
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    if (var > 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple->getPredicateName());
        if (wSetIt != predicateWSetMap.end()) {
            wSetIt->second->erase(*tuple);
        }
    }
    if (var < 0) {
        std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
        if (fSetIt != predicateWSetMap.end()) {
            fSetIt->second->erase(*tuple);
        }
    }
    std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple->getPredicateName());
    if (it == predicateUSetMap.end()) {
        } else {
        const auto& insertResult = it->second->insert(tuple);
        if (insertResult.second) {
            for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[it->first]) {
                auxMap -> insert2(*insertResult.first);
            }
        }
    }
    if(currentDecisionLevel >= 0){
    }
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
}
inline void Executor::addedVarName(int var, const std::string & atom) {
    std::vector<int> terms;
    const std::string* predicate = parseTuple(atom,terms);
    factory.addNewTuple(terms,predicate,var);
}
void Executor::clearPropagations() {
    propagatedLiteralsAndReasons.clear();
}
void Executor::clear() {
    failedConstraints.clear();
    predicateToAuxiliaryMaps.clear();
}
void Executor::init() {
    predicateWSetMap[&_bound]=&wbound;
    predicateUSetMap[&_bound]=&ubound;
    predicateFSetMap[&_bound]=&fbound;
    stringToUniqueStringPointer["bound"] = &_bound;
    predicateWSetMap[&_delete]=&wdelete;
    predicateUSetMap[&_delete]=&udelete;
    predicateFSetMap[&_delete]=&fdelete;
    stringToUniqueStringPointer["delete"] = &_delete;
    predicateWSetMap[&_edge]=&wedge;
    predicateUSetMap[&_edge]=&uedge;
    predicateFSetMap[&_edge]=&fedge;
    stringToUniqueStringPointer["edge"] = &_edge;
    predicateWSetMap[&_indeg]=&windeg;
    predicateUSetMap[&_indeg]=&uindeg;
    predicateFSetMap[&_indeg]=&findeg;
    stringToUniqueStringPointer["indeg"] = &_indeg;
    predicateWSetMap[&_keep]=&wkeep;
    predicateUSetMap[&_keep]=&ukeep;
    predicateFSetMap[&_keep]=&fkeep;
    stringToUniqueStringPointer["keep"] = &_keep;
    predicateWSetMap[&_vertex]=&wvertex;
    predicateUSetMap[&_vertex]=&uvertex;
    predicateFSetMap[&_vertex]=&fvertex;
    stringToUniqueStringPointer["vertex"] = &_vertex;
    predicateToAuxiliaryMaps[&_edge].push_back(&pedge_);
    predicateToAuxiliaryMaps[&_keep].push_back(&pkeep_1_);
    predicateToAuxiliaryMaps[&_bound].push_back(&pbound_);
    predicateToAuxiliaryMaps[&_vertex].push_back(&pvertex_);
    predicateToUndefAuxiliaryMaps[&_edge].push_back(&uedge_);
    predicateToUndefAuxiliaryMaps[&_keep].push_back(&ukeep_1_);
    predicateToUndefAuxiliaryMaps[&_bound].push_back(&ubound_);
    predicateToUndefAuxiliaryMaps[&_vertex].push_back(&uvertex_);
    predicateToFalseAuxiliaryMaps[&_edge].push_back(&fedge_);
    predicateToFalseAuxiliaryMaps[&_keep].push_back(&fkeep_1_);
    predicateToFalseAuxiliaryMaps[&_bound].push_back(&fbound_);
    predicateToFalseAuxiliaryMaps[&_vertex].push_back(&fvertex_);
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){
    if(tupleU->getWaspID() == 0){
        bool propagated=false;
        std::unordered_map<const std::string*,PredicateWSet*>::iterator falseSet = predicateFSetMap.find(tupleU->getPredicateName());
        std::unordered_map<const std::string*,PredicateWSet*>::iterator undefSet = predicateUSetMap.find(tupleU->getPredicateName());
        std::unordered_map<const std::string*,PredicateWSet*>::iterator trueSet = predicateWSetMap.find(tupleU->getPredicateName());
        if(falseSet==predicateFSetMap.end()){
            exit(180);
        }
        if(undefSet==predicateUSetMap.end()){
            exit(180);
        }
        if(trueSet==predicateWSetMap.end()){
            exit(180);
        }
        if(isNegated == asNegative){
            if(falseSet->second->find(*tupleU)!=NULL){
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                undefSet->second->erase(*tupleU);
                const auto& insertResult = trueSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToAuxiliaryMaps[trueSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    propagated = true;
                }
            }
        }else{
            if(trueSet->second->find(*tupleU)!=NULL){
                return true;
            }else if(undefSet->second->find(*tupleU)!=NULL){
                undefSet->second->erase(*tupleU);
                const auto& insertResult = falseSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[falseSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    propagated = true;
                }
            }
        }
        if(propagated){
            int it = tupleU->getId();
            int sign = isNegated != asNegative ? -1 : 1;
            stack.push_back(sign*it);
            levelToIntLiterals[currentDecisionLevel].push_back(sign*it);
        }
    }else{
        int it = tupleU->getWaspID();
        int sign = isNegated == asNegative ? -1 : 1;
        propagatedLiterals.insert(it*sign);
    }
    return false;
}
void Executor::printInternalLiterals(){
    {
        std::set<std::vector<int>> trueHeads;
        const std::vector<const Tuple*>* tuples = &pedge_.getValues({});
        for(unsigned i=0; i<tuples->size();i++){
            int X = tuples->at(i)->at(0);
            int Y = tuples->at(i)->at(1);
            Tuple* boundTuple = factory.addNewInternalTuple({X,Y},&_delete);
            if(wdelete.find(*boundTuple) == NULL && udelete.find(*boundTuple) == NULL){
                std::vector<int> head({X,Y});
                std::cout<<"keep("<<head[0]<<","<<head[1]<<")"<<std::endl;
                Tuple* tupleHead = factory.addNewInternalTuple(head,&_keep);
                if(wkeep.find(*tupleHead) == NULL){
                std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tupleHead->getPredicateName());
                if (it == predicateWSetMap.end()) {
                    } else {
                    const auto& insertResult = it->second->insert(tupleHead);
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                } // close undef insert 
            } // close find predicateset 
        }
    }
}
{
    std::set<std::vector<int>> trueHeads;
    const std::vector<const Tuple*>* tuples = &pvertex_.getValues({});
    for(unsigned i=0; i<tuples->size();i++){
        int V = tuples->at(i)->at(0);
        const std::vector<const Tuple*>* tuples = &pbound_.getValues({});
        for(unsigned i=0; i<tuples->size();i++){
            int K = tuples->at(i)->at(0);
            std::set<std::vector<int>> aggrSetKey;
            int aggregateValue=0;
            const std::vector<const Tuple*>* tuples = &pkeep_1_.getValues({V});
            for(unsigned i=0; i<tuples->size() && aggregateValue < K;i++){
                int X = tuples->at(i)->at(0);
                std::vector<int> aggrKey({X});
                if(aggrSetKey.count(aggrKey)==0){
                    aggrSetKey.insert(aggrKey);
                    aggregateValue+=1;
                }
            }
            if(aggregateValue >= K){
                std::vector<int> head({V,K});
                std::cout<<"indeg("<<head[0]<<","<<head[1]<<")"<<std::endl;
            }
        }
    }
}
}
void Executor::unRollToLevel(int decisionLevel){
for(unsigned i = 0; i<propagatedLiterals.size(); i++){
    int var = propagatedLiterals[i] > 0 ? propagatedLiterals[i] : -propagatedLiterals[i];
    int sign = propagatedLiterals[i] > 0 ? -1 : 1;
    Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);
    if(literalNotPropagated!=NULL)
        reasonForLiteral.erase(sign*literalNotPropagated->getId());
}
propagatedLiterals.clear();
while(currentDecisionLevel > decisionLevel){
    while(!levelToIntLiterals[currentDecisionLevel].empty()){
        int var = levelToIntLiterals[currentDecisionLevel].back();
        levelToIntLiterals[currentDecisionLevel].pop_back();
        reasonForLiteral.erase(var);
        int uVar = var>0 ? var : -var;
        Tuple* tuple = factory.getTupleFromInternalID(uVar);
        if (var > 0) {
            std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple->getPredicateName());
            if (wSetIt != predicateWSetMap.end()) {
                wSetIt->second->erase(*tuple);
            }
        } //true removing
        if (var < 0) {
            std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());
            if (fSetIt != predicateFSetMap.end()) {
                fSetIt->second->erase(*tuple);
            }
        }//false removing
        std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple->getPredicateName());
        if (it == predicateUSetMap.end()) {
            } else {
            const auto& insertResult = it->second->insert(tuple);
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
    int factVar = facts[i]>0 ? facts[i] : -facts[i];
    int minus = facts[i]<0 ? -1 : 1;
    propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());
    if(propagatedLiterals.contains(-facts[i])) propagatedLiterals.erase(-facts[i]);
}
if(decisionLevel>-1) {
}
if(decisionLevel==-1) {
    if(!undefinedLoaded)
        undefLiteralsReceived();
}//close decision level == -1
while(!propagationStack.empty()){
    int startVar = propagationStack.back();
    int uStartVar = startVar<0 ? -startVar : startVar;
    Tuple starter (*factory.getTupleFromInternalID(uStartVar));
    starter.setNegated(startVar<0);
    std::string minus = starter.isNegated() ? "not " : "";
    propagationStack.pop_back();
}
}
}
