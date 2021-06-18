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
const std::string _aggr_id0 = "aggr_id0";
PredicateWSet waggr_id0(1);
PredicateWSet uaggr_id0(1);
PredicateWSet faggr_id0(1);
const std::string _aggr_id1 = "aggr_id1";
PredicateWSet waggr_id1(1);
PredicateWSet uaggr_id1(1);
PredicateWSet faggr_id1(1);
const std::string _location = "location";
PredicateWSet wlocation(1);
PredicateWSet ulocation(1);
PredicateWSet flocation(1);
const std::string _max_total_weight = "max_total_weight";
PredicateWSet wmax_total_weight(1);
PredicateWSet umax_total_weight(1);
PredicateWSet fmax_total_weight(1);
const std::string _leafPos = "leafPos";
PredicateWSet wleafPos(2);
PredicateWSet uleafPos(2);
PredicateWSet fleafPos(2);
const std::string _scost = "scost";
PredicateWSet wscost(3);
PredicateWSet uscost(3);
PredicateWSet fscost(3);
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
AuxMap paggr_id0_({});
AuxMap uaggr_id0_({});
AuxMap faggr_id0_({});
AuxMap pscost_({});
AuxMap uscost_({});
AuxMap fscost_({});
AuxMap pmax_total_weight_({});
AuxMap umax_total_weight_({});
AuxMap fmax_total_weight_({});
AuxMap paggr_id1_({});
AuxMap uaggr_id1_({});
AuxMap faggr_id1_({});
AuxMap paggr_id1_0_({0});
AuxMap uaggr_id1_0_({0});
AuxMap faggr_id1_0_({0});
AuxMap pleafPos_1_({1});
AuxMap uleafPos_1_({1});
AuxMap fleafPos_1_({1});
AuxMap plocation_({});
AuxMap ulocation_({});
AuxMap flocation_({});
void Executor::handleConflict(int literal){
    std::cout<<"Handle conflict"<<std::endl;
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
    if(tuple->getPredicateName() == &_scost){
        {
            const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i)->getId();
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(0);
                possibleSum[itAggrId]-=tuple->at(0);
            }
        }
        {
            const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i)->getId();
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(0);
                possibleSum[itAggrId]-=tuple->at(0);
            }
        }
        {
            const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
            for(unsigned i=0;i<aggrIds->size();i++){
                int itAggrId = aggrIds->at(i)->getId();
                if(var>0)
                    actualSum[itAggrId]+=tuple->at(0);
                possibleSum[itAggrId]-=tuple->at(0);
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
        if(tuple->getPredicateName() == &_scost){
            {
                const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i)->getId();
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i)->getId();
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
            {
                const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                for(unsigned i=0;i<aggrIds->size();i++){
                    int itAggrId = aggrIds->at(i)->getId();
                    if(var>0)
                        actualSum[itAggrId]-=tuple->at(0);
                    possibleSum[itAggrId]+=tuple->at(0);
                }
            }
        }
    }
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {
        const std::vector<const Tuple*>* tuples = &plocation_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ulocation_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=tuples->at(i);
            }else{
                tuple=tuplesU->at(i-tuples->size());
            }
            Tuple* head = factory.addNewInternalTuple({tuple->at(0)},&_aggr_id1);
            const auto& insertResult = uaggr_id1.insert(head);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id1]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &pmax_total_weight_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &umax_total_weight_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=tuples->at(i);
            }else{
                tuple=tuplesU->at(i-tuples->size());
            }
            Tuple* head = factory.addNewInternalTuple({tuple->at(0)},&_aggr_id0);
            const auto& insertResult = uaggr_id0.insert(head);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id0]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* aggregateIds = &uaggr_id0_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i)->getId();
            const std::vector<const Tuple*>* aggrSetTuples = &uscost_.getValues({});
            for(unsigned j=0; j<aggrSetTuples->size(); j++)
                possibleSum[it]+=aggrSetTuples->at(j)->at(0);
        }
    }
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
    waggr_id0.clear();
    waggr_id1.clear();
    paggr_id1_.clear();
    paggr_id1_0_.clear();
    paggr_id0_.clear();
    faggr_id1_.clear();
    faggr_id1_0_.clear();
    faggr_id0_.clear();
}
void Executor::init() {
    predicateWSetMap[&_aggr_id0]=&waggr_id0;
    predicateUSetMap[&_aggr_id0]=&uaggr_id0;
    predicateFSetMap[&_aggr_id0]=&faggr_id0;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    predicateWSetMap[&_aggr_id1]=&waggr_id1;
    predicateUSetMap[&_aggr_id1]=&uaggr_id1;
    predicateFSetMap[&_aggr_id1]=&faggr_id1;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    predicateWSetMap[&_location]=&wlocation;
    predicateUSetMap[&_location]=&ulocation;
    predicateFSetMap[&_location]=&flocation;
    stringToUniqueStringPointer["location"] = &_location;
    predicateWSetMap[&_max_total_weight]=&wmax_total_weight;
    predicateUSetMap[&_max_total_weight]=&umax_total_weight;
    predicateFSetMap[&_max_total_weight]=&fmax_total_weight;
    stringToUniqueStringPointer["max_total_weight"] = &_max_total_weight;
    predicateWSetMap[&_leafPos]=&wleafPos;
    predicateUSetMap[&_leafPos]=&uleafPos;
    predicateFSetMap[&_leafPos]=&fleafPos;
    stringToUniqueStringPointer["leafPos"] = &_leafPos;
    predicateWSetMap[&_scost]=&wscost;
    predicateUSetMap[&_scost]=&uscost;
    predicateFSetMap[&_scost]=&fscost;
    stringToUniqueStringPointer["scost"] = &_scost;
    predicateToAuxiliaryMaps[&_leafPos].push_back(&pleafPos_1_);
    predicateToAuxiliaryMaps[&_scost].push_back(&pscost_);
    predicateToAuxiliaryMaps[&_location].push_back(&plocation_);
    predicateToAuxiliaryMaps[&_aggr_id1].push_back(&paggr_id1_);
    predicateToAuxiliaryMaps[&_aggr_id1].push_back(&paggr_id1_0_);
    predicateToAuxiliaryMaps[&_max_total_weight].push_back(&pmax_total_weight_);
    predicateToAuxiliaryMaps[&_aggr_id0].push_back(&paggr_id0_);
    predicateToUndefAuxiliaryMaps[&_leafPos].push_back(&uleafPos_1_);
    predicateToUndefAuxiliaryMaps[&_scost].push_back(&uscost_);
    predicateToUndefAuxiliaryMaps[&_location].push_back(&ulocation_);
    predicateToUndefAuxiliaryMaps[&_aggr_id1].push_back(&uaggr_id1_);
    predicateToUndefAuxiliaryMaps[&_aggr_id1].push_back(&uaggr_id1_0_);
    predicateToUndefAuxiliaryMaps[&_max_total_weight].push_back(&umax_total_weight_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0].push_back(&uaggr_id0_);
    predicateToFalseAuxiliaryMaps[&_leafPos].push_back(&fleafPos_1_);
    predicateToFalseAuxiliaryMaps[&_scost].push_back(&fscost_);
    predicateToFalseAuxiliaryMaps[&_location].push_back(&flocation_);
    predicateToFalseAuxiliaryMaps[&_aggr_id1].push_back(&faggr_id1_);
    predicateToFalseAuxiliaryMaps[&_aggr_id1].push_back(&faggr_id1_0_);
    predicateToFalseAuxiliaryMaps[&_max_total_weight].push_back(&fmax_total_weight_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0].push_back(&faggr_id0_);
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
                    if(tupleU->getPredicateName() == &_scost){
                        {
                            const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
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
                undefSet->second->erase(*tupleU);
                const auto& insertResult = falseSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[falseSet->first]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    if(tupleU->getPredicateName() == &_scost){
                        {
                            const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
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
        if(!propagatedLiterals.contains(-it*sign)){
            propagatedLiterals.insert(it*sign);
        }
    }
    return false;
}
void Executor::printInternalLiterals(const std::unordered_map<int,string>& answerSet){
    for(const auto& pair : answerSet) onLiteralTrue(pair.first,pair.second);
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
            if(tuple->getPredicateName() == &_scost){
                {
                    const std::vector<const Tuple*>* aggrIds = &paggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i)->getId();
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<const Tuple*>* aggrIds = &uaggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i)->getId();
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<const Tuple*>* aggrIds = &faggr_id0_.getValues({});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i)->getId();
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
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
        {
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int M = tuples->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &pscost_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uscost_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < M+1){
                    std::cout<<"Conflitct on aggregate starting from true aggr id "<<std::endl;
                    propagatedLiterals.insert(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= M+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &fscost_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int M = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &pscost_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uscost_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(actualSum[aggrIdIt] >= M+1){
                    std::cout<<"Conflitct on aggregate starting from false aggr id "<<actualSum[aggrIdIt]<<std::endl;
                    propagatedLiterals.insert(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= M+1){
                            int itProp = joinTuplesU->at(index)->getId();
                            if(reasonForLiteral.count(-itProp) == 0 ){
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i)->getId();
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    int it = tuplesF->at(i)->getId();
                                    reason.push_back(-it);
                                    reasonForLiteral[-itProp].insert(-it);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int M = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &pscost_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uscost_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(actualSum[aggrIdIt] >= M+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < M+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &fscost_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int P = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &pleafPos_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uleafPos_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 2){
                    std::cout<<"Conflitct on aggregate starting from true aggr id "<<std::endl;
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 2){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &fleafPos_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int P = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &pleafPos_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uleafPos_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 2){
                    std::cout<<"Conflitct on aggregate starting from false aggr id "<<actualSum[aggrIdIt]<<std::endl;
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 2 -1){
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int P = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &pleafPos_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uleafPos_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &fleafPos_1_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &plocation_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ulocation_.getValues({});
                else if(tupleU->getPredicateName() == &_location && !tupleUNegated)
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
                        Tuple* positiveTuple = factory.addNewInternalTuple({P},&_aggr_id1);
                        const Tuple* tuple1 = waggr_id1.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaggr_id1.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id1 && ! tupleUNegated){
                            if(tupleU == uaggr_id1.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &pmax_total_weight_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &umax_total_weight_.getValues({});
                else if(tupleU->getPredicateName() == &_max_total_weight && !tupleUNegated)
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
                        int M = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({M},&_aggr_id0);
                        const Tuple* tuple1 = waggr_id0.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaggr_id0.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0 && ! tupleUNegated){
                            if(tupleU == uaggr_id0.find(*positiveTuple)){
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
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        starter.setNegated(startVar<0);
        std::string minus = starter.isNegated() ? "not " : "";
        propagationStack.pop_back();
        if(starter.getPredicateName() == &_aggr_id0){
            int M = starter[0];
            std::vector<int> sharedVar({});
            const std::vector<const Tuple*>* tuples = &pscost_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uscost_.getValues(sharedVar);
            if(starter.isNegated()){
                if(actualSum[uStartVar]>=M+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index =0; index<tuplesU->size(); index++){
                        if(actualSum[uStartVar]+tuplesU->at(index)->at(0) >= M+1){
                            int itProp = tuplesU->at(index)->getId();
                            if(reasonForLiteral.count(-itProp)==0){
                                if(reason.empty()){
                                    for(unsigned i =0; i< tuples->size(); i++){
                                        int it = tuples->at(i)->getId();
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    reason.push_back(startVar);
                                    reasonForLiteral[-itProp].insert(startVar);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(tuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < M+1){
                    const std::vector<const Tuple*>* tuplesF = &fscost_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();index++){
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at(0) < M+1){
                            int itProp = tuplesU->at(index)->getId();
                            if(reasonForLiteral.count(itProp) == 0){
                                const std::vector<const Tuple*>* tuplesF = &fscost_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i)->getId();
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_scost){
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int M = tuples->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &pscost_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uscost_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < M+1){
                    std::cout<<"Conflitct on aggregate starting from true aggr id "<<std::endl;
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &fscost_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= M+1) {index++; continue;}
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &fscost_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int M = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &pscost_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uscost_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(actualSum[aggrIdIt] >= M+1){
                    std::cout<<"Conflitct on aggregate starting from false aggr id "<<actualSum[aggrIdIt]<<std::endl;
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= M+1){
                            int itProp = joinTuplesU->at(index)->getId();
                            if(reasonForLiteral.count(-itProp) == 0 ){
                                if(reason.empty()){
                                    for(unsigned i =0; i< joinTuples->size(); i++){
                                        int it = joinTuples->at(i)->getId();
                                        reason.push_back(it);
                                        reasonForLiteral[-itProp].insert(it);
                                    }
                                    int it = tuplesF->at(i)->getId();
                                    reason.push_back(-it);
                                    reasonForLiteral[-itProp].insert(-it);
                                }else{
                                    for(int reasonLit : reason)
                                        reasonForLiteral[-itProp].insert(reasonLit);
                                }
                            }
                            propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int M = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({});
                const std::vector<const Tuple*>* joinTuples = &pscost_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uscost_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(actualSum[aggrIdIt] >= M+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < M+1){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &fscost_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id0 && !starter.isNegated()){
                int M = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({M},&_max_total_weight);
                const Tuple* tuple1 = wmax_total_weight.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = umax_total_weight.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_max_total_weight && ! tupleUNegated){
                    if(tupleU == umax_total_weight.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{std::cout<<"Reason already computed"<<std::endl;}
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_max_total_weight && !starter.isNegated()){
                int M = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({M},&_aggr_id0);
                const Tuple* tuple1 = waggr_id0.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_id0.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id0 && ! tupleUNegated){
                    if(tupleU == uaggr_id0.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{std::cout<<"Reason already computed"<<std::endl;}
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id1){
            int P = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<const Tuple*>* tuples = &pleafPos_1_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uleafPos_1_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=2){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 2 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    for(unsigned i =0; i<tuplesU->size(); i++){
                        int itProp = tuplesU->at(i)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 2){
                    const std::vector<const Tuple*>* tuplesF = &fleafPos_1_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 2){
                    for(unsigned index=0;index<tuplesU->size();index++){
                        int itProp = tuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &fleafPos_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_leafPos){
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int P = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &pleafPos_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uleafPos_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 2){
                    std::cout<<"Conflitct on aggregate starting from true aggr id "<<std::endl;
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &fleafPos_1_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 2){
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &fleafPos_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int P = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &pleafPos_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uleafPos_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 2){
                    std::cout<<"Conflitct on aggregate starting from false aggr id "<<actualSum[aggrIdIt]<<std::endl;
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 2 -1){
                    std::vector<int> reason;
                    for(unsigned index=0; index<joinTuplesU->size(); index++){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(-itProp) == 0 ){
                            if(reason.empty()){
                                for(unsigned i =0; i< joinTuples->size(); i++){
                                    int it = joinTuples->at(i)->getId();
                                    reason.push_back(it);
                                    reasonForLiteral[-itProp].insert(it);
                                }
                                int it = tuplesF->at(i)->getId();
                                reason.push_back(-it);
                                reasonForLiteral[-itProp].insert(-it);
                            }else{
                                for(int reasonLit : reason)
                                    reasonForLiteral[-itProp].insert(reasonLit);
                            }
                        }
                        propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int P = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &pleafPos_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uleafPos_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 2){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &fleafPos_1_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            int it = joinTuplesF->at(j)->getId();
                            reasonForLiteral[-itProp].insert(-it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);
                }else{
                    i++;
                }
            }//close undef for
        }//close aggr set starter
        {
            if(starter.getPredicateName() == &_aggr_id1 && !starter.isNegated()){
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({P},&_location);
                const Tuple* tuple1 = wlocation.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ulocation.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_location && ! tupleUNegated){
                    if(tupleU == ulocation.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{std::cout<<"Reason already computed"<<std::endl;}
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
            if(starter.getPredicateName() == &_location && !starter.isNegated()){
                int P = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({P},&_aggr_id1);
                const Tuple* tuple1 = waggr_id1.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_id1.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id1 && ! tupleUNegated){
                    if(tupleU == uaggr_id1.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    if(tupleU != NULL){
                        int itUndef = tupleU->getId();
                        int var = tupleUNegated ? 1 : -1;
                        var*=itUndef;
                        if(reasonForLiteral.count(var) == 0){
                            {
                                int it = starter.getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{std::cout<<"Reason already computed"<<std::endl;}
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*1);
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
