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
PredicateWSet waggr_id0(2);
PredicateWSet uaggr_id0(2);
PredicateWSet faggr_id0(2);
const std::string _aggr_id1 = "aggr_id1";
PredicateWSet waggr_id1(2);
PredicateWSet uaggr_id1(2);
PredicateWSet faggr_id1(2);
const std::string _aggr_id2 = "aggr_id2";
PredicateWSet waggr_id2(2);
PredicateWSet uaggr_id2(2);
PredicateWSet faggr_id2(2);
const std::string _aggr_id3 = "aggr_id3";
PredicateWSet waggr_id3(2);
PredicateWSet uaggr_id3(2);
PredicateWSet faggr_id3(2);
const std::string _aggr_set0 = "aggr_set0";
PredicateWSet waggr_set0(2);
PredicateWSet uaggr_set0(2);
PredicateWSet faggr_set0(2);
const std::string _aggr_set1 = "aggr_set1";
PredicateWSet waggr_set1(2);
PredicateWSet uaggr_set1(2);
PredicateWSet faggr_set1(2);
const std::string _aux0 = "aux0";
PredicateWSet waux0(2);
PredicateWSet uaux0(2);
PredicateWSet faux0(2);
const std::string _aux1 = "aux1";
PredicateWSet waux1(2);
PredicateWSet uaux1(2);
PredicateWSet faux1(2);
const std::string _aux2 = "aux2";
PredicateWSet waux2(2);
PredicateWSet uaux2(2);
PredicateWSet faux2(2);
const std::string _aux3 = "aux3";
PredicateWSet waux3(2);
PredicateWSet uaux3(2);
PredicateWSet faux3(2);
const std::string _body0 = "body0";
PredicateWSet wbody0(2);
PredicateWSet ubody0(2);
PredicateWSet fbody0(2);
const std::string _body1 = "body1";
PredicateWSet wbody1(2);
PredicateWSet ubody1(2);
PredicateWSet fbody1(2);
const std::string _filled = "filled";
PredicateWSet wfilled(2);
PredicateWSet ufilled(2);
PredicateWSet ffilled(2);
const std::string _xvalue = "xvalue";
PredicateWSet wxvalue(2);
PredicateWSet uxvalue(2);
PredicateWSet fxvalue(2);
const std::string _yvalue = "yvalue";
PredicateWSet wyvalue(2);
PredicateWSet uyvalue(2);
PredicateWSet fyvalue(2);
std::map<int,int> externalLiteralsLevel;
std::map<int,std::vector<int>> levelToIntLiterals;
std::map<int,std::vector<int>> levelToExtLiterals;
std::map<int,UnorderedSet<int>> reasonForLiteral;
int currentDecisionLevel=-1;
std::unordered_map<int,int> supportedLiterals;
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
AuxMap pyvalue_({});
AuxMap uyvalue_({});
AuxMap fyvalue_({});
AuxMap pxvalue_({});
AuxMap uxvalue_({});
AuxMap fxvalue_({});
AuxMap pfilled_({});
AuxMap ufilled_({});
AuxMap ffilled_({});
AuxMap paggr_set0_({});
AuxMap uaggr_set0_({});
AuxMap faggr_set0_({});
AuxMap paux0_({});
AuxMap uaux0_({});
AuxMap faux0_({});
AuxMap pbody0_({});
AuxMap ubody0_({});
AuxMap fbody0_({});
AuxMap paux1_({});
AuxMap uaux1_({});
AuxMap faux1_({});
AuxMap paggr_id0_({});
AuxMap uaggr_id0_({});
AuxMap faggr_id0_({});
AuxMap paggr_set0_0_({0});
AuxMap uaggr_set0_0_({0});
AuxMap faggr_set0_0_({0});
AuxMap paggr_id1_({});
AuxMap uaggr_id1_({});
AuxMap faggr_id1_({});
AuxMap paggr_set0_0_0_({0,0});
AuxMap uaggr_set0_0_0_({0,0});
AuxMap faggr_set0_0_0_({0,0});
AuxMap paggr_set1_({});
AuxMap uaggr_set1_({});
AuxMap faggr_set1_({});
AuxMap paux2_({});
AuxMap uaux2_({});
AuxMap faux2_({});
AuxMap pbody1_({});
AuxMap ubody1_({});
AuxMap fbody1_({});
AuxMap paux3_({});
AuxMap uaux3_({});
AuxMap faux3_({});
AuxMap paggr_id2_({});
AuxMap uaggr_id2_({});
AuxMap faggr_id2_({});
AuxMap paggr_set1_0_({0});
AuxMap uaggr_set1_0_({0});
AuxMap faggr_set1_0_({0});
AuxMap paggr_id3_({});
AuxMap uaggr_id3_({});
AuxMap faggr_id3_({});
AuxMap paggr_set1_0_0_({0,0});
AuxMap uaggr_set1_0_0_({0,0});
AuxMap faggr_set1_0_0_({0,0});
//printing aux maps needed for reasons of negative literals;
void Executor::handleConflict(int literal){
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
    int currentLit=0;
    while(!stack.empty()){
        int lit = stack.back();
        stack.pop_back();
        for(unsigned i = 0; i<reasonForLiteral[lit].size(); i++){
            int reasonLiteral=reasonForLiteral[lit][i];
            if(getExternalLit){
                if(externalLiteralsLevel.count(reasonLiteral)!=0){
                    if(externalLiteralsLevel[reasonLiteral] == currentDecisionLevel)
                        currentLit = reasonLiteral;
                }
            }
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
    for(unsigned i=0; i<reas.size(); i++){
        Tuple t = reas[i]>0 ? atomsTable[reas[i]] : atomsTable[-reas[i]];
    }
    return currentLit;
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
    if(!propagatedLiterals.empty()){
        propagatedLiterals.clear();
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
}
void Executor::undefLiteralsReceived()const{
    if(undefinedLoaded)
        return;
    undefinedLoaded=true;
    {//Generating aux3
        const std::vector<const Tuple*>* tuples = &pyvalue_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uyvalue_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int X = tuple0->at(0);
            int V = tuple0->at(1);
            Tuple aux({X,V}, &_aux3);
            if(uaux3.find(aux) == NULL){
                const auto& insertResult = uaux3.insert(Tuple({X,V},&_aux3));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux3]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(aux);
                    tupleToVar[aux]=atomsTable.size()-1;
                }
            }
        }
    }//closing aux generation
    {
        const std::vector<const Tuple*>* tuples = &paux3_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uaux3_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int X = tuple0->at(0);
            int V = tuple0->at(1);
            if(undef0){
                Tuple head({X,V},&_body1);
                const auto& insertResult = ubody1.insert(Tuple({X,V},&_body1));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_body1]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(head);
                    tupleToVar[head]=atomsTable.size()-1;
                    {
                        Tuple aggrId({X,V},&_aggr_id2);
                        const auto& insertResult = uaggr_id2.insert(Tuple({X,V},&_aggr_id2));
                        if (insertResult.second) {
                            for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id2]) {
                                auxMap -> insert2(*insertResult.first);
                            }
                            atomsTable.push_back(aggrId);
                            tupleToVar[aggrId]=atomsTable.size()-1;
                        }
                    }
                    {
                        Tuple aggrId({X,V},&_aggr_id3);
                        const auto& insertResult = uaggr_id3.insert(Tuple({X,V},&_aggr_id3));
                        if (insertResult.second) {
                            for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id3]) {
                                auxMap -> insert2(*insertResult.first);
                            }
                            atomsTable.push_back(aggrId);
                            tupleToVar[aggrId]=atomsTable.size()-1;
                        }
                    }
                }
            }
        }
    }
    {//Generating aux1
        const std::vector<const Tuple*>* tuples = &pxvalue_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uxvalue_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int Y = tuple0->at(0);
            int V = tuple0->at(1);
            Tuple aux({Y,V}, &_aux1);
            if(uaux1.find(aux) == NULL){
                const auto& insertResult = uaux1.insert(Tuple({Y,V},&_aux1));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux1]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(aux);
                    tupleToVar[aux]=atomsTable.size()-1;
                }
            }
        }
    }//closing aux generation
    {
        const std::vector<const Tuple*>* tuples = &paux1_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uaux1_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int Y = tuple0->at(0);
            int V = tuple0->at(1);
            if(undef0){
                Tuple head({Y,V},&_body0);
                const auto& insertResult = ubody0.insert(Tuple({Y,V},&_body0));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_body0]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(head);
                    tupleToVar[head]=atomsTable.size()-1;
                    {
                        Tuple aggrId({Y,V},&_aggr_id0);
                        const auto& insertResult = uaggr_id0.insert(Tuple({Y,V},&_aggr_id0));
                        if (insertResult.second) {
                            for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id0]) {
                                auxMap -> insert2(*insertResult.first);
                            }
                            atomsTable.push_back(aggrId);
                            tupleToVar[aggrId]=atomsTable.size()-1;
                        }
                    }
                    {
                        Tuple aggrId({Y,V},&_aggr_id1);
                        const auto& insertResult = uaggr_id1.insert(Tuple({Y,V},&_aggr_id1));
                        if (insertResult.second) {
                            for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id1]) {
                                auxMap -> insert2(*insertResult.first);
                            }
                            atomsTable.push_back(aggrId);
                            tupleToVar[aggrId]=atomsTable.size()-1;
                        }
                    }
                }
            }
        }
    }
    {//Generating aux2
        const std::vector<const Tuple*>* tuples = &pfilled_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ufilled_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int X = tuple0->at(0);
            int Y = tuple0->at(1);
            Tuple aux({X,Y}, &_aux2);
            if(uaux2.find(aux) == NULL){
                const auto& insertResult = uaux2.insert(Tuple({X,Y},&_aux2));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux2]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(aux);
                    tupleToVar[aux]=atomsTable.size()-1;
                }
            }
        }
    }//closing aux generation
    {
        const std::vector<const Tuple*>* tuples = &paux2_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uaux2_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int X = tuple0->at(0);
            int Y = tuple0->at(1);
            if(undef0){
                Tuple head({X,Y},&_aggr_set1);
                const auto& insertResult = uaggr_set1.insert(Tuple({X,Y},&_aggr_set1));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set1]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(head);
                    tupleToVar[head]=atomsTable.size()-1;
                }
            }
        }
    }
    {//Generating aux0
        const std::vector<const Tuple*>* tuples = &pfilled_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ufilled_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int X = tuple0->at(0);
            int Y = tuple0->at(1);
            Tuple aux({Y,X}, &_aux0);
            if(uaux0.find(aux) == NULL){
                const auto& insertResult = uaux0.insert(Tuple({Y,X},&_aux0));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aux0]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(aux);
                    tupleToVar[aux]=atomsTable.size()-1;
                }
            }
        }
    }//closing aux generation
    {
        const std::vector<const Tuple*>* tuples = &paux0_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uaux0_.getValues({});
        bool undef0=false;
        for(int i=0;i<tuples->size()+tuplesU->size();i++){
            const Tuple* tuple0=NULL;
            if(i<tuples->size()){
                tuple0=tuples->at(i);
            }else{
                tuple0=tuplesU->at(i-tuples->size());
                undef0=true;
            }
            int Y = tuple0->at(0);
            int X = tuple0->at(1);
            if(undef0){
                Tuple head({Y,X},&_aggr_set0);
                const auto& insertResult = uaggr_set0.insert(Tuple({Y,X},&_aggr_set0));
                if (insertResult.second) {
                    for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set0]) {
                        auxMap -> insert2(*insertResult.first);
                    }
                    atomsTable.push_back(head);
                    tupleToVar[head]=atomsTable.size()-1;
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
    waggr_id0.clear();
    waggr_id1.clear();
    waggr_id2.clear();
    waggr_id3.clear();
    waggr_set0.clear();
    waggr_set1.clear();
    wbody0.clear();
    wbody1.clear();
    paggr_id2_.clear();
    paggr_id3_.clear();
    paggr_set0_.clear();
    paggr_set0_0_.clear();
    paggr_set0_0_0_.clear();
    pbody0_.clear();
    paggr_id1_.clear();
    paggr_id0_.clear();
    paggr_set1_.clear();
    paggr_set1_0_.clear();
    paggr_set1_0_0_.clear();
    pbody1_.clear();
    faggr_id2_.clear();
    faggr_id3_.clear();
    faggr_set0_.clear();
    faggr_set0_0_.clear();
    faggr_set0_0_0_.clear();
    fbody0_.clear();
    faggr_id1_.clear();
    faggr_id0_.clear();
    faggr_set1_.clear();
    faggr_set1_0_.clear();
    faggr_set1_0_0_.clear();
    fbody1_.clear();
}
void Executor::init() {
    std::cout<<"Init"<<std::endl;
    predicateWSetMap[&_aggr_id0]=&waggr_id0;
    predicateUSetMap[&_aggr_id0]=&uaggr_id0;
    predicateFSetMap[&_aggr_id0]=&faggr_id0;
    stringToUniqueStringPointer["aggr_id0"] = &_aggr_id0;
    predicateWSetMap[&_aggr_id1]=&waggr_id1;
    predicateUSetMap[&_aggr_id1]=&uaggr_id1;
    predicateFSetMap[&_aggr_id1]=&faggr_id1;
    stringToUniqueStringPointer["aggr_id1"] = &_aggr_id1;
    predicateWSetMap[&_aggr_id2]=&waggr_id2;
    predicateUSetMap[&_aggr_id2]=&uaggr_id2;
    predicateFSetMap[&_aggr_id2]=&faggr_id2;
    stringToUniqueStringPointer["aggr_id2"] = &_aggr_id2;
    predicateWSetMap[&_aggr_id3]=&waggr_id3;
    predicateUSetMap[&_aggr_id3]=&uaggr_id3;
    predicateFSetMap[&_aggr_id3]=&faggr_id3;
    stringToUniqueStringPointer["aggr_id3"] = &_aggr_id3;
    predicateWSetMap[&_aggr_set0]=&waggr_set0;
    predicateUSetMap[&_aggr_set0]=&uaggr_set0;
    predicateFSetMap[&_aggr_set0]=&faggr_set0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    predicateWSetMap[&_aggr_set1]=&waggr_set1;
    predicateUSetMap[&_aggr_set1]=&uaggr_set1;
    predicateFSetMap[&_aggr_set1]=&faggr_set1;
    stringToUniqueStringPointer["aggr_set1"] = &_aggr_set1;
    predicateWSetMap[&_aux0]=&waux0;
    predicateUSetMap[&_aux0]=&uaux0;
    predicateFSetMap[&_aux0]=&faux0;
    stringToUniqueStringPointer["aux0"] = &_aux0;
    predicateWSetMap[&_aux1]=&waux1;
    predicateUSetMap[&_aux1]=&uaux1;
    predicateFSetMap[&_aux1]=&faux1;
    stringToUniqueStringPointer["aux1"] = &_aux1;
    predicateWSetMap[&_aux2]=&waux2;
    predicateUSetMap[&_aux2]=&uaux2;
    predicateFSetMap[&_aux2]=&faux2;
    stringToUniqueStringPointer["aux2"] = &_aux2;
    predicateWSetMap[&_aux3]=&waux3;
    predicateUSetMap[&_aux3]=&uaux3;
    predicateFSetMap[&_aux3]=&faux3;
    stringToUniqueStringPointer["aux3"] = &_aux3;
    predicateWSetMap[&_body0]=&wbody0;
    predicateUSetMap[&_body0]=&ubody0;
    predicateFSetMap[&_body0]=&fbody0;
    stringToUniqueStringPointer["body0"] = &_body0;
    predicateWSetMap[&_body1]=&wbody1;
    predicateUSetMap[&_body1]=&ubody1;
    predicateFSetMap[&_body1]=&fbody1;
    stringToUniqueStringPointer["body1"] = &_body1;
    predicateWSetMap[&_filled]=&wfilled;
    predicateUSetMap[&_filled]=&ufilled;
    predicateFSetMap[&_filled]=&ffilled;
    stringToUniqueStringPointer["filled"] = &_filled;
    predicateWSetMap[&_xvalue]=&wxvalue;
    predicateUSetMap[&_xvalue]=&uxvalue;
    predicateFSetMap[&_xvalue]=&fxvalue;
    stringToUniqueStringPointer["xvalue"] = &_xvalue;
    predicateWSetMap[&_yvalue]=&wyvalue;
    predicateUSetMap[&_yvalue]=&uyvalue;
    predicateFSetMap[&_yvalue]=&fyvalue;
    stringToUniqueStringPointer["yvalue"] = &_yvalue;
    predicateToAuxiliaryMaps[&_aggr_id2].push_back(&paggr_id2_);
    predicateToAuxiliaryMaps[&_yvalue].push_back(&pyvalue_);
    predicateToAuxiliaryMaps[&_aggr_id3].push_back(&paggr_id3_);
    predicateToAuxiliaryMaps[&_aux3].push_back(&paux3_);
    predicateToAuxiliaryMaps[&_xvalue].push_back(&pxvalue_);
    predicateToAuxiliaryMaps[&_filled].push_back(&pfilled_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_0_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_0_0_);
    predicateToAuxiliaryMaps[&_aux0].push_back(&paux0_);
    predicateToAuxiliaryMaps[&_aux2].push_back(&paux2_);
    predicateToAuxiliaryMaps[&_body0].push_back(&pbody0_);
    predicateToAuxiliaryMaps[&_aux1].push_back(&paux1_);
    predicateToAuxiliaryMaps[&_aggr_id1].push_back(&paggr_id1_);
    predicateToAuxiliaryMaps[&_aggr_id0].push_back(&paggr_id0_);
    predicateToAuxiliaryMaps[&_aggr_set1].push_back(&paggr_set1_);
    predicateToAuxiliaryMaps[&_aggr_set1].push_back(&paggr_set1_0_);
    predicateToAuxiliaryMaps[&_aggr_set1].push_back(&paggr_set1_0_0_);
    predicateToAuxiliaryMaps[&_body1].push_back(&pbody1_);
    predicateToUndefAuxiliaryMaps[&_aggr_id2].push_back(&uaggr_id2_);
    predicateToUndefAuxiliaryMaps[&_yvalue].push_back(&uyvalue_);
    predicateToUndefAuxiliaryMaps[&_aggr_id3].push_back(&uaggr_id3_);
    predicateToUndefAuxiliaryMaps[&_aux3].push_back(&uaux3_);
    predicateToUndefAuxiliaryMaps[&_xvalue].push_back(&uxvalue_);
    predicateToUndefAuxiliaryMaps[&_filled].push_back(&ufilled_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_0_0_);
    predicateToUndefAuxiliaryMaps[&_aux0].push_back(&uaux0_);
    predicateToUndefAuxiliaryMaps[&_aux2].push_back(&uaux2_);
    predicateToUndefAuxiliaryMaps[&_body0].push_back(&ubody0_);
    predicateToUndefAuxiliaryMaps[&_aux1].push_back(&uaux1_);
    predicateToUndefAuxiliaryMaps[&_aggr_id1].push_back(&uaggr_id1_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0].push_back(&uaggr_id0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set1].push_back(&uaggr_set1_);
    predicateToUndefAuxiliaryMaps[&_aggr_set1].push_back(&uaggr_set1_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set1].push_back(&uaggr_set1_0_0_);
    predicateToUndefAuxiliaryMaps[&_body1].push_back(&ubody1_);
    predicateToFalseAuxiliaryMaps[&_aggr_id2].push_back(&faggr_id2_);
    predicateToFalseAuxiliaryMaps[&_yvalue].push_back(&fyvalue_);
    predicateToFalseAuxiliaryMaps[&_aggr_id3].push_back(&faggr_id3_);
    predicateToFalseAuxiliaryMaps[&_aux3].push_back(&faux3_);
    predicateToFalseAuxiliaryMaps[&_xvalue].push_back(&fxvalue_);
    predicateToFalseAuxiliaryMaps[&_filled].push_back(&ffilled_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_0_0_);
    predicateToFalseAuxiliaryMaps[&_aux0].push_back(&faux0_);
    predicateToFalseAuxiliaryMaps[&_aux2].push_back(&faux2_);
    predicateToFalseAuxiliaryMaps[&_body0].push_back(&fbody0_);
    predicateToFalseAuxiliaryMaps[&_aux1].push_back(&faux1_);
    predicateToFalseAuxiliaryMaps[&_aggr_id1].push_back(&faggr_id1_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0].push_back(&faggr_id0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set1].push_back(&faggr_set1_);
    predicateToFalseAuxiliaryMaps[&_aggr_set1].push_back(&faggr_set1_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set1].push_back(&faggr_set1_0_0_);
    predicateToFalseAuxiliaryMaps[&_body1].push_back(&fbody1_);
}
bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){
    if(tupleU->getPredicateName() == &_aggr_id2 || tupleU->getPredicateName() == &_aggr_set0 || tupleU->getPredicateName() == &_aux0 || tupleU->getPredicateName() == &_aux2 || tupleU->getPredicateName() == &_body0 || tupleU->getPredicateName() == &_aux1 || tupleU->getPredicateName() == &_aggr_id1 || tupleU->getPredicateName() == &_aggr_id3 || tupleU->getPredicateName() == &_aux3 || tupleU->getPredicateName() == &_aggr_id0 || tupleU->getPredicateName() == &_aggr_set1 || tupleU->getPredicateName() == &_body1){
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
    while(currentDecisionLevel > decisionLevel){
        levelToExtLiterals.erase(currentDecisionLevel);
        while(!levelToIntLiterals[currentDecisionLevel].empty()){
            int var = levelToIntLiterals[currentDecisionLevel].back();
            levelToIntLiterals[currentDecisionLevel].pop_back();
            reasonForLiteral.erase(var);
            if(supportedLiterals[var] >= currentDecisionLevel)
                supportedLiterals.erase(var);
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
        levelToExtLiterals[currentDecisionLevel].push_back(facts[i]);
    }
    if(decisionLevel==-1) {
        if(!undefinedLoaded)
            undefLiteralsReceived();
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pbody1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_.getValues({});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        Tuple negativeTuple({X,V},&_aggr_id3);
                        const Tuple* tuple1 = waggr_id3.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaggr_id3.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id3 && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &pbody1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody1_.getValues({});
                else if(tupleU->getPredicateName() == &_body1 && !tupleUNegated)
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
                        Tuple positiveTuple({X,V},&_aggr_id2);
                        const Tuple* tuple1 = waggr_id2.find(positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaggr_id2.find(positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                            if(tupleU == uaggr_id2.find(positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &pyvalue_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uyvalue_.getValues({});
                else if(tupleU->getPredicateName() == &_yvalue && !tupleUNegated)
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
                        Tuple negativeTuple({X,V},&_aux3);
                        const Tuple* tuple1 = waux3.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaux3.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux3 && tupleUNegated && tupleU==tupleUndef1){
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
                        Tuple negativeTuple({X,V},&_yvalue);
                        const Tuple* tuple1 = wyvalue.find(negativeTuple);
                        const Tuple* tupleUndef1 = uyvalue.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_yvalue && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &pfilled_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ufilled_.getValues({});
                else if(tupleU->getPredicateName() == &_filled && !tupleUNegated)
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
                        int Y = tuple0->at(1);
                        Tuple negativeTuple({X,Y},&_aux2);
                        const Tuple* tuple1 = waux2.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaux2.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux2 && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paux2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux2_.getValues({});
                else if(tupleU->getPredicateName() == &_aux2 && !tupleUNegated)
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
                        int Y = tuple0->at(1);
                        Tuple negativeTuple({X,Y},&_filled);
                        const Tuple* tuple1 = wfilled.find(negativeTuple);
                        const Tuple* tupleUndef1 = ufilled.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_filled && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &pbody0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValues({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        int Y = tuple0->at(0);
                        int V = tuple0->at(1);
                        Tuple negativeTuple({Y,V},&_aggr_id1);
                        const Tuple* tuple1 = waggr_id1.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaggr_id1.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id1 && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &pbody0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ubody0_.getValues({});
                else if(tupleU->getPredicateName() == &_body0 && !tupleUNegated)
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
                        int Y = tuple0->at(0);
                        int V = tuple0->at(1);
                        Tuple positiveTuple({Y,V},&_aggr_id0);
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
                const std::vector<const Tuple*>* tuples = &pxvalue_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uxvalue_.getValues({});
                else if(tupleU->getPredicateName() == &_xvalue && !tupleUNegated)
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
                        int Y = tuple0->at(0);
                        int V = tuple0->at(1);
                        Tuple negativeTuple({Y,V},&_aux1);
                        const Tuple* tuple1 = waux1.find(negativeTuple);
                        const Tuple* tupleUndef1 = uaux1.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux1 && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paux1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaux1_.getValues({});
                else if(tupleU->getPredicateName() == &_aux1 && !tupleUNegated)
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
                        int Y = tuple0->at(0);
                        int V = tuple0->at(1);
                        Tuple negativeTuple({Y,V},&_xvalue);
                        const Tuple* tuple1 = wxvalue.find(negativeTuple);
                        const Tuple* tupleUndef1 = uxvalue.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_xvalue && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &pfilled_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ufilled_.getValues({});
                else if(tupleU->getPredicateName() == &_filled && !tupleUNegated)
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
                        int Y = tuple0->at(1);
                        Tuple negativeTuple({Y,X},&_aux0);
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
                        int Y = tuple0->at(0);
                        int X = tuple0->at(1);
                        Tuple negativeTuple({X,Y},&_filled);
                        const Tuple* tuple1 = wfilled.find(negativeTuple);
                        const Tuple* tupleUndef1 = ufilled.find(negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = &negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_filled && tupleUNegated && tupleU==tupleUndef1){
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
                int Y = head->at(0);
                int X = head->at(1);
                const Tuple* tuple = waux0.find(Tuple({Y,X},&_aux0));
                const Tuple* tupleU = uaux0.find(Tuple({Y,X},&_aux0));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propagatedLiterals.insert(-1);
                    }else{
                        propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        const auto & it = tupleToVar.find(*head);
                        if(it != tupleToVar.end()){
                            supportedLiterals[it->second]=currentDecisionLevel;
                        }
                    }
                }else{
                    const auto & it = tupleToVar.find(*head);
                    if(it != tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* undefHeads = &uaggr_set0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = undefHeads->at(i);
                int Y = head->at(0);
                int X = head->at(1);
                const Tuple* tuple = waux0.find(Tuple({Y,X},&_aux0));
                const Tuple* tupleU = uaux0.find(Tuple({Y,X},&_aux0));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals);
                    const auto& it = tupleToVar.find(*head);
                    if(it!=tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* falseHeads = &faggr_set0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = falseHeads->at(i);
                int Y = head->at(0);
                int X = head->at(1);
                const Tuple* tuple = waux0.find(Tuple({Y,X},&_aux0));
                const Tuple* tupleU = uaux0.find(Tuple({Y,X},&_aux0));
                if(tuple == NULL){
                    if(tupleU != NULL){
                        propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propagatedLiterals.insert(-1);
                }
            }
        }
        {
            const std::vector<const Tuple*>* trueHeads = &pbody0_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = trueHeads->at(i);
                int Y = head->at(0);
                int V = head->at(1);
                const Tuple* tuple = waux1.find(Tuple({Y,V},&_aux1));
                const Tuple* tupleU = uaux1.find(Tuple({Y,V},&_aux1));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propagatedLiterals.insert(-1);
                    }else{
                        propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        const auto & it = tupleToVar.find(*head);
                        if(it != tupleToVar.end()){
                            supportedLiterals[it->second]=currentDecisionLevel;
                        }
                    }
                }else{
                    const auto & it = tupleToVar.find(*head);
                    if(it != tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* undefHeads = &ubody0_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = undefHeads->at(i);
                int Y = head->at(0);
                int V = head->at(1);
                const Tuple* tuple = waux1.find(Tuple({Y,V},&_aux1));
                const Tuple* tupleU = uaux1.find(Tuple({Y,V},&_aux1));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals);
                    const auto& it = tupleToVar.find(*head);
                    if(it!=tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* falseHeads = &fbody0_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = falseHeads->at(i);
                int Y = head->at(0);
                int V = head->at(1);
                const Tuple* tuple = waux1.find(Tuple({Y,V},&_aux1));
                const Tuple* tupleU = uaux1.find(Tuple({Y,V},&_aux1));
                if(tuple == NULL){
                    if(tupleU != NULL){
                        propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propagatedLiterals.insert(-1);
                }
            }
        }
        {
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == V+1){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
                int Y = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == V+1 -1){
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
                int Y = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V+1){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V+1){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == V){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
                int Y = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == V -1){
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
                int Y = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
            const std::vector<const Tuple*>* trueHeads = &paggr_set1_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = trueHeads->at(i);
                int X = head->at(0);
                int Y = head->at(1);
                const Tuple* tuple = waux2.find(Tuple({X,Y},&_aux2));
                const Tuple* tupleU = uaux2.find(Tuple({X,Y},&_aux2));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propagatedLiterals.insert(-1);
                    }else{
                        propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        const auto & it = tupleToVar.find(*head);
                        if(it != tupleToVar.end()){
                            supportedLiterals[it->second]=currentDecisionLevel;
                        }
                    }
                }else{
                    const auto & it = tupleToVar.find(*head);
                    if(it != tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* undefHeads = &uaggr_set1_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = undefHeads->at(i);
                int X = head->at(0);
                int Y = head->at(1);
                const Tuple* tuple = waux2.find(Tuple({X,Y},&_aux2));
                const Tuple* tupleU = uaux2.find(Tuple({X,Y},&_aux2));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals);
                    const auto& it = tupleToVar.find(*head);
                    if(it!=tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* falseHeads = &faggr_set1_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = falseHeads->at(i);
                int X = head->at(0);
                int Y = head->at(1);
                const Tuple* tuple = waux2.find(Tuple({X,Y},&_aux2));
                const Tuple* tupleU = uaux2.find(Tuple({X,Y},&_aux2));
                if(tuple == NULL){
                    if(tupleU != NULL){
                        propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propagatedLiterals.insert(-1);
                }
            }
        }
        {
            const std::vector<const Tuple*>* trueHeads = &pbody1_.getValues({});
            for(unsigned i = 0; i < trueHeads->size(); i++){
                const Tuple* head = trueHeads->at(i);
                int X = head->at(0);
                int V = head->at(1);
                const Tuple* tuple = waux3.find(Tuple({X,V},&_aux3));
                const Tuple* tupleU = uaux3.find(Tuple({X,V},&_aux3));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propagatedLiterals.insert(-1);
                    }else{
                        propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        const auto & it = tupleToVar.find(*head);
                        if(it != tupleToVar.end()){
                            supportedLiterals[it->second]=currentDecisionLevel;
                        }
                    }
                }else{
                    const auto & it = tupleToVar.find(*head);
                    if(it != tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* undefHeads = &ubody1_.getValues({});
            for(unsigned i = 0; i < undefHeads->size(); i++){
                const Tuple* head = undefHeads->at(i);
                int X = head->at(0);
                int V = head->at(1);
                const Tuple* tuple = waux3.find(Tuple({X,V},&_aux3));
                const Tuple* tupleU = uaux3.find(Tuple({X,V},&_aux3));
                if(tuple == NULL){
                    if(tupleU == NULL){
                        propUndefined(head,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propUndefined(head,false,propagationStack,false,propagatedLiterals);
                    const auto& it = tupleToVar.find(*head);
                    if(it!=tupleToVar.end()){
                        supportedLiterals[it->second]=currentDecisionLevel;
                    }
                }
            }
            const std::vector<const Tuple*>* falseHeads = &fbody1_.getValues({});
            for(unsigned i = 0; i < falseHeads->size(); i++){
                const Tuple* head = falseHeads->at(i);
                int X = head->at(0);
                int V = head->at(1);
                const Tuple* tuple = waux3.find(Tuple({X,V},&_aux3));
                const Tuple* tupleU = uaux3.find(Tuple({X,V},&_aux3));
                if(tuple == NULL){
                    if(tupleU != NULL){
                        propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                    }
                }else{
                    propagatedLiterals.insert(-1);
                }
            }
        }
        {
            const std::vector<const Tuple*>* tuples = &paggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id2_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int X = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == V+1){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
                int X = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V+1){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == V+1 -1){
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
                int X = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V+1){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V+1){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
            const std::vector<const Tuple*>* tuples = &paggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id3_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int X = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == V){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
                int X = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == V -1){
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
                int X = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_set0){
            int Y = starter[0];
            int X = starter[1];
            const Tuple tuple ({Y,X}, &_aux0);
            const Tuple* tupleU = uaux0.find(tuple);
            if(!starter.isNegated()){
                if(waux0.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux0.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux0){
            int Y = starter[0];
            int X = starter[1];
            if(!starter.isNegated()){
                Tuple head({Y,X}, &_aggr_set0);
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
                Tuple head({Y,X}, &_aggr_set0);
                if(waggr_set0.find(head) != NULL){
                    const auto it = tupleToVar.find(head);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    const Tuple* tupleU = uaggr_set0.find(head);
                    if(tupleU!=NULL){
                        const auto it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_set0){
            int Y = starter[0];
            int X = starter[1];
            const Tuple tuple ({Y,X}, &_aux0);
            const Tuple* tupleU = uaux0.find(tuple);
            if(!starter.isNegated()){
                if(waux0.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux0.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        {
            if(starter.getPredicateName() == &_filled && starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({Y,X},&_aux0);
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
            if(starter.getPredicateName() == &_aux0 && !starter.isNegated()){
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,Y},&_filled);
                const Tuple* tuple1 = wfilled.find(negativeTuple);
                const Tuple* tupleUndef1 = ufilled.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_filled && tupleUNegated && tupleU==tupleUndef1){
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
                int Y = starter[0];
                int X = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,Y},&_filled);
                const Tuple* tuple1 = wfilled.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ufilled.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_filled && ! tupleUNegated){
                    if(tupleU == ufilled.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_filled && !starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({Y,X},&_aux0);
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
        if(starter.getPredicateName() == &_body0){
            int Y = starter[0];
            int V = starter[1];
            const Tuple tuple ({Y,V}, &_aux1);
            const Tuple* tupleU = uaux1.find(tuple);
            if(!starter.isNegated()){
                if(waux1.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux1.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux1){
            int Y = starter[0];
            int V = starter[1];
            if(!starter.isNegated()){
                Tuple head({Y,V}, &_body0);
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
                Tuple head({Y,V}, &_body0);
                if(wbody0.find(head) != NULL){
                    const auto it = tupleToVar.find(head);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    const Tuple* tupleU = ubody0.find(head);
                    if(tupleU!=NULL){
                        const auto it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_body0){
            int Y = starter[0];
            int V = starter[1];
            const Tuple tuple ({Y,V}, &_aux1);
            const Tuple* tupleU = uaux1.find(tuple);
            if(!starter.isNegated()){
                if(waux1.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux1.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        {
            if(starter.getPredicateName() == &_xvalue && starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({Y,V},&_aux1);
                const Tuple* tuple1 = waux1.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaux1.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aux1 && ! tupleUNegated){
                    if(tupleU == uaux1.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_aux1 && !starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({Y,V},&_xvalue);
                const Tuple* tuple1 = wxvalue.find(negativeTuple);
                const Tuple* tupleUndef1 = uxvalue.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_xvalue && tupleUNegated && tupleU==tupleUndef1){
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
            if(starter.getPredicateName() == &_aux1 && starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({Y,V},&_xvalue);
                const Tuple* tuple1 = wxvalue.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uxvalue.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_xvalue && ! tupleUNegated){
                    if(tupleU == uxvalue.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_xvalue && !starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({Y,V},&_aux1);
                const Tuple* tuple1 = waux1.find(negativeTuple);
                const Tuple* tupleUndef1 = uaux1.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux1 && tupleUNegated && tupleU==tupleUndef1){
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
        if(starter.getPredicateName() == &_aggr_id0){
            int Y = starter[0];
            int V = starter[1];
            std::vector<int> sharedVar({starter[0],starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_0_0_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=V+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        auto it = tupleToVar.find(*tuples->at(i));
                        if(it != tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == V+1 -1){
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
                if(tuples->size()+tuplesU->size() < V+1){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(-it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == V+1){
                    while(tuplesU->size()>0){
                        auto itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V+1){
                    auto itProp = tupleToVar.find(*tuples->at(i));
                    if(itProp!=tupleToVar.end()){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            auto it = tupleToVar.find(*joinTuplesF->at(j));
                            if(it!=tupleToVar.end()){
                                reasonForLiteral[-itProp->second].insert(-it->second);
                            }
                        }
                        handleConflict(-itProp->second);
                        return;
                    }
                }else if(joinTuples->size() + joinTuplesU->size() == V+1){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
                int Y = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V+1){
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
                }else if(joinTuples->size() == V+1 -1){
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
                int Y = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V+1){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V+1){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_id1){
            int Y = starter[0];
            int V = starter[1];
            std::vector<int> sharedVar({starter[0],starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_0_0_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=V){
                    for(unsigned i =0; i< tuples->size(); i++){
                        auto it = tupleToVar.find(*tuples->at(i));
                        if(it != tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == V -1){
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
                if(tuples->size()+tuplesU->size() < V){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(-it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == V){
                    while(tuplesU->size()>0){
                        auto itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int Y = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V){
                    auto itProp = tupleToVar.find(*tuples->at(i));
                    if(itProp!=tupleToVar.end()){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            auto it = tupleToVar.find(*joinTuplesF->at(j));
                            if(it!=tupleToVar.end()){
                                reasonForLiteral[-itProp->second].insert(-it->second);
                            }
                        }
                        handleConflict(-itProp->second);
                        return;
                    }
                }else if(joinTuples->size() + joinTuplesU->size() == V){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
                int Y = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V){
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
                }else if(joinTuples->size() == V -1){
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
                int Y = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_0_0_.getValues(sharedVar);
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
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({Y,V},&_body0);
                const Tuple* tuple1 = wbody0.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody0.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                    if(tupleU == ubody0.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({Y,V},&_aggr_id0);
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
        {
            if(starter.getPredicateName() == &_aggr_id1 && starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({Y,V},&_body0);
                const Tuple* tuple1 = wbody0.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody0.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body0 && ! tupleUNegated){
                    if(tupleU == ubody0.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_body0 && !starter.isNegated()){
                int Y = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({Y,V},&_aggr_id1);
                const Tuple* tuple1 = waggr_id1.find(negativeTuple);
                const Tuple* tupleUndef1 = uaggr_id1.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id1 && tupleUNegated && tupleU==tupleUndef1){
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
        if(starter.getPredicateName() == &_aggr_set1){
            int X = starter[0];
            int Y = starter[1];
            const Tuple tuple ({X,Y}, &_aux2);
            const Tuple* tupleU = uaux2.find(tuple);
            if(!starter.isNegated()){
                if(waux2.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux2.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux2){
            int X = starter[0];
            int Y = starter[1];
            if(!starter.isNegated()){
                Tuple head({X,Y}, &_aggr_set1);
                const Tuple* tupleU = uaggr_set1.find(head);
                if(waggr_set1.find(head) == tupleU && tupleU==NULL){
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
                Tuple head({X,Y}, &_aggr_set1);
                if(waggr_set1.find(head) != NULL){
                    const auto it = tupleToVar.find(head);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    const Tuple* tupleU = uaggr_set1.find(head);
                    if(tupleU!=NULL){
                        const auto it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_set1){
            int X = starter[0];
            int Y = starter[1];
            const Tuple tuple ({X,Y}, &_aux2);
            const Tuple* tupleU = uaux2.find(tuple);
            if(!starter.isNegated()){
                if(waux2.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux2.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        {
            if(starter.getPredicateName() == &_filled && starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,Y},&_aux2);
                const Tuple* tuple1 = waux2.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaux2.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aux2 && ! tupleUNegated){
                    if(tupleU == uaux2.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_aux2 && !starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,Y},&_filled);
                const Tuple* tuple1 = wfilled.find(negativeTuple);
                const Tuple* tupleUndef1 = ufilled.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_filled && tupleUNegated && tupleU==tupleUndef1){
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
            if(starter.getPredicateName() == &_aux2 && starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,Y},&_filled);
                const Tuple* tuple1 = wfilled.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ufilled.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_filled && ! tupleUNegated){
                    if(tupleU == ufilled.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_filled && !starter.isNegated()){
                int X = starter[0];
                int Y = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,Y},&_aux2);
                const Tuple* tuple1 = waux2.find(negativeTuple);
                const Tuple* tupleUndef1 = uaux2.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux2 && tupleUNegated && tupleU==tupleUndef1){
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
        if(starter.getPredicateName() == &_body1){
            int X = starter[0];
            int V = starter[1];
            const Tuple tuple ({X,V}, &_aux3);
            const Tuple* tupleU = uaux3.find(tuple);
            if(!starter.isNegated()){
                if(waux3.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux3.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        if(starter.getPredicateName() == &_aux3){
            int X = starter[0];
            int V = starter[1];
            if(!starter.isNegated()){
                Tuple head({X,V}, &_body1);
                const Tuple* tupleU = ubody1.find(head);
                if(wbody1.find(head) == tupleU && tupleU==NULL){
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
                Tuple head({X,V}, &_body1);
                if(wbody1.find(head) != NULL){
                    const auto it = tupleToVar.find(head);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    const Tuple* tupleU = ubody1.find(head);
                    if(tupleU!=NULL){
                        const auto it = tupleToVar.find(head);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0 )
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_body1){
            int X = starter[0];
            int V = starter[1];
            const Tuple tuple ({X,V}, &_aux3);
            const Tuple* tupleU = uaux3.find(tuple);
            if(!starter.isNegated()){
                if(waux3.find(tuple) == tupleU && tupleU==NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[it->second].insert(startVar);
                        handleConflict(it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(it->second) == 0 )
                                reasonForLiteral[it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);
                        }
                    }
                }
            }else{
                if(waux3.find(tuple)!=NULL){
                    const auto& it = tupleToVar.find(tuple);
                    if(it!=tupleToVar.end()){
                        reasonForLiteral[-it->second].insert(startVar);
                        handleConflict(-it->second);
                        return;
                    }
                }else{
                    if(tupleU!=NULL){
                        const auto& it = tupleToVar.find(tuple);
                        if(it!=tupleToVar.end()){
                            if(reasonForLiteral.count(-it->second) == 0)
                                reasonForLiteral[-it->second].insert(startVar);
                            propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);
                        }
                    }
                }
            }
        }//close if starter
        {
            if(starter.getPredicateName() == &_yvalue && starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,V},&_aux3);
                const Tuple* tuple1 = waux3.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaux3.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aux3 && ! tupleUNegated){
                    if(tupleU == uaux3.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_aux3 && !starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,V},&_yvalue);
                const Tuple* tuple1 = wyvalue.find(negativeTuple);
                const Tuple* tupleUndef1 = uyvalue.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_yvalue && tupleUNegated && tupleU==tupleUndef1){
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
                Tuple positiveTuple({X,V},&_yvalue);
                const Tuple* tuple1 = wyvalue.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uyvalue.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_yvalue && ! tupleUNegated){
                    if(tupleU == uyvalue.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_yvalue && !starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,V},&_aux3);
                const Tuple* tuple1 = waux3.find(negativeTuple);
                const Tuple* tupleUndef1 = uaux3.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aux3 && tupleUNegated && tupleU==tupleUndef1){
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
        if(starter.getPredicateName() == &_aggr_id2){
            int X = starter[0];
            int V = starter[1];
            std::vector<int> sharedVar({starter[0],starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set1_0_0_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=V+1){
                    for(unsigned i =0; i< tuples->size(); i++){
                        auto it = tupleToVar.find(*tuples->at(i));
                        if(it != tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == V+1 -1){
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
                if(tuples->size()+tuplesU->size() < V+1){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set1_0_0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(-it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == V+1){
                    while(tuplesU->size()>0){
                        auto itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_set1){
            const std::vector<const Tuple*>* tuples = &paggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id2_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int X = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V+1){
                    auto itProp = tupleToVar.find(*tuples->at(i));
                    if(itProp!=tupleToVar.end()){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            auto it = tupleToVar.find(*joinTuplesF->at(j));
                            if(it!=tupleToVar.end()){
                                reasonForLiteral[-itProp->second].insert(-it->second);
                            }
                        }
                        handleConflict(-itProp->second);
                        return;
                    }
                }else if(joinTuples->size() + joinTuplesU->size() == V+1){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
                int X = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V+1){
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
                }else if(joinTuples->size() == V+1 -1){
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
                int X = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V+1){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V+1){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_id3){
            int X = starter[0];
            int V = starter[1];
            std::vector<int> sharedVar({starter[0],starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set1_0_0_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=V){
                    for(unsigned i =0; i< tuples->size(); i++){
                        auto it = tupleToVar.find(*tuples->at(i));
                        if(it != tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == V -1){
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
                if(tuples->size()+tuplesU->size() < V){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set1_0_0_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        auto it = tupleToVar.find(*tuplesF->at(i));
                        if(it!=tupleToVar.end()){
                            reasonForLiteral[-startVar].insert(-it->second);
                        }
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == V){
                    while(tuplesU->size()>0){
                        auto itProp = tupleToVar.find(*tuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
        if(starter.getPredicateName() == &_aggr_set1){
            const std::vector<const Tuple*>* tuples = &paggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id3_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id3_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int X = tuples->at(i)->at(0);
                int V = tuples->at(i)->at(1);
                std::vector<int> sharedVar({tuples->at(i)->at(0),tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() + joinTuplesU->size() < V){
                    auto itProp = tupleToVar.find(*tuples->at(i));
                    if(itProp!=tupleToVar.end()){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
                        for(unsigned j = 0; j < joinTuplesF->size(); j++){
                            auto it = tupleToVar.find(*joinTuplesF->at(j));
                            if(it!=tupleToVar.end()){
                                reasonForLiteral[-itProp->second].insert(-it->second);
                            }
                        }
                        handleConflict(-itProp->second);
                        return;
                    }
                }else if(joinTuples->size() + joinTuplesU->size() == V){
                    while(joinTuplesU->size()>0){
                        auto itProp = tupleToVar.find(*joinTuplesU->at(0));
                        if(itProp != tupleToVar.end()){
                            if(reasonForLiteral.count(itProp->second) == 0 ){
                                const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
                int X = tuplesF->at(i)->at(0);
                int V = tuplesF->at(i)->at(1);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0),tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size()>=V){
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
                }else if(joinTuples->size() == V -1){
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
                int X = tuplesU->at(i)->at(0);
                int V = tuplesU->at(i)->at(1);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0),tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_0_0_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_0_0_.getValues(sharedVar);
                if(joinTuples->size() >= V){
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
                }else if(joinTuples->size() + joinTuplesU->size() < V){
                    auto itProp = tupleToVar.find(*tuplesU->at(i));
                    if(itProp != tupleToVar.end()){
                        if(reasonForLiteral.count(-itProp->second) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_0_0_.getValues(sharedVar);
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
            if(starter.getPredicateName() == &_aggr_id2 && !starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,V},&_body1);
                const Tuple* tuple1 = wbody1.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody1.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body1 && ! tupleUNegated){
                    if(tupleU == ubody1.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_body1 && !starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,V},&_aggr_id2);
                const Tuple* tuple1 = waggr_id2.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_id2.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                    if(tupleU == uaggr_id2.find(positiveTuple)){
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
        {
            if(starter.getPredicateName() == &_aggr_id3 && starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple positiveTuple({X,V},&_body1);
                const Tuple* tuple1 = wbody1.find(positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ubody1.find(positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_body1 && ! tupleUNegated){
                    if(tupleU == ubody1.find(positiveTuple)){
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
            if(starter.getPredicateName() == &_body1 && !starter.isNegated()){
                int X = starter[0];
                int V = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple negativeTuple({X,V},&_aggr_id3);
                const Tuple* tuple1 = waggr_id3.find(negativeTuple);
                const Tuple* tupleUndef1 = uaggr_id3.find(negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = &negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_id3 && tupleUNegated && tupleU==tupleUndef1){
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
}
}
