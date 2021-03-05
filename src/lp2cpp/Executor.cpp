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
const std::string _a = "a";
PredicateWSet wa(2);
PredicateWSet ua(2);
PredicateWSet fa(2);
const std::string _b = "b";
PredicateWSet wb(1);
PredicateWSet ub(1);
PredicateWSet fb(1);
const std::string _c = "c";
PredicateWSet wc(2);
PredicateWSet uc(2);
PredicateWSet fc(2);
const std::string _f = "f";
PredicateWSet wf(1);
PredicateWSet uf(1);
PredicateWSet ff(1);
std::unordered_map<int,std::vector<int>> levelToExtLiterals;
std::unordered_map<int,std::vector<int>> levelToIntLiterals;
int currentDecisionLevel=-1;
std::unordered_map < unsigned int, std::set < VarsIndex > > trueAggrVars[0];
std::unordered_map < unsigned int, std::set < VarsIndex > > undefAggrVars[0];
std::unordered_map < unsigned int, std::set < VarsIndex > > trueNegativeAggrVars[0];
std::unordered_map < unsigned int, std::set < VarsIndex > > undefNegativeAggrVars[0];
DynamicTrie aggrVariable[0];
DynamicTrie sharedVariable[0];
std::unordered_map < unsigned int, ReasonTable > positiveAggrReason[0];
std::unordered_map < unsigned int, ReasonTable > negativeAggrReason[0];
std::unordered_map < unsigned int, int > actualSum[0];
std::unordered_map < unsigned int, int > possibleSum[0];
std::unordered_map < unsigned int, int > actualNegativeSum[0];
std::unordered_map < unsigned int, int > possibleNegativeSum[0];
std::unordered_map < unsigned int, int > maxPossibleNegativeSum[0];
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
AuxMap pc_0_({0});
AuxMap uc_0_({0});
AuxMap pa_1_({1});
AuxMap ua_1_({1});
AuxMap pa_({});
AuxMap ua_({});
AuxMap pc_({});
AuxMap uc_({});
AuxMap pb_({});
AuxMap ub_({});
AuxMap fb_({});
AuxMap pf_({});
AuxMap uf_({});
//printing aux maps needed for reasons of negative literals;
void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){
    int v = var==-1?var:-var;
    PostponedReasonData* data = reasonMapping.getAt(v);
    if(data == nullptr || data->getPropagationLevel() == -1) return;
    const std::vector<int>* aggregates_id = &data->getAggregateId();
    for(int i=0; i < aggregates_id->size();i++){
        int aggr_index=aggregates_id->at(i);
        std::vector<int> sharedVars(data->getSharedVariables());
        unsigned int  varsIndex=sharedVariable[aggr_index].addElements(sharedVars)->getId();
        if(data->isPositive(i)){
            positiveAggrReason[aggr_index][varsIndex].getLiteralUntil(data->getPropagationLevel(),reas);
        }else{
            negativeAggrReason[aggr_index][varsIndex].getLiteralUntil(data->getPropagationLevel(),reas);
        }
    }
    const UnorderedSet<int>* body = &data->getBodyReason();
    for(unsigned i=0;i<body->size();i++){
        reas.insert(body->at(i));
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
    std::cout<<"True "<<minus;tuple.print();std::cout<<std::endl;
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
    for(const Tuple* t: wb.getTuples()) t->print();
    std::cout<<std::endl;
    for(const Tuple* t: ub.getTuples()) t->print();
    std::cout<<std::endl;
    for(const Tuple* t: fb.getTuples()) t->print();
    std::cout<<std::endl;
}
inline void Executor::onLiteralUndef(int var) {
    unsigned uVar = var > 0 ? var : -var;
    const Tuple & tuple = atomsTable[uVar];
    std::unordered_map<const std::string*,int>::iterator sum_it;
    std::string minus = var < 0 ? "-" : "";
    std::cout<<"Undef "<<minus;tuple.print();std::cout<<std::endl;
    reasonMapping.erase(-var);
    reasonMapping.erase(-1);
    while(!propagatedLiterals.empty()){
        reasonMapping.erase(propagatedLiterals[0]);
        propagatedLiterals.erase(propagatedLiterals[0]);
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
    for(const Tuple* t: wb.getTuples()) t->print();
    std::cout<<std::endl;
    for(const Tuple* t: ub.getTuples()) t->print();
    std::cout<<std::endl;
    for(const Tuple* t: fb.getTuples()) t->print();
    std::cout<<std::endl;
}
void Executor::undefLiteralsReceived()const{
    std::cout<<"Undef received"<<std::endl;
    {
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
            int X = tuple0->at(0);
            int Y = tuple0->at(1);
            const std::vector<const Tuple*>* tuples = &pc_0_.getValues({Y});
            const std::vector<const Tuple*>* tuplesU = &uc_0_.getValues({Y});
            bool undef1=false;
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple1=NULL;
                if(i<tuples->size()){
                    tuple1=tuples->at(i);
                }else{
                    tuple1=tuplesU->at(i-tuples->size());
                    undef1=true;
                }
                int Z = tuple1->at(1);
                if(undef0 || undef1){
                    Tuple head({Y},&_b);
                    head.print();
                    std::cout<<"Saving"<<std::endl;
                    const auto& insertResult = ub.insert(Tuple({Y},&_b));
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                        atomsTable.push_back(head);
                        tupleToVar[head]=atomsTable.size()-1;
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
    wb.clear();
    pb_.clear();
    fb_.clear();
}
void Executor::init() {
    std::cout<<"Init"<<std::endl;
    createFunctionsMap();
    predicateWSetMap[&_a]=&wa;
    predicateUSetMap[&_a]=&ua;
    stringToUniqueStringPointer["a"] = &_a;
    predicateWSetMap[&_b]=&wb;
    predicateUSetMap[&_b]=&ub;
    stringToUniqueStringPointer["b"] = &_b;
    predicateWSetMap[&_c]=&wc;
    predicateUSetMap[&_c]=&uc;
    stringToUniqueStringPointer["c"] = &_c;
    predicateWSetMap[&_f]=&wf;
    predicateUSetMap[&_f]=&uf;
    stringToUniqueStringPointer["f"] = &_f;
    predicateToAuxiliaryMaps[&_f].push_back(&pf_);
    predicateToAuxiliaryMaps[&_b].push_back(&pb_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_);
    predicateToAuxiliaryMaps[&_a].push_back(&pa_1_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_);
    predicateToAuxiliaryMaps[&_c].push_back(&pc_0_);
    predicateToUndefAuxiliaryMaps[&_f].push_back(&uf_);
    predicateToUndefAuxiliaryMaps[&_b].push_back(&ub_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_);
    predicateToUndefAuxiliaryMaps[&_a].push_back(&ua_1_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_);
    predicateToUndefAuxiliaryMaps[&_c].push_back(&uc_0_);
    predicateToFalseAuxiliaryMaps[&_b].push_back(&fb_);
}
void propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative){
    if(tupleU->getPredicateName() == &_f){
        auto it = tupleToVar.find(*tupleU);
        int sign = isNegated == asNegative ? -1 : 1;
        if(it!=tupleToVar.end()){
            std::cout<<"Propagating: ";
            tupleU->print();
            std::cout <<" "<<sign*it->second<<std::endl;
        }
    }
    if(tupleU->getPredicateName() == &_c){
        auto it = tupleToVar.find(*tupleU);
        int sign = isNegated == asNegative ? -1 : 1;
        if(it!=tupleToVar.end()){
            std::cout<<"Propagating: ";
            tupleU->print();
            std::cout <<" "<<sign*it->second<<std::endl;
        }
    }
    if(tupleU->getPredicateName() == &_a){
        auto it = tupleToVar.find(*tupleU);
        int sign = isNegated == asNegative ? -1 : 1;
        if(it!=tupleToVar.end()){
            std::cout<<"Propagating: ";
            tupleU->print();
            std::cout <<" "<<sign*it->second<<std::endl;
        }
    }
    if(tupleU->getPredicateName() == &_b){
        bool propagated = false;
        if(isNegated != asNegative){
            const auto& insertResult = fb.insert(Tuple(*tupleU));
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[&_b]) {
                    auxMap -> insert2(*insertResult.first);
                }
                std::cout<<"Prop internal predicate as false";                tupleU->print();
                std::cout<<std::endl;
                propagated = true;
            }
        }else{
            std::cout<<"Prop undefined"<<std::endl;
            const auto& insertResult = wb.insert(Tuple(*tupleU));
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToAuxiliaryMaps[&_b]) {
                    auxMap -> insert2(*insertResult.first);
                }
                std::cout<<"Prop internal predicate as true";                tupleU->print();
                std::cout<<std::endl;
                propagated = true;
            }
        }
        if(propagated){
            auto it = tupleToVar.find(*tupleU);
            int sign = isNegated != asNegative ? -1 : 1;
            if(it!=tupleToVar.end()){
                stack.push_back(sign*it->second);
                levelToIntLiterals[currentDecisionLevel].push_back(sign*it->second);
            }
            ub.erase(*tupleU);
        }
    }
}
void unRollToLevel(int decisionLevel){
    for(auto& level :levelToIntLiterals){
        if(level.first >=decisionLevel){
            while(!level.second.empty()){
                int var = level.second.back();
                int uVar = var>0 ? var : -var;
                Tuple t = atomsTable[uVar];
                if(t.getPredicateName() == &_b){
                    if(var>0){
                        wb.erase(t);
                    }else{
                        fb.erase(t);
                    }
                    const auto& insertResult = ub.insert(Tuple(t));
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_b]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                    level.second.pop_back();
                }
            }
        }
    }
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts) {
    int decisionLevel = facts[0];
    if(currentDecisionLevel > decisionLevel)
        unRollToLevel(decisionLevel);
    currentDecisionLevel=decisionLevel;
    clearPropagations();
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
    }
    std::vector<int> propagationStack;
    if(decisionLevel==-1) {
        //propagation at level -1 no starter
        {
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            const std::vector<const Tuple*>* tuples = &pa_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            if(tupleU==NULL)
                tuplesU = &ua_.getValues({});
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple0=NULL;
                if(i<tuples->size())
                    tuple0=tuples->at(i);
                else{
                    tupleU = tuple0 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                    boundTupleU=false;
                }
                if(tuple0!= NULL){
                    int X = tuple0->at(0);
                    int Y = tuple0->at(1);
                    const std::vector<const Tuple*>* tuples = &pc_0_.getValues({Y});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    if(tupleU==NULL)
                        tuplesU = &uc_0_.getValues({Y});
                    for(int i=0;i<tuples->size()+tuplesU->size();i++){
                        const Tuple* tuple1=NULL;
                        if(i<tuples->size())
                            tuple1=tuples->at(i);
                        else{
                            tupleU = tuple1 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                            boundTupleU=false;
                        }
                        if(tuple1!= NULL){
                            int Z = tuple1->at(1);
                            Tuple head({Y},&_b);
                            if(tupleU==NULL){
                                if(wb.find(head)==NULL && ub.find(head)==NULL){
                                    std::cout<<"Conflict"<<std::endl;
                                }else{
                                    if(ub.find(head)!=NULL){
                                        //propagate head as true
                                        tupleU=&head;
                                        propUndefined(tupleU,tupleUNegated,propagationStack,false);
                                    }
                                }
                            }else{
                                if(wb.find(head)!=NULL){
                                    //support propagation of body literal as true
                                    if(boundTupleU){
                                        propUndefined(tupleU,tupleUNegated,propagationStack,false);
                                    }
                                    else{
                                        if((tupleU->getPredicateName() == &_a && ua_1_.getValues({Y}).size() == 1)||(tupleU->getPredicateName() == &_c && uc_0_.getValues({Y}).size() == 1)){
                                            propUndefined(tupleU,tupleUNegated,propagationStack,false);
                                        }
                                    }
                                }else if(ub.find(head)==NULL){
                                    //false head and undefined body -> propagate undefined as false
                                    propUndefined(tupleU,tupleUNegated,propagationStack,true);
                                }
                            }
                        }
                    }
                }
            }
        }
        //propagation at level -1 no starter
        {
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            const std::vector<const Tuple*>* tuples = &pb_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            if(tupleU==NULL)
                tuplesU = &ub_.getValues({});
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple0=NULL;
                if(i<tuples->size())
                    tuple0=tuples->at(i);
                else{
                    tupleU = tuple0 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                    boundTupleU=false;
                }
                if(tuple0!= NULL){
                    int X = tuple0->at(0);
                    Tuple positiveTuple({X},&_f);
                    const Tuple* tuple1=NULL;
                    if(wf.find(positiveTuple) != NULL){
                        tuple1=&positiveTuple;
                    }else if(tupleU==NULL && uf.find(positiveTuple)!=NULL){
                        tupleU = tuple1 = &positiveTuple;
                        tupleUNegated=false;
                        boundTupleU=true;
                    }
                    if(tuple1!=NULL){
                        if(tupleU==NULL){
                            std::cout<<"Conflict"<<std::endl;
                        }else{
                            //propagate body lit as false
                            propUndefined(tupleU,tupleUNegated,propagationStack,true);
                        }
                    }
                }
            }
        }
    }//close decision level == -1
    for(unsigned i=1;i<facts.size();i++) {
        unsigned factVar = facts[i] > 0 ? facts[i] : -facts[i];
        Tuple starter = atomsTable[factVar];
        starter.print();
        starter.setNegated(facts[i]<0);
        //propagation starting from true body literal
        if(starter.getPredicateName() == &_f && !starter.isNegated()){
            int X = starter[0];
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            Tuple positiveTuple({X},&_b);
            const Tuple* tuple1=NULL;
            if(wb.find(positiveTuple) != NULL){
                tuple1=&positiveTuple;
            }else if(tupleU==NULL && ub.find(positiveTuple)!=NULL){
                tupleU = tuple1 = &positiveTuple;
                tupleUNegated=false;
                boundTupleU=true;
            }
            if(tuple1!=NULL){
                if(tupleU==NULL){
                    std::cout<<"Conflict"<<std::endl;
                }else{
                    //propagate body lit as false
                    propUndefined(tupleU,tupleUNegated,propagationStack,true);
                }
            }
        }
        //propagation starting from true body literal
        if(starter.getPredicateName() == &_c && !starter.isNegated()){
            int Y = starter[0];
            int Z = starter[1];
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            const std::vector<const Tuple*>* tuples = &pa_1_.getValues({Y});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            if(tupleU==NULL)
                tuplesU = &ua_1_.getValues({Y});
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple1=NULL;
                if(i<tuples->size())
                    tuple1=tuples->at(i);
                else{
                    tupleU = tuple1 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                    boundTupleU=false;
                }
                if(tuple1!= NULL){
                    int X = tuple1->at(0);
                    Tuple head({Y},&_b);
                    if(tupleU==NULL){
                        if(wb.find(head)==NULL && ub.find(head)==NULL){
                            std::cout<<"Conflict"<<std::endl;
                        }else{
                            if(ub.find(head)!=NULL){
                                //propagate head as true
                                tupleU=&head;
                                propUndefined(tupleU,tupleUNegated,propagationStack,false);
                            }
                        }
                    }else{
                        if(wb.find(head)!=NULL){
                            //support propagation of body literal as true
                            if(boundTupleU){
                                propUndefined(tupleU,tupleUNegated,propagationStack,false);
                            }
                            else{
                                if((tupleU->getPredicateName() == &_a && ua_1_.getValues({Y}).size() == 1)){
                                    propUndefined(tupleU,tupleUNegated,propagationStack,false);
                                }
                            }
                        }else if(ub.find(head)==NULL){
                            //false head and undefined body -> propagate undefined as false
                            propUndefined(tupleU,tupleUNegated,propagationStack,true);
                        }
                    }
                }
            }
        }
        else if(starter.getPredicateName() == &_c && starter.isNegated()){
            int Y = starter[0];
            int Z = starter[1];
            if(uc_0_.getValues({Y}).size()==0){
                //propagate false head when no other literal undefined with starter predicate name
                const Tuple* tupleU = ub.find(Tuple({Y},&_b));
                if(tupleU != NULL){
                    propUndefined(tupleU,false,propagationStack,true);
                }
            }
        }
        //propagation starting from true body literal
        if(starter.getPredicateName() == &_a && !starter.isNegated()){
            int X = starter[0];
            int Y = starter[1];
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            const std::vector<const Tuple*>* tuples = &pc_0_.getValues({Y});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            if(tupleU==NULL)
                tuplesU = &uc_0_.getValues({Y});
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple1=NULL;
                if(i<tuples->size())
                    tuple1=tuples->at(i);
                else{
                    tupleU = tuple1 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                    boundTupleU=false;
                }
                if(tuple1!= NULL){
                    int Z = tuple1->at(1);
                    Tuple head({Y},&_b);
                    if(tupleU==NULL){
                        if(wb.find(head)==NULL && ub.find(head)==NULL){
                            std::cout<<"Conflict"<<std::endl;
                        }else{
                            if(ub.find(head)!=NULL){
                                //propagate head as true
                                tupleU=&head;
                                propUndefined(tupleU,tupleUNegated,propagationStack,false);
                            }
                        }
                    }else{
                        if(wb.find(head)!=NULL){
                            //support propagation of body literal as true
                            if(boundTupleU){
                                propUndefined(tupleU,tupleUNegated,propagationStack,false);
                            }
                            else{
                                if((tupleU->getPredicateName() == &_c && uc_0_.getValues({Y}).size() == 1)){
                                    propUndefined(tupleU,tupleUNegated,propagationStack,false);
                                }
                            }
                        }else if(ub.find(head)==NULL){
                            //false head and undefined body -> propagate undefined as false
                            propUndefined(tupleU,tupleUNegated,propagationStack,true);
                        }
                    }
                }
            }
        }
        else if(starter.getPredicateName() == &_a && starter.isNegated()){
            int X = starter[0];
            int Y = starter[1];
            if(ua_1_.getValues({Y}).size()==0){
                //propagate false head when no other literal undefined with starter predicate name
                const Tuple* tupleU = ub.find(Tuple({Y},&_b));
                if(tupleU != NULL){
                    propUndefined(tupleU,false,propagationStack,true);
                }
            }
        }
    }
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter = atomsTable[uStartVar];
        starter.setNegated(startVar<0);
        starter.print();std::cout<<" Starter"<<std::endl;
        propagationStack.pop_back();
        //propagation starting from true body literal
        if(starter.getPredicateName() == &_b && !starter.isNegated()){
            int X = starter[0];
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            Tuple positiveTuple({X},&_f);
            const Tuple* tuple1=NULL;
            if(wf.find(positiveTuple) != NULL){
                tuple1=&positiveTuple;
            }else if(tupleU==NULL && uf.find(positiveTuple)!=NULL){
                tupleU = tuple1 = &positiveTuple;
                tupleUNegated=false;
                boundTupleU=true;
            }
            if(tuple1!=NULL){
                if(tupleU==NULL){
                    std::cout<<"Conflict"<<std::endl;
                }else{
                    //propagate body lit as false
                    propUndefined(tupleU,tupleUNegated,propagationStack,true);
                }
            }
        }
        //propagation starting from false head
        if(starter.getPredicateName() == &_b && starter.isNegated()){
            int Y = starter[0];
            const Tuple* tupleU=NULL;
            bool tupleUNegated=false;
            bool boundTupleU=false;
            const std::vector<const Tuple*>* tuples = &pa_1_.getValues({Y});
            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
            if(tupleU==NULL)
                tuplesU = &ua_1_.getValues({Y});
            for(int i=0;i<tuples->size()+tuplesU->size();i++){
                const Tuple* tuple0=NULL;
                if(i<tuples->size())
                    tuple0=tuples->at(i);
                else{
                    tupleU = tuple0 = tuplesU->at(i-tuples->size());
                    tupleUNegated=false;
                    boundTupleU=false;
                }
                if(tuple0!= NULL){
                    int X = tuple0->at(0);
                    const std::vector<const Tuple*>* tuples = &pc_0_.getValues({Y});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    if(tupleU==NULL)
                        tuplesU = &uc_0_.getValues({Y});
                    for(int i=0;i<tuples->size()+tuplesU->size();i++){
                        const Tuple* tuple1=NULL;
                        if(i<tuples->size())
                            tuple1=tuples->at(i);
                        else{
                            tupleU = tuple1 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                            boundTupleU=false;
                        }
                        if(tuple1!= NULL){
                            int Z = tuple1->at(1);
                            if(tupleU==NULL){
                                std::cout<<"Conflict"<<std::endl;
                            }else{
                                //propagate body lit as false
                                propUndefined(tupleU,tupleUNegated,propagationStack,true);
                            }
                        }
                    }
                }
            }
        }
    }
}
}
