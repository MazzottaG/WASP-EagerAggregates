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
const std::string _aggr_id2 = "aggr_id2";
PredicateWSet waggr_id2(1);
PredicateWSet uaggr_id2(1);
PredicateWSet faggr_id2(1);
const std::string _aggr_set0 = "aggr_set0";
PredicateWSet waggr_set0(2);
PredicateWSet uaggr_set0(2);
PredicateWSet faggr_set0(2);
const std::string _aggr_set1 = "aggr_set1";
PredicateWSet waggr_set1(2);
PredicateWSet uaggr_set1(2);
PredicateWSet faggr_set1(2);
const std::string _aggr_set2 = "aggr_set2";
PredicateWSet waggr_set2(3);
PredicateWSet uaggr_set2(3);
PredicateWSet faggr_set2(3);
const std::string _cabinet = "cabinet";
PredicateWSet wcabinet(1);
PredicateWSet ucabinet(1);
PredicateWSet fcabinet(1);
const std::string _cabinetDomain = "cabinetDomain";
PredicateWSet wcabinetDomain(1);
PredicateWSet ucabinetDomain(1);
PredicateWSet fcabinetDomain(1);
const std::string _cabinetSize = "cabinetSize";
PredicateWSet wcabinetSize(2);
PredicateWSet ucabinetSize(2);
PredicateWSet fcabinetSize(2);
const std::string _cabinetTOthing = "cabinetTOthing";
PredicateWSet wcabinetTOthing(2);
PredicateWSet ucabinetTOthing(2);
PredicateWSet fcabinetTOthing(2);
const std::string _delete_cabinet = "delete_cabinet";
PredicateWSet wdelete_cabinet(1);
PredicateWSet udelete_cabinet(1);
PredicateWSet fdelete_cabinet(1);
const std::string _delete_cabinetTOthing = "delete_cabinetTOthing";
PredicateWSet wdelete_cabinetTOthing(2);
PredicateWSet udelete_cabinetTOthing(2);
PredicateWSet fdelete_cabinetTOthing(2);
const std::string _delete_personTOroom = "delete_personTOroom";
PredicateWSet wdelete_personTOroom(2);
PredicateWSet udelete_personTOroom(2);
PredicateWSet fdelete_personTOroom(2);
const std::string _delete_room = "delete_room";
PredicateWSet wdelete_room(1);
PredicateWSet udelete_room(1);
PredicateWSet fdelete_room(1);
const std::string _delete_roomTOcabinet = "delete_roomTOcabinet";
PredicateWSet wdelete_roomTOcabinet(2);
PredicateWSet udelete_roomTOcabinet(2);
PredicateWSet fdelete_roomTOcabinet(2);
const std::string _personTOroom = "personTOroom";
PredicateWSet wpersonTOroom(2);
PredicateWSet upersonTOroom(2);
PredicateWSet fpersonTOroom(2);
const std::string _personTOthing = "personTOthing";
PredicateWSet wpersonTOthing(2);
PredicateWSet upersonTOthing(2);
PredicateWSet fpersonTOthing(2);
const std::string _room = "room";
PredicateWSet wroom(1);
PredicateWSet uroom(1);
PredicateWSet froom(1);
const std::string _roomTOcabinet = "roomTOcabinet";
PredicateWSet wroomTOcabinet(2);
PredicateWSet uroomTOcabinet(2);
PredicateWSet froomTOcabinet(2);
const std::string _thing = "thing";
PredicateWSet wthing(1);
PredicateWSet uthing(1);
PredicateWSet fthing(1);
const std::string _thingLong = "thingLong";
PredicateWSet wthingLong(1);
PredicateWSet uthingLong(1);
PredicateWSet fthingLong(1);
const std::string _thingShort = "thingShort";
PredicateWSet wthingShort(1);
PredicateWSet uthingShort(1);
PredicateWSet fthingShort(1);
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
AuxMap proomTOcabinet_({});
AuxMap uroomTOcabinet_({});
AuxMap froomTOcabinet_({});
AuxMap pcabinetSize_0_({0});
AuxMap ucabinetSize_0_({0});
AuxMap fcabinetSize_0_({0});
AuxMap pcabinetTOthing_({});
AuxMap ucabinetTOthing_({});
AuxMap fcabinetTOthing_({});
AuxMap paggr_set0_({});
AuxMap uaggr_set0_({});
AuxMap faggr_set0_({});
AuxMap pthing_({});
AuxMap uthing_({});
AuxMap fthing_({});
AuxMap paggr_set0_0_({0});
AuxMap uaggr_set0_0_({0});
AuxMap faggr_set0_0_({0});
AuxMap pcabinetTOthing_1_({1});
AuxMap ucabinetTOthing_1_({1});
AuxMap fcabinetTOthing_1_({1});
AuxMap paggr_id0_({});
AuxMap uaggr_id0_({});
AuxMap faggr_id0_({});
AuxMap paggr_id0_0_({0});
AuxMap uaggr_id0_0_({0});
AuxMap faggr_id0_0_({0});
AuxMap paggr_set0_1_({1});
AuxMap uaggr_set0_1_({1});
AuxMap faggr_set0_1_({1});
AuxMap pcabinet_({});
AuxMap ucabinet_({});
AuxMap fcabinet_({});
AuxMap paggr_set1_({});
AuxMap uaggr_set1_({});
AuxMap faggr_set1_({});
AuxMap pcabinetDomain_({});
AuxMap ucabinetDomain_({});
AuxMap fcabinetDomain_({});
AuxMap paggr_set1_0_({0});
AuxMap uaggr_set1_0_({0});
AuxMap faggr_set1_0_({0});
AuxMap proomTOcabinet_1_({1});
AuxMap uroomTOcabinet_1_({1});
AuxMap froomTOcabinet_1_({1});
AuxMap paggr_id1_({});
AuxMap uaggr_id1_({});
AuxMap faggr_id1_({});
AuxMap paggr_id1_0_({0});
AuxMap uaggr_id1_0_({0});
AuxMap faggr_id1_0_({0});
AuxMap paggr_set1_1_({1});
AuxMap uaggr_set1_1_({1});
AuxMap faggr_set1_1_({1});
AuxMap proom_({});
AuxMap uroom_({});
AuxMap froom_({});
AuxMap pcabinetTOthing_0_({0});
AuxMap ucabinetTOthing_0_({0});
AuxMap fcabinetTOthing_0_({0});
AuxMap ppersonTOthing_1_({1});
AuxMap upersonTOthing_1_({1});
AuxMap fpersonTOthing_1_({1});
AuxMap ppersonTOthing_({});
AuxMap upersonTOthing_({});
AuxMap fpersonTOthing_({});
AuxMap ppersonTOroom_({});
AuxMap upersonTOroom_({});
AuxMap fpersonTOroom_({});
AuxMap ppersonTOroom_1_({1});
AuxMap upersonTOroom_1_({1});
AuxMap fpersonTOroom_1_({1});
AuxMap pthingLong_({});
AuxMap uthingLong_({});
AuxMap fthingLong_({});
AuxMap pthingShort_({});
AuxMap uthingShort_({});
AuxMap fthingShort_({});
AuxMap paggr_set2_({});
AuxMap uaggr_set2_({});
AuxMap faggr_set2_({});
AuxMap paggr_set2_1_2_({1,2});
AuxMap uaggr_set2_1_2_({1,2});
AuxMap faggr_set2_1_2_({1,2});
AuxMap pcabinetSize_({});
AuxMap ucabinetSize_({});
AuxMap fcabinetSize_({});
AuxMap paggr_set2_0_1_({0,1});
AuxMap uaggr_set2_0_1_({0,1});
AuxMap faggr_set2_0_1_({0,1});
AuxMap paggr_set2_1_({1});
AuxMap uaggr_set2_1_({1});
AuxMap faggr_set2_1_({1});
AuxMap paggr_id2_({});
AuxMap uaggr_id2_({});
AuxMap faggr_id2_({});
AuxMap paggr_id2_0_({0});
AuxMap uaggr_id2_0_({0});
AuxMap faggr_id2_0_({0});
AuxMap paggr_set2_2_({2});
AuxMap uaggr_set2_2_({2});
AuxMap faggr_set2_2_({2});
AuxMap pdelete_cabinetTOthing_({});
AuxMap udelete_cabinetTOthing_({});
AuxMap fdelete_cabinetTOthing_({});
AuxMap pdelete_roomTOcabinet_({});
AuxMap udelete_roomTOcabinet_({});
AuxMap fdelete_roomTOcabinet_({});
AuxMap pdelete_personTOroom_({});
AuxMap udelete_personTOroom_({});
AuxMap fdelete_personTOroom_({});
AuxMap pdelete_cabinet_({});
AuxMap udelete_cabinet_({});
AuxMap fdelete_cabinet_({});
AuxMap pdelete_room_({});
AuxMap udelete_room_({});
AuxMap fdelete_room_({});
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
    {
        const std::vector<const Tuple*>* tuples = &proomTOcabinet_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uroomTOcabinet_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int R = tuple->at(0);
            int C = tuple->at(1);
            Tuple* boundTuple = factory.addNewInternalTuple({C}, &_cabinetDomain);
            if(ucabinetDomain.find(*boundTuple)!=NULL || wcabinetDomain.find(*boundTuple)!=NULL){
                const std::vector<const Tuple*>* tuples = &pcabinetSize_0_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &ucabinetSize_0_.getValues({C});
                for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
                    const Tuple* tuple = NULL;
                    if(i<tuples->size())
                        tuple=tuples->at(i);
                    else
                        tuple=tuplesU->at(i-tuples->size());
                    if(tuple->at(0) == C){
                        int S = tuple->at(1);
                        Tuple* aux = factory.addNewInternalTuple({S,C,R}, &_aggr_set2);
                        if(uaggr_set2.find(*aux) == NULL){
                            const auto& insertResult = uaggr_set2.insert(aux);
                            if (insertResult.second) {
                                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set2]) {
                                    auxMap -> insert2(*insertResult.first);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &proomTOcabinet_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uroomTOcabinet_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int R = tuple->at(0);
            int C = tuple->at(1);
            Tuple* boundTuple = factory.addNewInternalTuple({C}, &_cabinetDomain);
            if(ucabinetDomain.find(*boundTuple)!=NULL || wcabinetDomain.find(*boundTuple)!=NULL){
                Tuple* aux = factory.addNewInternalTuple({C,R}, &_aggr_set1);
                if(uaggr_set1.find(*aux) == NULL){
                    const auto& insertResult = uaggr_set1.insert(aux);
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set1]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &pcabinetTOthing_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ucabinetTOthing_.getValues({});
        for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size())
                tuple=tuples->at(i);
            else
                tuple=tuplesU->at(i-tuples->size());
            int C = tuple->at(0);
            int T = tuple->at(1);
            Tuple* boundTuple = factory.addNewInternalTuple({T}, &_thing);
            if(uthing.find(*boundTuple)!=NULL || wthing.find(*boundTuple)!=NULL){
                Tuple* aux = factory.addNewInternalTuple({T,C}, &_aggr_set0);
                if(uaggr_set0.find(*aux) == NULL){
                    const auto& insertResult = uaggr_set0.insert(aux);
                    if (insertResult.second) {
                        for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_set0]) {
                            auxMap -> insert2(*insertResult.first);
                        }
                    }
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &proom_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uroom_.getValues({});
        for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){
            const Tuple* tuple = NULL;
            if(i<tuples->size()){
                tuple=tuples->at(i);
            }else{
                tuple=tuplesU->at(i-tuples->size());
            }
            Tuple* head = factory.addNewInternalTuple({tuple->at(0)},&_aggr_id2);
            const auto& insertResult = uaggr_id2.insert(head);
            if (insertResult.second) {
                for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_aggr_id2]) {
                    auxMap -> insert2(*insertResult.first);
                }
            }
        }
    }
    {
        const std::vector<const Tuple*>* tuples = &proom_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &uroom_.getValues({});
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
        const std::vector<const Tuple*>* tuples = &pcabinet_.getValues({});
        const std::vector<const Tuple*>* tuplesU = &ucabinet_.getValues({});
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
        const std::vector<const Tuple*>* aggregateIds = &uaggr_id2_.getValues({});
        for(unsigned i=0;i<aggregateIds->size();i++){
            int it = aggregateIds->at(i)->getId();
            const std::vector<const Tuple*>* aggrSetTuples = &uaggr_set2_2_.getValues({aggregateIds->at(i)->at(0)});
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
    waggr_id2.clear();
    paggr_id2_.clear();
    paggr_id2_0_.clear();
    paggr_id1_.clear();
    paggr_id1_0_.clear();
    paggr_id0_.clear();
    paggr_id0_0_.clear();
    faggr_id2_.clear();
    faggr_id2_0_.clear();
    faggr_id1_.clear();
    faggr_id1_0_.clear();
    faggr_id0_.clear();
    faggr_id0_0_.clear();
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
    predicateWSetMap[&_aggr_id2]=&waggr_id2;
    predicateUSetMap[&_aggr_id2]=&uaggr_id2;
    predicateFSetMap[&_aggr_id2]=&faggr_id2;
    stringToUniqueStringPointer["aggr_id2"] = &_aggr_id2;
    predicateWSetMap[&_aggr_set0]=&waggr_set0;
    predicateUSetMap[&_aggr_set0]=&uaggr_set0;
    predicateFSetMap[&_aggr_set0]=&faggr_set0;
    stringToUniqueStringPointer["aggr_set0"] = &_aggr_set0;
    predicateWSetMap[&_aggr_set1]=&waggr_set1;
    predicateUSetMap[&_aggr_set1]=&uaggr_set1;
    predicateFSetMap[&_aggr_set1]=&faggr_set1;
    stringToUniqueStringPointer["aggr_set1"] = &_aggr_set1;
    predicateWSetMap[&_aggr_set2]=&waggr_set2;
    predicateUSetMap[&_aggr_set2]=&uaggr_set2;
    predicateFSetMap[&_aggr_set2]=&faggr_set2;
    stringToUniqueStringPointer["aggr_set2"] = &_aggr_set2;
    predicateWSetMap[&_cabinet]=&wcabinet;
    predicateUSetMap[&_cabinet]=&ucabinet;
    predicateFSetMap[&_cabinet]=&fcabinet;
    stringToUniqueStringPointer["cabinet"] = &_cabinet;
    predicateWSetMap[&_cabinetDomain]=&wcabinetDomain;
    predicateUSetMap[&_cabinetDomain]=&ucabinetDomain;
    predicateFSetMap[&_cabinetDomain]=&fcabinetDomain;
    stringToUniqueStringPointer["cabinetDomain"] = &_cabinetDomain;
    predicateWSetMap[&_cabinetSize]=&wcabinetSize;
    predicateUSetMap[&_cabinetSize]=&ucabinetSize;
    predicateFSetMap[&_cabinetSize]=&fcabinetSize;
    stringToUniqueStringPointer["cabinetSize"] = &_cabinetSize;
    predicateWSetMap[&_cabinetTOthing]=&wcabinetTOthing;
    predicateUSetMap[&_cabinetTOthing]=&ucabinetTOthing;
    predicateFSetMap[&_cabinetTOthing]=&fcabinetTOthing;
    stringToUniqueStringPointer["cabinetTOthing"] = &_cabinetTOthing;
    predicateWSetMap[&_delete_cabinet]=&wdelete_cabinet;
    predicateUSetMap[&_delete_cabinet]=&udelete_cabinet;
    predicateFSetMap[&_delete_cabinet]=&fdelete_cabinet;
    stringToUniqueStringPointer["delete_cabinet"] = &_delete_cabinet;
    predicateWSetMap[&_delete_cabinetTOthing]=&wdelete_cabinetTOthing;
    predicateUSetMap[&_delete_cabinetTOthing]=&udelete_cabinetTOthing;
    predicateFSetMap[&_delete_cabinetTOthing]=&fdelete_cabinetTOthing;
    stringToUniqueStringPointer["delete_cabinetTOthing"] = &_delete_cabinetTOthing;
    predicateWSetMap[&_delete_personTOroom]=&wdelete_personTOroom;
    predicateUSetMap[&_delete_personTOroom]=&udelete_personTOroom;
    predicateFSetMap[&_delete_personTOroom]=&fdelete_personTOroom;
    stringToUniqueStringPointer["delete_personTOroom"] = &_delete_personTOroom;
    predicateWSetMap[&_delete_room]=&wdelete_room;
    predicateUSetMap[&_delete_room]=&udelete_room;
    predicateFSetMap[&_delete_room]=&fdelete_room;
    stringToUniqueStringPointer["delete_room"] = &_delete_room;
    predicateWSetMap[&_delete_roomTOcabinet]=&wdelete_roomTOcabinet;
    predicateUSetMap[&_delete_roomTOcabinet]=&udelete_roomTOcabinet;
    predicateFSetMap[&_delete_roomTOcabinet]=&fdelete_roomTOcabinet;
    stringToUniqueStringPointer["delete_roomTOcabinet"] = &_delete_roomTOcabinet;
    predicateWSetMap[&_personTOroom]=&wpersonTOroom;
    predicateUSetMap[&_personTOroom]=&upersonTOroom;
    predicateFSetMap[&_personTOroom]=&fpersonTOroom;
    stringToUniqueStringPointer["personTOroom"] = &_personTOroom;
    predicateWSetMap[&_personTOthing]=&wpersonTOthing;
    predicateUSetMap[&_personTOthing]=&upersonTOthing;
    predicateFSetMap[&_personTOthing]=&fpersonTOthing;
    stringToUniqueStringPointer["personTOthing"] = &_personTOthing;
    predicateWSetMap[&_room]=&wroom;
    predicateUSetMap[&_room]=&uroom;
    predicateFSetMap[&_room]=&froom;
    stringToUniqueStringPointer["room"] = &_room;
    predicateWSetMap[&_roomTOcabinet]=&wroomTOcabinet;
    predicateUSetMap[&_roomTOcabinet]=&uroomTOcabinet;
    predicateFSetMap[&_roomTOcabinet]=&froomTOcabinet;
    stringToUniqueStringPointer["roomTOcabinet"] = &_roomTOcabinet;
    predicateWSetMap[&_thing]=&wthing;
    predicateUSetMap[&_thing]=&uthing;
    predicateFSetMap[&_thing]=&fthing;
    stringToUniqueStringPointer["thing"] = &_thing;
    predicateWSetMap[&_thingLong]=&wthingLong;
    predicateUSetMap[&_thingLong]=&uthingLong;
    predicateFSetMap[&_thingLong]=&fthingLong;
    stringToUniqueStringPointer["thingLong"] = &_thingLong;
    predicateWSetMap[&_thingShort]=&wthingShort;
    predicateUSetMap[&_thingShort]=&uthingShort;
    predicateFSetMap[&_thingShort]=&fthingShort;
    stringToUniqueStringPointer["thingShort"] = &_thingShort;
    predicateToAuxiliaryMaps[&_delete_cabinet].push_back(&pdelete_cabinet_);
    predicateToAuxiliaryMaps[&_delete_roomTOcabinet].push_back(&pdelete_roomTOcabinet_);
    predicateToAuxiliaryMaps[&_aggr_id2].push_back(&paggr_id2_);
    predicateToAuxiliaryMaps[&_aggr_id2].push_back(&paggr_id2_0_);
    predicateToAuxiliaryMaps[&_aggr_set2].push_back(&paggr_set2_);
    predicateToAuxiliaryMaps[&_aggr_set2].push_back(&paggr_set2_0_1_);
    predicateToAuxiliaryMaps[&_aggr_set2].push_back(&paggr_set2_1_);
    predicateToAuxiliaryMaps[&_aggr_set2].push_back(&paggr_set2_1_2_);
    predicateToAuxiliaryMaps[&_aggr_set2].push_back(&paggr_set2_2_);
    predicateToAuxiliaryMaps[&_thingLong].push_back(&pthingLong_);
    predicateToAuxiliaryMaps[&_roomTOcabinet].push_back(&proomTOcabinet_);
    predicateToAuxiliaryMaps[&_roomTOcabinet].push_back(&proomTOcabinet_1_);
    predicateToAuxiliaryMaps[&_delete_room].push_back(&pdelete_room_);
    predicateToAuxiliaryMaps[&_cabinetSize].push_back(&pcabinetSize_);
    predicateToAuxiliaryMaps[&_cabinetSize].push_back(&pcabinetSize_0_);
    predicateToAuxiliaryMaps[&_cabinetTOthing].push_back(&pcabinetTOthing_);
    predicateToAuxiliaryMaps[&_cabinetTOthing].push_back(&pcabinetTOthing_0_);
    predicateToAuxiliaryMaps[&_cabinetTOthing].push_back(&pcabinetTOthing_1_);
    predicateToAuxiliaryMaps[&_delete_cabinetTOthing].push_back(&pdelete_cabinetTOthing_);
    predicateToAuxiliaryMaps[&_room].push_back(&proom_);
    predicateToAuxiliaryMaps[&_thing].push_back(&pthing_);
    predicateToAuxiliaryMaps[&_aggr_id1].push_back(&paggr_id1_);
    predicateToAuxiliaryMaps[&_aggr_id1].push_back(&paggr_id1_0_);
    predicateToAuxiliaryMaps[&_cabinet].push_back(&pcabinet_);
    predicateToAuxiliaryMaps[&_delete_personTOroom].push_back(&pdelete_personTOroom_);
    predicateToAuxiliaryMaps[&_thingShort].push_back(&pthingShort_);
    predicateToAuxiliaryMaps[&_aggr_id0].push_back(&paggr_id0_);
    predicateToAuxiliaryMaps[&_aggr_id0].push_back(&paggr_id0_0_);
    predicateToAuxiliaryMaps[&_aggr_set1].push_back(&paggr_set1_);
    predicateToAuxiliaryMaps[&_aggr_set1].push_back(&paggr_set1_0_);
    predicateToAuxiliaryMaps[&_aggr_set1].push_back(&paggr_set1_1_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_0_);
    predicateToAuxiliaryMaps[&_aggr_set0].push_back(&paggr_set0_1_);
    predicateToAuxiliaryMaps[&_personTOroom].push_back(&ppersonTOroom_);
    predicateToAuxiliaryMaps[&_personTOroom].push_back(&ppersonTOroom_1_);
    predicateToAuxiliaryMaps[&_cabinetDomain].push_back(&pcabinetDomain_);
    predicateToAuxiliaryMaps[&_personTOthing].push_back(&ppersonTOthing_);
    predicateToAuxiliaryMaps[&_personTOthing].push_back(&ppersonTOthing_1_);
    predicateToUndefAuxiliaryMaps[&_delete_cabinet].push_back(&udelete_cabinet_);
    predicateToUndefAuxiliaryMaps[&_delete_roomTOcabinet].push_back(&udelete_roomTOcabinet_);
    predicateToUndefAuxiliaryMaps[&_aggr_id2].push_back(&uaggr_id2_);
    predicateToUndefAuxiliaryMaps[&_aggr_id2].push_back(&uaggr_id2_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set2].push_back(&uaggr_set2_);
    predicateToUndefAuxiliaryMaps[&_aggr_set2].push_back(&uaggr_set2_0_1_);
    predicateToUndefAuxiliaryMaps[&_aggr_set2].push_back(&uaggr_set2_1_);
    predicateToUndefAuxiliaryMaps[&_aggr_set2].push_back(&uaggr_set2_1_2_);
    predicateToUndefAuxiliaryMaps[&_aggr_set2].push_back(&uaggr_set2_2_);
    predicateToUndefAuxiliaryMaps[&_thingLong].push_back(&uthingLong_);
    predicateToUndefAuxiliaryMaps[&_roomTOcabinet].push_back(&uroomTOcabinet_);
    predicateToUndefAuxiliaryMaps[&_roomTOcabinet].push_back(&uroomTOcabinet_1_);
    predicateToUndefAuxiliaryMaps[&_delete_room].push_back(&udelete_room_);
    predicateToUndefAuxiliaryMaps[&_cabinetSize].push_back(&ucabinetSize_);
    predicateToUndefAuxiliaryMaps[&_cabinetSize].push_back(&ucabinetSize_0_);
    predicateToUndefAuxiliaryMaps[&_cabinetTOthing].push_back(&ucabinetTOthing_);
    predicateToUndefAuxiliaryMaps[&_cabinetTOthing].push_back(&ucabinetTOthing_0_);
    predicateToUndefAuxiliaryMaps[&_cabinetTOthing].push_back(&ucabinetTOthing_1_);
    predicateToUndefAuxiliaryMaps[&_delete_cabinetTOthing].push_back(&udelete_cabinetTOthing_);
    predicateToUndefAuxiliaryMaps[&_room].push_back(&uroom_);
    predicateToUndefAuxiliaryMaps[&_thing].push_back(&uthing_);
    predicateToUndefAuxiliaryMaps[&_aggr_id1].push_back(&uaggr_id1_);
    predicateToUndefAuxiliaryMaps[&_aggr_id1].push_back(&uaggr_id1_0_);
    predicateToUndefAuxiliaryMaps[&_cabinet].push_back(&ucabinet_);
    predicateToUndefAuxiliaryMaps[&_delete_personTOroom].push_back(&udelete_personTOroom_);
    predicateToUndefAuxiliaryMaps[&_thingShort].push_back(&uthingShort_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0].push_back(&uaggr_id0_);
    predicateToUndefAuxiliaryMaps[&_aggr_id0].push_back(&uaggr_id0_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set1].push_back(&uaggr_set1_);
    predicateToUndefAuxiliaryMaps[&_aggr_set1].push_back(&uaggr_set1_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set1].push_back(&uaggr_set1_1_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_0_);
    predicateToUndefAuxiliaryMaps[&_aggr_set0].push_back(&uaggr_set0_1_);
    predicateToUndefAuxiliaryMaps[&_personTOroom].push_back(&upersonTOroom_);
    predicateToUndefAuxiliaryMaps[&_personTOroom].push_back(&upersonTOroom_1_);
    predicateToUndefAuxiliaryMaps[&_cabinetDomain].push_back(&ucabinetDomain_);
    predicateToUndefAuxiliaryMaps[&_personTOthing].push_back(&upersonTOthing_);
    predicateToUndefAuxiliaryMaps[&_personTOthing].push_back(&upersonTOthing_1_);
    predicateToFalseAuxiliaryMaps[&_delete_cabinet].push_back(&fdelete_cabinet_);
    predicateToFalseAuxiliaryMaps[&_delete_roomTOcabinet].push_back(&fdelete_roomTOcabinet_);
    predicateToFalseAuxiliaryMaps[&_aggr_id2].push_back(&faggr_id2_);
    predicateToFalseAuxiliaryMaps[&_aggr_id2].push_back(&faggr_id2_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set2].push_back(&faggr_set2_);
    predicateToFalseAuxiliaryMaps[&_aggr_set2].push_back(&faggr_set2_0_1_);
    predicateToFalseAuxiliaryMaps[&_aggr_set2].push_back(&faggr_set2_1_);
    predicateToFalseAuxiliaryMaps[&_aggr_set2].push_back(&faggr_set2_1_2_);
    predicateToFalseAuxiliaryMaps[&_aggr_set2].push_back(&faggr_set2_2_);
    predicateToFalseAuxiliaryMaps[&_thingLong].push_back(&fthingLong_);
    predicateToFalseAuxiliaryMaps[&_roomTOcabinet].push_back(&froomTOcabinet_);
    predicateToFalseAuxiliaryMaps[&_roomTOcabinet].push_back(&froomTOcabinet_1_);
    predicateToFalseAuxiliaryMaps[&_delete_room].push_back(&fdelete_room_);
    predicateToFalseAuxiliaryMaps[&_cabinetSize].push_back(&fcabinetSize_);
    predicateToFalseAuxiliaryMaps[&_cabinetSize].push_back(&fcabinetSize_0_);
    predicateToFalseAuxiliaryMaps[&_cabinetTOthing].push_back(&fcabinetTOthing_);
    predicateToFalseAuxiliaryMaps[&_cabinetTOthing].push_back(&fcabinetTOthing_0_);
    predicateToFalseAuxiliaryMaps[&_cabinetTOthing].push_back(&fcabinetTOthing_1_);
    predicateToFalseAuxiliaryMaps[&_delete_cabinetTOthing].push_back(&fdelete_cabinetTOthing_);
    predicateToFalseAuxiliaryMaps[&_room].push_back(&froom_);
    predicateToFalseAuxiliaryMaps[&_thing].push_back(&fthing_);
    predicateToFalseAuxiliaryMaps[&_aggr_id1].push_back(&faggr_id1_);
    predicateToFalseAuxiliaryMaps[&_aggr_id1].push_back(&faggr_id1_0_);
    predicateToFalseAuxiliaryMaps[&_cabinet].push_back(&fcabinet_);
    predicateToFalseAuxiliaryMaps[&_delete_personTOroom].push_back(&fdelete_personTOroom_);
    predicateToFalseAuxiliaryMaps[&_thingShort].push_back(&fthingShort_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0].push_back(&faggr_id0_);
    predicateToFalseAuxiliaryMaps[&_aggr_id0].push_back(&faggr_id0_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set1].push_back(&faggr_set1_);
    predicateToFalseAuxiliaryMaps[&_aggr_set1].push_back(&faggr_set1_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set1].push_back(&faggr_set1_1_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_0_);
    predicateToFalseAuxiliaryMaps[&_aggr_set0].push_back(&faggr_set0_1_);
    predicateToFalseAuxiliaryMaps[&_personTOroom].push_back(&fpersonTOroom_);
    predicateToFalseAuxiliaryMaps[&_personTOroom].push_back(&fpersonTOroom_1_);
    predicateToFalseAuxiliaryMaps[&_cabinetDomain].push_back(&fcabinetDomain_);
    predicateToFalseAuxiliaryMaps[&_personTOthing].push_back(&fpersonTOthing_);
    predicateToFalseAuxiliaryMaps[&_personTOthing].push_back(&fpersonTOthing_1_);
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
                    if(tupleU->getPredicateName() == &_aggr_set2){
                        {
                            const std::vector<const Tuple*>* aggrIds = &paggr_id2_0_.getValues({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &uaggr_id2_0_.getValues({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                actualSum[itAggrId]+=tupleU->at(0);
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &faggr_id2_0_.getValues({tupleU->at(2)});
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
                    if(tupleU->getPredicateName() == &_aggr_set2){
                        {
                            const std::vector<const Tuple*>* aggrIds = &paggr_id2_0_.getValues({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &uaggr_id2_0_.getValues({tupleU->at(2)});
                            for(unsigned i=0;i<aggrIds->size();i++){
                                int itAggrId = aggrIds->at(i)->getId();
                                possibleSum[itAggrId]-=tupleU->at(0);
                            }
                        }
                        {
                            const std::vector<const Tuple*>* aggrIds = &faggr_id2_0_.getValues({tupleU->at(2)});
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
        propagatedLiterals.insert(it*sign);
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
            if(tuple->getPredicateName() == &_aggr_set2){
                {
                    const std::vector<const Tuple*>* aggrIds = &paggr_id2_0_.getValues({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i)->getId();
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<const Tuple*>* aggrIds = &uaggr_id2_0_.getValues({tuple->at(2)});
                    for(unsigned i=0;i<aggrIds->size();i++){
                        int itAggrId = aggrIds->at(i)->getId();
                        if(var>0)
                            actualSum[itAggrId]-=tuple->at(0);
                        possibleSum[itAggrId]+=tuple->at(0);
                    }
                }
                {
                    const std::vector<const Tuple*>* aggrIds = &faggr_id2_0_.getValues({tuple->at(2)});
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
                int C = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 6){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 6){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int C = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 6){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 6 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
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
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int C = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 6){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 6){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
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
                int R = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 5){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() + joinTuplesU->size() == 5){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int R = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 5){
                    propagatedLiterals.insert(-1);
                }else if(joinTuples->size() == 5 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
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
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int R = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
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
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_.getValues({});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        int T1 = tuple0->at(1);
                        const std::vector<const Tuple*>* tuples = &pcabinetTOthing_0_.getValues({C});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucabinetTOthing_0_.getValues({C});
                        else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                                if(tupleU->at(0) == C)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int T2 = tuple1->at(1);
                                const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T1});
                                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &upersonTOthing_1_.getValues({T1});
                                else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                                    const Tuple* tuple2 = NULL;
                                    if(i<tuples->size())
                                        tuple2 = tuples->at(i);
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple2 = tuplesU->at(i-tuples->size());
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == T1)
                                            tuple2 = tupleU;
                                    }
                                    if(tuple2!=NULL){
                                        int P1 = tuple2->at(0);
                                        const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T2});
                                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                        std::vector<const Tuple*> undeRepeated;
                                        if(tupleU == NULL)
                                            tuplesU = &upersonTOthing_1_.getValues({T2});
                                        else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                                            const Tuple* tuple3 = NULL;
                                            if(i<tuples->size())
                                                tuple3 = tuples->at(i);
                                            else if(i<tuples->size()+tuplesU->size()){
                                                tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                                tupleUNegated=false;
                                            }else if(!undeRepeated.empty()){
                                                if(tupleU->at(1) == T2)
                                                    tuple3 = tupleU;
                                            }
                                            if(tuple3!=NULL){
                                                int P2 = tuple3->at(0);
                                                if(P1 < P2){
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
                    }
                }
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &ppersonTOroom_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upersonTOroom_.getValues({});
                else if(tupleU->getPredicateName() == &_personTOroom && !tupleUNegated)
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
                        int P1 = tuple0->at(0);
                        int R = tuple0->at(1);
                        const std::vector<const Tuple*>* tuples = &ppersonTOroom_1_.getValues({R});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &upersonTOroom_1_.getValues({R});
                        else if(tupleU->getPredicateName() == &_personTOroom && !tupleUNegated)
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
                                if(tupleU->at(1) == R)
                                    tuple1 = tupleU;
                            }
                            if(tuple1!=NULL){
                                int P2 = tuple1->at(0);
                                if(P1 < P2){
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
                const std::vector<const Tuple*>* tuples = &pthingLong_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uthingLong_.getValues({});
                else if(tupleU->getPredicateName() == &_thingLong && !tupleUNegated)
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
                        int T = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({T},&_thingShort);
                        const Tuple* tuple1 = wthingShort.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uthingShort.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_thingShort && ! tupleUNegated){
                            if(tupleU == uthingShort.find(*positiveTuple)){
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
            const std::vector<const Tuple*>* tuples = &paggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id2_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int R = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set2_2_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set2_2_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 5){
                    propagatedLiterals.insert(-1);
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= 5) {index++; continue;}
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set2_2_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i)->getId();
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
                int R = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set2_2_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set2_2_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(actualSum[aggrIdIt] >= 5){
                    propagatedLiterals.insert(-1);
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= 5){
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
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int R = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set2_2_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set2_2_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(actualSum[aggrIdIt] >= 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set2_2_.getValues(sharedVar);
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
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_.getValues({});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        int T = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({C,T},&_delete_cabinetTOthing);
                        const Tuple* tuple1 = wdelete_cabinetTOthing.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = udelete_cabinetTOthing.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_cabinetTOthing && ! tupleUNegated){
                            if(tupleU == udelete_cabinetTOthing.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &proomTOcabinet_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroomTOcabinet_.getValues({});
                else if(tupleU->getPredicateName() == &_roomTOcabinet && !tupleUNegated)
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
                        int R = tuple0->at(0);
                        int C = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({R,C},&_delete_roomTOcabinet);
                        const Tuple* tuple1 = wdelete_roomTOcabinet.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = udelete_roomTOcabinet.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_roomTOcabinet && ! tupleUNegated){
                            if(tupleU == udelete_roomTOcabinet.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &ppersonTOroom_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upersonTOroom_.getValues({});
                else if(tupleU->getPredicateName() == &_personTOroom && !tupleUNegated)
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
                        int R = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({P,R},&_delete_personTOroom);
                        const Tuple* tuple1 = wdelete_personTOroom.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = udelete_personTOroom.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_personTOroom && ! tupleUNegated){
                            if(tupleU == udelete_personTOroom.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &pcabinet_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinet_.getValues({});
                else if(tupleU->getPredicateName() == &_cabinet && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({C},&_delete_cabinet);
                        const Tuple* tuple1 = wdelete_cabinet.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = udelete_cabinet.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_cabinet && ! tupleUNegated){
                            if(tupleU == udelete_cabinet.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &proom_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroom_.getValues({});
                else if(tupleU->getPredicateName() == &_room && !tupleUNegated)
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
                        int R = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({R},&_delete_room);
                        const Tuple* tuple1 = wdelete_room.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = udelete_room.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_room && ! tupleUNegated){
                            if(tupleU == udelete_room.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &proom_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroom_.getValues({});
                else if(tupleU->getPredicateName() == &_room && !tupleUNegated)
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
                        int R = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({R},&_aggr_id2);
                        const Tuple* tuple1 = waggr_id2.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uaggr_id2.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                            if(tupleU == uaggr_id2.find(*positiveTuple)){
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
                const std::vector<const Tuple*>* tuples = &proomTOcabinet_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroomTOcabinet_.getValues({});
                else if(tupleU->getPredicateName() == &_roomTOcabinet && !tupleUNegated)
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
                        int R = tuple0->at(0);
                        int C = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                        const Tuple* tuple1 = wcabinetDomain.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = ucabinetDomain.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                            if(tupleU == ucabinetDomain.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            const std::vector<const Tuple*>* tuples = &pcabinetSize_0_.getValues({C});
                            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &ucabinetSize_0_.getValues({C});
                            else if(tupleU->getPredicateName() == &_cabinetSize && !tupleUNegated)
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
                                const Tuple* tuple2 = NULL;
                                if(i<tuples->size())
                                    tuple2 = tuples->at(i);
                                else if(i<tuples->size()+tuplesU->size()){
                                    tupleU = tuple2 = tuplesU->at(i-tuples->size());
                                    tupleUNegated=false;
                                }else if(!undeRepeated.empty()){
                                    if(tupleU->at(0) == C)
                                        tuple2 = tupleU;
                                }
                                if(tuple2!=NULL){
                                    int S = tuple2->at(1);
                                    Tuple* negativeTuple = factory.addNewInternalTuple({S,C,R},&_aggr_set2);
                                    const Tuple* tuple3 = waggr_set2.find(*negativeTuple);
                                    const Tuple* tupleUndef3 = uaggr_set2.find(*negativeTuple);
                                    if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                        tuple3 = negativeTuple;
                                    else if(tupleU == NULL & tupleUndef3 != NULL){
                                        tupleU = tuple3 = tupleUndef3;
                                        tupleUNegated=true;
                                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set2 && tupleUNegated && tupleU==tupleUndef3){
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
            }
        }
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set2_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set2 && !tupleUNegated)
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
                        int S = tuple0->at(0);
                        int C = tuple0->at(1);
                        int R = tuple0->at(2);
                        Tuple* negativeTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                        const Tuple* tuple1 = wcabinetDomain.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ucabinetDomain.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetDomain && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paggr_set2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set2_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set2 && !tupleUNegated)
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
                        int S = tuple0->at(0);
                        int C = tuple0->at(1);
                        int R = tuple0->at(2);
                        Tuple* negativeTuple = factory.addNewInternalTuple({C,S},&_cabinetSize);
                        const Tuple* tuple1 = wcabinetSize.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ucabinetSize.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetSize && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paggr_set2_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set2_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set2 && !tupleUNegated)
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
                        int S = tuple0->at(0);
                        int C = tuple0->at(1);
                        int R = tuple0->at(2);
                        Tuple* negativeTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                        const Tuple* tuple1 = wroomTOcabinet.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uroomTOcabinet.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_roomTOcabinet && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &proom_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroom_.getValues({});
                else if(tupleU->getPredicateName() == &_room && !tupleUNegated)
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
                        int R = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({R},&_aggr_id1);
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
                const std::vector<const Tuple*>* tuples = &proomTOcabinet_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroomTOcabinet_.getValues({});
                else if(tupleU->getPredicateName() == &_roomTOcabinet && !tupleUNegated)
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
                        int R = tuple0->at(0);
                        int C = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                        const Tuple* tuple1 = wcabinetDomain.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = ucabinetDomain.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                            if(tupleU == ucabinetDomain.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({C,R},&_aggr_set1);
                            const Tuple* tuple2 = waggr_set1.find(*negativeTuple);
                            const Tuple* tupleUndef2 = uaggr_set1.find(*negativeTuple);
                            if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                                tuple2 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef2 != NULL){
                                tupleU = tuple2 = tupleUndef2;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set1 && tupleUNegated && tupleU==tupleUndef2){
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
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set1_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set1 && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        int R = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                        const Tuple* tuple1 = wcabinetDomain.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ucabinetDomain.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetDomain && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paggr_set1_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set1_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set1 && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        int R = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                        const Tuple* tuple1 = wroomTOcabinet.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uroomTOcabinet.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_roomTOcabinet && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &pcabinet_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinet_.getValues({});
                else if(tupleU->getPredicateName() == &_cabinet && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        Tuple* positiveTuple = factory.addNewInternalTuple({C},&_aggr_id0);
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
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_.getValues({});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        int C = tuple0->at(0);
                        int T = tuple0->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({T},&_thing);
                        const Tuple* tuple1 = wthing.find(*positiveTuple);
                        if(tuple1 == tupleU && tupleU == NULL){
                            tuple1 = tupleU = uthing.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_thing && ! tupleUNegated){
                            if(tupleU == uthing.find(*positiveTuple)){
                                tuple1=tupleU;
                            }
                        }
                        if(tuple1!=NULL){
                            Tuple* negativeTuple = factory.addNewInternalTuple({T,C},&_aggr_set0);
                            const Tuple* tuple2 = waggr_set0.find(*negativeTuple);
                            const Tuple* tupleUndef2 = uaggr_set0.find(*negativeTuple);
                            if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                                tuple2 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef2 != NULL){
                                tupleU = tuple2 = tupleUndef2;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set0 && tupleUNegated && tupleU==tupleUndef2){
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
        {
            {
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        int T = tuple0->at(0);
                        int C = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({T},&_thing);
                        const Tuple* tuple1 = wthing.find(*negativeTuple);
                        const Tuple* tupleUndef1 = uthing.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_thing && tupleUNegated && tupleU==tupleUndef1){
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
                const std::vector<const Tuple*>* tuples = &paggr_set0_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_.getValues({});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        int T = tuple0->at(0);
                        int C = tuple0->at(1);
                        Tuple* negativeTuple = factory.addNewInternalTuple({C,T},&_cabinetTOthing);
                        const Tuple* tuple1 = wcabinetTOthing.find(*negativeTuple);
                        const Tuple* tupleUndef1 = ucabinetTOthing.find(*negativeTuple);
                        if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                            tuple1 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef1 != NULL){
                            tupleU = tuple1 = tupleUndef1;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetTOthing && tupleUNegated && tupleU==tupleUndef1){
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
    }//close decision level == -1
    while(!propagationStack.empty()){
        int startVar = propagationStack.back();
        int uStartVar = startVar<0 ? -startVar : startVar;
        Tuple starter (*factory.getTupleFromInternalID(uStartVar));
        starter.setNegated(startVar<0);
        std::string minus = starter.isNegated() ? "not " : "";
        propagationStack.pop_back();
        {
            if(starter.getPredicateName() == &_cabinetTOthing && starter.isNegated()){
                int C = starter[0];
                int T = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({T,C},&_aggr_set0);
                const Tuple* tuple1 = waggr_set0.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_set0.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_set0 && ! tupleUNegated){
                    if(tupleU == uaggr_set0.find(*positiveTuple)){
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
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
            if(starter.getPredicateName() == &_aggr_set0 && !starter.isNegated()){
                int T = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({C,T},&_cabinetTOthing);
                const Tuple* tuple1 = wcabinetTOthing.find(*negativeTuple);
                const Tuple* tupleUndef1 = ucabinetTOthing.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetTOthing && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_thing && starter.isNegated()){
                int T = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set0_0_.getValues({T});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set0_0_.getValues({T});
                else if(tupleU->getPredicateName() == &_aggr_set0 && !tupleUNegated)
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
                        if(tupleU->at(0) == T)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int C = tuple1->at(1);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
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
            if(starter.getPredicateName() == &_aggr_set0 && !starter.isNegated()){
                int T = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({T},&_thing);
                const Tuple* tuple1 = wthing.find(*negativeTuple);
                const Tuple* tupleUndef1 = uthing.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_thing && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aggr_set0 && starter.isNegated()){
                int T = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C,T},&_cabinetTOthing);
                const Tuple* tuple1 = wcabinetTOthing.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinetTOthing.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetTOthing && ! tupleUNegated){
                    if(tupleU == ucabinetTOthing.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({T},&_thing);
                    const Tuple* tuple2 = wthing.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = uthing.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_thing && ! tupleUNegated){
                        if(tupleU == uthing.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_thing && !starter.isNegated()){
                int T = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_1_.getValues({T});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_1_.getValues({T});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        if(tupleU->at(1) == T)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int C = tuple1->at(0);
                        Tuple* negativeTuple = factory.addNewInternalTuple({T,C},&_aggr_set0);
                        const Tuple* tuple2 = waggr_set0.find(*negativeTuple);
                        const Tuple* tupleUndef2 = uaggr_set0.find(*negativeTuple);
                        if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                            tuple2 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef2 != NULL){
                            tupleU = tuple2 = tupleUndef2;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set0 && tupleUNegated && tupleU==tupleUndef2){
                            tuple2=tupleU;
                        }else if(tuple2!=NULL){
                            tuple2=NULL;
                        }
                        if(tuple2!=NULL){
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
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_cabinetTOthing && !starter.isNegated()){
                int C = starter[0];
                int T = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({T},&_thing);
                const Tuple* tuple1 = wthing.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uthing.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_thing && ! tupleUNegated){
                    if(tupleU == uthing.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* negativeTuple = factory.addNewInternalTuple({T,C},&_aggr_set0);
                    const Tuple* tuple2 = waggr_set0.find(*negativeTuple);
                    const Tuple* tupleUndef2 = uaggr_set0.find(*negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set0 && tupleUNegated && tupleU==tupleUndef2){
                        tuple2=tupleU;
                    }else if(tuple2!=NULL){
                        tuple2=NULL;
                    }
                    if(tuple2!=NULL){
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
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*-1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id0){
            int C = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set0_1_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set0_1_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=6){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 6 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 6){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set0_1_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 6){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &faggr_set0_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set0){
            const std::vector<const Tuple*>* tuples = &paggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id0_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id0_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int C = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 6){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 6){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int C = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 6){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 6 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
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
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int C = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set0_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set0_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 6){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 6){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set0_1_.getValues(sharedVar);
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
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinet);
                const Tuple* tuple1 = wcabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinet && ! tupleUNegated){
                    if(tupleU == ucabinet.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_cabinet && !starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_aggr_id0);
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_roomTOcabinet && starter.isNegated()){
                int R = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C,R},&_aggr_set1);
                const Tuple* tuple1 = waggr_set1.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_set1.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_set1 && ! tupleUNegated){
                    if(tupleU == uaggr_set1.find(*positiveTuple)){
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                            if(tuple1!=tupleU){
                                int it = tuple1->getId();
                                reasonForLiteral[var].insert(it*1);
                            }
                        }else{
                        }
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
            if(starter.getPredicateName() == &_aggr_set1 && !starter.isNegated()){
                int C = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                const Tuple* tuple1 = wroomTOcabinet.find(*negativeTuple);
                const Tuple* tupleUndef1 = uroomTOcabinet.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_roomTOcabinet && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_cabinetDomain && starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set1_0_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set1_0_.getValues({C});
                else if(tupleU->getPredicateName() == &_aggr_set1 && !tupleUNegated)
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
                        if(tupleU->at(0) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int R = tuple1->at(1);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
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
            if(starter.getPredicateName() == &_aggr_set1 && !starter.isNegated()){
                int C = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                const Tuple* tuple1 = wcabinetDomain.find(*negativeTuple);
                const Tuple* tupleUndef1 = ucabinetDomain.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetDomain && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aggr_set1 && starter.isNegated()){
                int C = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                const Tuple* tuple1 = wroomTOcabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uroomTOcabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_roomTOcabinet && ! tupleUNegated){
                    if(tupleU == uroomTOcabinet.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                    const Tuple* tuple2 = wcabinetDomain.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = ucabinetDomain.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                        if(tupleU == ucabinetDomain.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_cabinetDomain && !starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &proomTOcabinet_1_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroomTOcabinet_1_.getValues({C});
                else if(tupleU->getPredicateName() == &_roomTOcabinet && !tupleUNegated)
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
                        if(tupleU->at(1) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int R = tuple1->at(0);
                        Tuple* negativeTuple = factory.addNewInternalTuple({C,R},&_aggr_set1);
                        const Tuple* tuple2 = waggr_set1.find(*negativeTuple);
                        const Tuple* tupleUndef2 = uaggr_set1.find(*negativeTuple);
                        if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                            tuple2 = negativeTuple;
                        else if(tupleU == NULL & tupleUndef2 != NULL){
                            tupleU = tuple2 = tupleUndef2;
                            tupleUNegated=true;
                        }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set1 && tupleUNegated && tupleU==tupleUndef2){
                            tuple2=tupleU;
                        }else if(tuple2!=NULL){
                            tuple2=NULL;
                        }
                        if(tuple2!=NULL){
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
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*-1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_roomTOcabinet && !starter.isNegated()){
                int R = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                const Tuple* tuple1 = wcabinetDomain.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinetDomain.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                    if(tupleU == ucabinetDomain.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* negativeTuple = factory.addNewInternalTuple({C,R},&_aggr_set1);
                    const Tuple* tuple2 = waggr_set1.find(*negativeTuple);
                    const Tuple* tupleUndef2 = uaggr_set1.find(*negativeTuple);
                    if(tuple2 == tupleUndef2 && tupleUndef2 == NULL)
                        tuple2 = negativeTuple;
                    else if(tupleU == NULL & tupleUndef2 != NULL){
                        tupleU = tuple2 = tupleUndef2;
                        tupleUNegated=true;
                    }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set1 && tupleUNegated && tupleU==tupleUndef2){
                        tuple2=tupleU;
                    }else if(tuple2!=NULL){
                        tuple2=NULL;
                    }
                    if(tuple2!=NULL){
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
                                if(tuple2!=tupleU){
                                    int it = tuple2->getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                            }else{
                            }
                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                        }else{
                            if(tuple1!=NULL){
                                int it = tuple1->getId();
                                reasonForLiteral[-startVar].insert(it*1);
                            }
                            if(tuple2!=NULL){
                                int it = tuple2->getId();
                                reasonForLiteral[-startVar].insert(it*-1);
                            }
                            handleConflict(-startVar);
                            return;
                        }
                    }
                }
            }
        }
        if(starter.getPredicateName() == &_aggr_id1){
            int R = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set1_1_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set1_1_.getValues(sharedVar);
            if(starter.isNegated()){
                if(tuples->size()>=5){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() == 5 -1){
                    std::vector<int> reason;
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reason.push_back(it);
                    }
                    reason.push_back(startVar);
                    while(!tuplesU->empty()){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(-itProp)==0){
                            for(int reasonLit : reason)
                                reasonForLiteral[-itProp].insert(reasonLit);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }else{
                if(tuples->size()+tuplesU->size() < 5){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set1_1_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else if(tuples->size() + tuplesU->size() == 5){
                    while(tuplesU->size()>0){
                        int itProp = tuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0){
                            const std::vector<const Tuple*>* tuplesF = &faggr_set1_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < tuplesF->size(); i++){
                                int it = tuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            reasonForLiteral[itProp].insert(startVar);
                        }
                        propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set1){
            const std::vector<const Tuple*>* tuples = &paggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id1_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id1_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int R = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(joinTuples->size() + joinTuplesU->size() < 5){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else if(joinTuples->size() + joinTuplesU->size() == 5){
                    while(joinTuplesU->size()>0){
                        int itProp = joinTuplesU->at(0)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it = joinTuplesF->at(i)->getId();
                                reasonForLiteral[itProp].insert(-it);
                            }
                            int itAggrId = tuples->at(i)->getId();
                            reasonForLiteral[itProp].insert(itAggrId);
                        }
                        propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);
                    }
                }
            }//close true for
            for(unsigned i = 0; i<tuplesF->size(); i++){
                int R = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(joinTuples->size() >= 5){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else if(joinTuples->size() == 5 -1){
                    std::vector<int> reason;
                    while(!joinTuplesU->empty()){
                        int itProp = joinTuplesU->at(0)->getId();
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
                        propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int R = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set1_1_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set1_1_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(joinTuples->size() >= 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(joinTuples->size() + joinTuplesU->size() < 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set1_1_.getValues(sharedVar);
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
                int R = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R},&_room);
                const Tuple* tuple1 = wroom.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uroom.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_room && ! tupleUNegated){
                    if(tupleU == uroom.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_room && !starter.isNegated()){
                int R = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R},&_aggr_id1);
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_personTOthing && !starter.isNegated()){
                int P2 = starter[0];
                int T2 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_.getValues({});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_.getValues({});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int C = tuple1->at(0);
                        int T1 = tuple1->at(1);
                        Tuple* positiveTuple = factory.addNewInternalTuple({C,T2},&_cabinetTOthing);
                        const Tuple* tuple2 = wcabinetTOthing.find(*positiveTuple);
                        if(tuple2 == tupleU && tupleU == NULL){
                            tuple2 = tupleU = ucabinetTOthing.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_cabinetTOthing && ! tupleUNegated){
                            if(tupleU == ucabinetTOthing.find(*positiveTuple)){
                                tuple2=tupleU;
                            }
                        }
                        if(tuple2!=NULL){
                            const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T1});
                            const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                            std::vector<const Tuple*> undeRepeated;
                            if(tupleU == NULL)
                                tuplesU = &upersonTOthing_1_.getValues({T1});
                            else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                                const Tuple* tuple3 = NULL;
                                if(i<tuples->size())
                                    tuple3 = tuples->at(i);
                                else if(i<tuples->size()+tuplesU->size()){
                                    tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                    tupleUNegated=false;
                                }else if(!undeRepeated.empty()){
                                    if(tupleU->at(1) == T1)
                                        tuple3 = tupleU;
                                }
                                if(tuple3!=NULL){
                                    int P1 = tuple3->at(0);
                                    if(P1 < P2){
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
                                                if(tuple2!=tupleU){
                                                    int it = tuple2->getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                                if(tuple3!=tupleU){
                                                    int it = tuple3->getId();
                                                    reasonForLiteral[var].insert(it*1);
                                                }
                                            }else{
                                            }
                                            bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                        }else{
                                            if(tuple1!=NULL){
                                                int it = tuple1->getId();
                                                reasonForLiteral[-startVar].insert(it*1);
                                            }
                                            if(tuple2!=NULL){
                                                int it = tuple2->getId();
                                                reasonForLiteral[-startVar].insert(it*1);
                                            }
                                            if(tuple3!=NULL){
                                                int it = tuple3->getId();
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
            }
            if(starter.getPredicateName() == &_personTOthing && !starter.isNegated()){
                int P1 = starter[0];
                int T1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_1_.getValues({T1});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_1_.getValues({T1});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        if(tupleU->at(1) == T1)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int C = tuple1->at(0);
                        const std::vector<const Tuple*>* tuples = &pcabinetTOthing_0_.getValues({C});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucabinetTOthing_0_.getValues({C});
                        else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                            const Tuple* tuple2 = NULL;
                            if(i<tuples->size())
                                tuple2 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple2 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == C)
                                    tuple2 = tupleU;
                            }
                            if(tuple2!=NULL){
                                int T2 = tuple2->at(1);
                                const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T2});
                                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &upersonTOthing_1_.getValues({T2});
                                else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                                    const Tuple* tuple3 = NULL;
                                    if(i<tuples->size())
                                        tuple3 = tuples->at(i);
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == T2)
                                            tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int P2 = tuple3->at(0);
                                        if(P1 < P2){
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
                                                    if(tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        reasonForLiteral[var].insert(it*1);
                                                    }
                                                    if(tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        reasonForLiteral[var].insert(it*1);
                                                    }
                                                }else{
                                                }
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                            }else{
                                                if(tuple1!=NULL){
                                                    int it = tuple1->getId();
                                                    reasonForLiteral[-startVar].insert(it*1);
                                                }
                                                if(tuple2!=NULL){
                                                    int it = tuple2->getId();
                                                    reasonForLiteral[-startVar].insert(it*1);
                                                }
                                                if(tuple3!=NULL){
                                                    int it = tuple3->getId();
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
                }
            }
            if(starter.getPredicateName() == &_cabinetTOthing && !starter.isNegated()){
                int C = starter[0];
                int T2 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_0_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_0_.getValues({C});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        if(tupleU->at(0) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T1 = tuple1->at(1);
                        const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T1});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &upersonTOthing_1_.getValues({T1});
                        else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                            const Tuple* tuple2 = NULL;
                            if(i<tuples->size())
                                tuple2 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple2 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(1) == T1)
                                    tuple2 = tupleU;
                            }
                            if(tuple2!=NULL){
                                int P1 = tuple2->at(0);
                                const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T2});
                                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &upersonTOthing_1_.getValues({T2});
                                else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                                    const Tuple* tuple3 = NULL;
                                    if(i<tuples->size())
                                        tuple3 = tuples->at(i);
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == T2)
                                            tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int P2 = tuple3->at(0);
                                        if(P1 < P2){
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
                                                    if(tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        reasonForLiteral[var].insert(it*1);
                                                    }
                                                    if(tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        reasonForLiteral[var].insert(it*1);
                                                    }
                                                }else{
                                                }
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                            }else{
                                                if(tuple1!=NULL){
                                                    int it = tuple1->getId();
                                                    reasonForLiteral[-startVar].insert(it*1);
                                                }
                                                if(tuple2!=NULL){
                                                    int it = tuple2->getId();
                                                    reasonForLiteral[-startVar].insert(it*1);
                                                }
                                                if(tuple3!=NULL){
                                                    int it = tuple3->getId();
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
                }
            }
            if(starter.getPredicateName() == &_cabinetTOthing && !starter.isNegated()){
                int C = starter[0];
                int T1 = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &pcabinetTOthing_0_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &ucabinetTOthing_0_.getValues({C});
                else if(tupleU->getPredicateName() == &_cabinetTOthing && !tupleUNegated)
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
                        if(tupleU->at(0) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int T2 = tuple1->at(1);
                        const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T1});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &upersonTOthing_1_.getValues({T1});
                        else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                            const Tuple* tuple2 = NULL;
                            if(i<tuples->size())
                                tuple2 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple2 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(1) == T1)
                                    tuple2 = tupleU;
                            }
                            if(tuple2!=NULL){
                                int P1 = tuple2->at(0);
                                const std::vector<const Tuple*>* tuples = &ppersonTOthing_1_.getValues({T2});
                                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                                std::vector<const Tuple*> undeRepeated;
                                if(tupleU == NULL)
                                    tuplesU = &upersonTOthing_1_.getValues({T2});
                                else if(tupleU->getPredicateName() == &_personTOthing && !tupleUNegated)
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
                                    const Tuple* tuple3 = NULL;
                                    if(i<tuples->size())
                                        tuple3 = tuples->at(i);
                                    else if(i<tuples->size()+tuplesU->size()){
                                        tupleU = tuple3 = tuplesU->at(i-tuples->size());
                                        tupleUNegated=false;
                                    }else if(!undeRepeated.empty()){
                                        if(tupleU->at(1) == T2)
                                            tuple3 = tupleU;
                                    }
                                    if(tuple3!=NULL){
                                        int P2 = tuple3->at(0);
                                        if(P1 < P2){
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
                                                    if(tuple2!=tupleU){
                                                        int it = tuple2->getId();
                                                        reasonForLiteral[var].insert(it*1);
                                                    }
                                                    if(tuple3!=tupleU){
                                                        int it = tuple3->getId();
                                                        reasonForLiteral[var].insert(it*1);
                                                    }
                                                }else{
                                                }
                                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                            }else{
                                                if(tuple1!=NULL){
                                                    int it = tuple1->getId();
                                                    reasonForLiteral[-startVar].insert(it*1);
                                                }
                                                if(tuple2!=NULL){
                                                    int it = tuple2->getId();
                                                    reasonForLiteral[-startVar].insert(it*1);
                                                }
                                                if(tuple3!=NULL){
                                                    int it = tuple3->getId();
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
                }
            }
        }
        {
            if(starter.getPredicateName() == &_personTOroom && !starter.isNegated()){
                int P2 = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &ppersonTOroom_1_.getValues({R});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upersonTOroom_1_.getValues({R});
                else if(tupleU->getPredicateName() == &_personTOroom && !tupleUNegated)
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
                        if(tupleU->at(1) == R)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int P1 = tuple1->at(0);
                        if(P1 < P2){
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
                                }else{
                                }
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
            if(starter.getPredicateName() == &_personTOroom && !starter.isNegated()){
                int P1 = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &ppersonTOroom_1_.getValues({R});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &upersonTOroom_1_.getValues({R});
                else if(tupleU->getPredicateName() == &_personTOroom && !tupleUNegated)
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
                        if(tupleU->at(1) == R)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int P2 = tuple1->at(0);
                        if(P1 < P2){
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
                                }else{
                                }
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
        {
            if(starter.getPredicateName() == &_thingShort && !starter.isNegated()){
                int T = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({T},&_thingLong);
                const Tuple* tuple1 = wthingLong.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uthingLong.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_thingLong && ! tupleUNegated){
                    if(tupleU == uthingLong.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_thingLong && !starter.isNegated()){
                int T = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({T},&_thingShort);
                const Tuple* tuple1 = wthingShort.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uthingShort.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_thingShort && ! tupleUNegated){
                    if(tupleU == uthingShort.find(*positiveTuple)){
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_roomTOcabinet && starter.isNegated()){
                int R = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set2_1_2_.getValues({C,R});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set2_1_2_.getValues({C,R});
                else if(tupleU->getPredicateName() == &_aggr_set2 && !tupleUNegated)
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
                        if(tupleU->at(1) == C && tupleU->at(2) == R)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int S = tuple1->at(0);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
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
            if(starter.getPredicateName() == &_aggr_set2 && !starter.isNegated()){
                int S = starter[0];
                int C = starter[1];
                int R = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                const Tuple* tuple1 = wroomTOcabinet.find(*negativeTuple);
                const Tuple* tupleUndef1 = uroomTOcabinet.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_roomTOcabinet && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_cabinetSize && starter.isNegated()){
                int C = starter[0];
                int S = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set2_0_1_.getValues({S,C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set2_0_1_.getValues({S,C});
                else if(tupleU->getPredicateName() == &_aggr_set2 && !tupleUNegated)
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
                        if(tupleU->at(0) == S && tupleU->at(1) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int R = tuple1->at(2);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
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
            if(starter.getPredicateName() == &_aggr_set2 && !starter.isNegated()){
                int S = starter[0];
                int C = starter[1];
                int R = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({C,S},&_cabinetSize);
                const Tuple* tuple1 = wcabinetSize.find(*negativeTuple);
                const Tuple* tupleUndef1 = ucabinetSize.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetSize && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_cabinetDomain && starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &paggr_set2_1_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uaggr_set2_1_.getValues({C});
                else if(tupleU->getPredicateName() == &_aggr_set2 && !tupleUNegated)
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
                        if(tupleU->at(1) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int S = tuple1->at(0);
                        int R = tuple1->at(2);
                        if(tupleU != NULL){
                            int itUndef = tupleU->getId();
                            int var = tupleUNegated ? 1 : -1;
                            var*=itUndef;
                            if(reasonForLiteral.count(var) == 0){
                                {
                                    int it = starter.getId();
                                    reasonForLiteral[var].insert(it*-1);
                                }
                                if(tuple1!=tupleU){
                                    int it = tuple1->getId();
                                    reasonForLiteral[var].insert(it*1);
                                }
                            }else{
                            }
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
            if(starter.getPredicateName() == &_aggr_set2 && !starter.isNegated()){
                int S = starter[0];
                int C = starter[1];
                int R = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* negativeTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                const Tuple* tuple1 = wcabinetDomain.find(*negativeTuple);
                const Tuple* tupleUndef1 = ucabinetDomain.find(*negativeTuple);
                if(tuple1 == tupleUndef1 && tupleUndef1 == NULL)
                    tuple1 = negativeTuple;
                else if(tupleU == NULL & tupleUndef1 != NULL){
                    tupleU = tuple1 = tupleUndef1;
                    tupleUNegated=true;
                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_cabinetDomain && tupleUNegated && tupleU==tupleUndef1){
                    tuple1=tupleU;
                }else if(tuple1!=NULL){
                    tuple1=NULL;
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
                                reasonForLiteral[var].insert(it*-1);
                            }
                        }else{
                        }
                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                    }else{
                        if(tuple1!=NULL){
                            int it = tuple1->getId();
                            reasonForLiteral[-startVar].insert(it*-1);
                        }
                        handleConflict(-startVar);
                        return;
                    }
                }
            }
        }
        {
            if(starter.getPredicateName() == &_aggr_set2 && starter.isNegated()){
                int S = starter[0];
                int C = starter[1];
                int R = starter[2];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                const Tuple* tuple1 = wroomTOcabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uroomTOcabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_roomTOcabinet && ! tupleUNegated){
                    if(tupleU == uroomTOcabinet.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    Tuple* positiveTuple = factory.addNewInternalTuple({C,S},&_cabinetSize);
                    const Tuple* tuple2 = wcabinetSize.find(*positiveTuple);
                    if(tuple2 == tupleU && tupleU == NULL){
                        tuple2 = tupleU = ucabinetSize.find(*positiveTuple);
                        tupleUNegated=false;
                    }else if(tupleU!=NULL && tuple2==NULL && tupleU->getPredicateName() == &_cabinetSize && ! tupleUNegated){
                        if(tupleU == ucabinetSize.find(*positiveTuple)){
                            tuple2=tupleU;
                        }
                    }
                    if(tuple2!=NULL){
                        Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                        const Tuple* tuple3 = wcabinetDomain.find(*positiveTuple);
                        if(tuple3 == tupleU && tupleU == NULL){
                            tuple3 = tupleU = ucabinetDomain.find(*positiveTuple);
                            tupleUNegated=false;
                        }else if(tupleU!=NULL && tuple3==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                            if(tupleU == ucabinetDomain.find(*positiveTuple)){
                                tuple3=tupleU;
                            }
                        }
                        if(tuple3!=NULL){
                            if(tupleU != NULL){
                                int itUndef = tupleU->getId();
                                int var = tupleUNegated ? 1 : -1;
                                var*=itUndef;
                                if(reasonForLiteral.count(var) == 0){
                                    {
                                        int it = starter.getId();
                                        reasonForLiteral[var].insert(it*-1);
                                    }
                                    if(tuple1!=tupleU){
                                        int it = tuple1->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple2!=tupleU){
                                        int it = tuple2->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                    if(tuple3!=tupleU){
                                        int it = tuple3->getId();
                                        reasonForLiteral[var].insert(it*1);
                                    }
                                }else{
                                }
                                bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                            }else{
                                if(tuple1!=NULL){
                                    int it = tuple1->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple2!=NULL){
                                    int it = tuple2->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                if(tuple3!=NULL){
                                    int it = tuple3->getId();
                                    reasonForLiteral[-startVar].insert(it*1);
                                }
                                handleConflict(-startVar);
                                return;
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_cabinetDomain && !starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                const std::vector<const Tuple*>* tuples = &proomTOcabinet_1_.getValues({C});
                const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                std::vector<const Tuple*> undeRepeated;
                if(tupleU == NULL)
                    tuplesU = &uroomTOcabinet_1_.getValues({C});
                else if(tupleU->getPredicateName() == &_roomTOcabinet && !tupleUNegated)
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
                        if(tupleU->at(1) == C)
                            tuple1 = tupleU;
                    }
                    if(tuple1!=NULL){
                        int R = tuple1->at(0);
                        const std::vector<const Tuple*>* tuples = &pcabinetSize_0_.getValues({C});
                        const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                        std::vector<const Tuple*> undeRepeated;
                        if(tupleU == NULL)
                            tuplesU = &ucabinetSize_0_.getValues({C});
                        else if(tupleU->getPredicateName() == &_cabinetSize && !tupleUNegated)
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
                            const Tuple* tuple2 = NULL;
                            if(i<tuples->size())
                                tuple2 = tuples->at(i);
                            else if(i<tuples->size()+tuplesU->size()){
                                tupleU = tuple2 = tuplesU->at(i-tuples->size());
                                tupleUNegated=false;
                            }else if(!undeRepeated.empty()){
                                if(tupleU->at(0) == C)
                                    tuple2 = tupleU;
                            }
                            if(tuple2!=NULL){
                                int S = tuple2->at(1);
                                Tuple* negativeTuple = factory.addNewInternalTuple({S,C,R},&_aggr_set2);
                                const Tuple* tuple3 = waggr_set2.find(*negativeTuple);
                                const Tuple* tupleUndef3 = uaggr_set2.find(*negativeTuple);
                                if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                    tuple3 = negativeTuple;
                                else if(tupleU == NULL & tupleUndef3 != NULL){
                                    tupleU = tuple3 = tupleUndef3;
                                    tupleUNegated=true;
                                }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set2 && tupleUNegated && tupleU==tupleUndef3){
                                    tuple3=tupleU;
                                }else if(tuple3!=NULL){
                                    tuple3=NULL;
                                }
                                if(tuple3!=NULL){
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
                                            if(tuple2!=tupleU){
                                                int it = tuple2->getId();
                                                reasonForLiteral[var].insert(it*1);
                                            }
                                            if(tuple3!=tupleU){
                                                int it = tuple3->getId();
                                                reasonForLiteral[var].insert(it*-1);
                                            }
                                        }else{
                                        }
                                        bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                    }else{
                                        if(tuple1!=NULL){
                                            int it = tuple1->getId();
                                            reasonForLiteral[-startVar].insert(it*1);
                                        }
                                        if(tuple2!=NULL){
                                            int it = tuple2->getId();
                                            reasonForLiteral[-startVar].insert(it*1);
                                        }
                                        if(tuple3!=NULL){
                                            int it = tuple3->getId();
                                            reasonForLiteral[-startVar].insert(it*-1);
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
            if(starter.getPredicateName() == &_cabinetSize && !starter.isNegated()){
                int C = starter[0];
                int S = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                const Tuple* tuple1 = wcabinetDomain.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinetDomain.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                    if(tupleU == ucabinetDomain.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    const std::vector<const Tuple*>* tuples = &proomTOcabinet_1_.getValues({C});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &uroomTOcabinet_1_.getValues({C});
                    else if(tupleU->getPredicateName() == &_roomTOcabinet && !tupleUNegated)
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
                        const Tuple* tuple2 = NULL;
                        if(i<tuples->size())
                            tuple2 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple2 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            if(tupleU->at(1) == C)
                                tuple2 = tupleU;
                        }
                        if(tuple2!=NULL){
                            int R = tuple2->at(0);
                            Tuple* negativeTuple = factory.addNewInternalTuple({S,C,R},&_aggr_set2);
                            const Tuple* tuple3 = waggr_set2.find(*negativeTuple);
                            const Tuple* tupleUndef3 = uaggr_set2.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set2 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
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
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
                                    }
                                    handleConflict(-startVar);
                                    return;
                                }
                            }
                        }
                    }
                }
            }
            if(starter.getPredicateName() == &_roomTOcabinet && !starter.isNegated()){
                int R = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinetDomain);
                const Tuple* tuple1 = wcabinetDomain.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinetDomain.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetDomain && ! tupleUNegated){
                    if(tupleU == ucabinetDomain.find(*positiveTuple)){
                        tuple1=tupleU;
                    }
                }
                if(tuple1!=NULL){
                    const std::vector<const Tuple*>* tuples = &pcabinetSize_0_.getValues({C});
                    const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;
                    std::vector<const Tuple*> undeRepeated;
                    if(tupleU == NULL)
                        tuplesU = &ucabinetSize_0_.getValues({C});
                    else if(tupleU->getPredicateName() == &_cabinetSize && !tupleUNegated)
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
                        const Tuple* tuple2 = NULL;
                        if(i<tuples->size())
                            tuple2 = tuples->at(i);
                        else if(i<tuples->size()+tuplesU->size()){
                            tupleU = tuple2 = tuplesU->at(i-tuples->size());
                            tupleUNegated=false;
                        }else if(!undeRepeated.empty()){
                            if(tupleU->at(0) == C)
                                tuple2 = tupleU;
                        }
                        if(tuple2!=NULL){
                            int S = tuple2->at(1);
                            Tuple* negativeTuple = factory.addNewInternalTuple({S,C,R},&_aggr_set2);
                            const Tuple* tuple3 = waggr_set2.find(*negativeTuple);
                            const Tuple* tupleUndef3 = uaggr_set2.find(*negativeTuple);
                            if(tuple3 == tupleUndef3 && tupleUndef3 == NULL)
                                tuple3 = negativeTuple;
                            else if(tupleU == NULL & tupleUndef3 != NULL){
                                tupleU = tuple3 = tupleUndef3;
                                tupleUNegated=true;
                            }else if(tupleU!=NULL && tupleU->getPredicateName() == &_aggr_set2 && tupleUNegated && tupleU==tupleUndef3){
                                tuple3=tupleU;
                            }else if(tuple3!=NULL){
                                tuple3=NULL;
                            }
                            if(tuple3!=NULL){
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
                                        if(tuple2!=tupleU){
                                            int it = tuple2->getId();
                                            reasonForLiteral[var].insert(it*1);
                                        }
                                        if(tuple3!=tupleU){
                                            int it = tuple3->getId();
                                            reasonForLiteral[var].insert(it*-1);
                                        }
                                    }else{
                                    }
                                    bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);
                                }else{
                                    if(tuple1!=NULL){
                                        int it = tuple1->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple2!=NULL){
                                        int it = tuple2->getId();
                                        reasonForLiteral[-startVar].insert(it*1);
                                    }
                                    if(tuple3!=NULL){
                                        int it = tuple3->getId();
                                        reasonForLiteral[-startVar].insert(it*-1);
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
        if(starter.getPredicateName() == &_aggr_id2){
            int R = starter[0];
            std::vector<int> sharedVar({starter[0]});
            const std::vector<const Tuple*>* tuples = &paggr_set2_2_.getValues(sharedVar);
            const std::vector<const Tuple*>* tuplesU = &uaggr_set2_2_.getValues(sharedVar);
            if(starter.isNegated()){
                if(actualSum[uStartVar]>=5){
                    for(unsigned i =0; i< tuples->size(); i++){
                        int it = tuples->at(i)->getId();
                        reasonForLiteral[-startVar].insert(it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    std::vector<int> reason;
                    for(int index=0; index<tuplesU->size();){
                        if(actualSum[uStartVar]+tuplesU->at(index)->at(0) >= 5){
                            int itProp =tuplesU->at(index)->getId();
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
                        }else index++;
                    }
                }
            }else{
                if(actualSum[uStartVar]+possibleSum[uStartVar] < 5){
                    const std::vector<const Tuple*>* tuplesF = &faggr_set2_2_.getValues(sharedVar);
                    for(unsigned i = 0; i < tuplesF->size(); i++){
                        int it = tuplesF->at(i)->getId();
                        reasonForLiteral[-startVar].insert(-it);
                    }
                    handleConflict(-startVar);
                    return;
                }else{
                    for(unsigned index=0;index<tuplesU->size();){
                        if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at(0) < 5){
                            int itProp = tuplesU->at(index)->getId();
                            if(reasonForLiteral.count(itProp) == 0){
                                const std::vector<const Tuple*>* tuplesF = &faggr_set2_2_.getValues(sharedVar);
                                for(unsigned i = 0; i < tuplesF->size(); i++){
                                    int it = tuplesF->at(i)->getId();
                                    reasonForLiteral[itProp].insert(-it);
                                }
                                reasonForLiteral[itProp].insert(startVar);
                            }
                            propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);
                        }else index++;
                    }
                }
            }
        }//close aggr id starter
        if(starter.getPredicateName() == &_aggr_set2){
            const std::vector<const Tuple*>* tuples = &paggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesU = &uaggr_id2_.getValues({});
            const std::vector<const Tuple*>* tuplesF = &faggr_id2_.getValues({});
            for(unsigned i = 0; i<tuples->size(); i++){
                int R = tuples->at(i)->at(0);
                std::vector<int> sharedVar({tuples->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set2_2_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set2_2_.getValues(sharedVar);
                int aggrIdIt=tuples->at(i)->getId();
                if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < 5){
                    int itProp = tuples->at(i)->getId();
                    const std::vector<const Tuple*>* joinTuplesF = &faggr_set2_2_.getValues(sharedVar);
                    for(unsigned j = 0; j < joinTuplesF->size(); j++){
                        int it = joinTuplesF->at(j)->getId();
                        reasonForLiteral[-itProp].insert(-it);
                    }
                    handleConflict(-itProp);
                    return;
                }else{
                    for(unsigned index=0; index<joinTuplesU->size();){
                        if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= 5) {index++; continue;}
                        int itProp = joinTuplesU->at(index)->getId();
                        if(reasonForLiteral.count(itProp) == 0 ){
                            const std::vector<const Tuple*>* joinTuplesF = &faggr_set2_2_.getValues(sharedVar);
                            for(unsigned i = 0; i < joinTuplesF->size(); i++){
                                int it =joinTuplesF->at(i)->getId();
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
                int R = tuplesF->at(i)->at(0);
                std::vector<int> sharedVar({tuplesF->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set2_2_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set2_2_.getValues(sharedVar);
                int aggrIdIt=tuplesF->at(i)->getId();
                if(actualSum[aggrIdIt] >= 5){
                    int itProp = tuplesF->at(i)->getId();
                    for(unsigned j =0; j< joinTuples->size(); j++){
                        int it = joinTuples->at(j)->getId();
                        reasonForLiteral[itProp].insert(it);
                    }
                    handleConflict(itProp);
                    return;
                }else{
                    std::vector<int> reason;
                    for(unsigned index=0;index<joinTuplesU->size();){
                        int itProp = joinTuplesU->at(index)->getId();
                        if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= 5){
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
                        }else index++;
                    }
                }
            }//close false for
            for(unsigned i = 0; i<tuplesU->size();){
                int R = tuplesU->at(i)->at(0);
                std::vector<int> sharedVar({tuplesU->at(i)->at(0)});
                const std::vector<const Tuple*>* joinTuples = &paggr_set2_2_.getValues(sharedVar);
                const std::vector<const Tuple*>* joinTuplesU = &uaggr_set2_2_.getValues(sharedVar);
                int aggrIdIt=tuplesU->at(i)->getId();
                if(actualSum[aggrIdIt] >= 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(itProp) == 0 ){
                        for(unsigned j = 0; j < joinTuples->size(); j++){
                            int it = joinTuples->at(j)->getId();
                            reasonForLiteral[itProp].insert(it);
                        }
                    }
                    propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);
                }else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < 5){
                    int itProp = tuplesU->at(i)->getId();
                    if(reasonForLiteral.count(-itProp) == 0 ){
                        const std::vector<const Tuple*>* joinTuplesF = &faggr_set2_2_.getValues(sharedVar);
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
            if(starter.getPredicateName() == &_aggr_id2 && !starter.isNegated()){
                int R = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R},&_room);
                const Tuple* tuple1 = wroom.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uroom.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_room && ! tupleUNegated){
                    if(tupleU == uroom.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_room && !starter.isNegated()){
                int R = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R},&_aggr_id2);
                const Tuple* tuple1 = waggr_id2.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uaggr_id2.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_aggr_id2 && ! tupleUNegated){
                    if(tupleU == uaggr_id2.find(*positiveTuple)){
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_delete_cabinetTOthing && !starter.isNegated()){
                int C = starter[0];
                int T = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C,T},&_cabinetTOthing);
                const Tuple* tuple1 = wcabinetTOthing.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinetTOthing.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinetTOthing && ! tupleUNegated){
                    if(tupleU == ucabinetTOthing.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_cabinetTOthing && !starter.isNegated()){
                int C = starter[0];
                int T = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C,T},&_delete_cabinetTOthing);
                const Tuple* tuple1 = wdelete_cabinetTOthing.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = udelete_cabinetTOthing.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_cabinetTOthing && ! tupleUNegated){
                    if(tupleU == udelete_cabinetTOthing.find(*positiveTuple)){
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_delete_roomTOcabinet && !starter.isNegated()){
                int R = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R,C},&_roomTOcabinet);
                const Tuple* tuple1 = wroomTOcabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uroomTOcabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_roomTOcabinet && ! tupleUNegated){
                    if(tupleU == uroomTOcabinet.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_roomTOcabinet && !starter.isNegated()){
                int R = starter[0];
                int C = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R,C},&_delete_roomTOcabinet);
                const Tuple* tuple1 = wdelete_roomTOcabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = udelete_roomTOcabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_roomTOcabinet && ! tupleUNegated){
                    if(tupleU == udelete_roomTOcabinet.find(*positiveTuple)){
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_delete_personTOroom && !starter.isNegated()){
                int P = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({P,R},&_personTOroom);
                const Tuple* tuple1 = wpersonTOroom.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = upersonTOroom.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_personTOroom && ! tupleUNegated){
                    if(tupleU == upersonTOroom.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_personTOroom && !starter.isNegated()){
                int P = starter[0];
                int R = starter[1];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({P,R},&_delete_personTOroom);
                const Tuple* tuple1 = wdelete_personTOroom.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = udelete_personTOroom.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_personTOroom && ! tupleUNegated){
                    if(tupleU == udelete_personTOroom.find(*positiveTuple)){
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_delete_cabinet && !starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_cabinet);
                const Tuple* tuple1 = wcabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = ucabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_cabinet && ! tupleUNegated){
                    if(tupleU == ucabinet.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_cabinet && !starter.isNegated()){
                int C = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({C},&_delete_cabinet);
                const Tuple* tuple1 = wdelete_cabinet.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = udelete_cabinet.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_cabinet && ! tupleUNegated){
                    if(tupleU == udelete_cabinet.find(*positiveTuple)){
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
                        }else{
                        }
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
        {
            if(starter.getPredicateName() == &_delete_room && !starter.isNegated()){
                int R = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R},&_room);
                const Tuple* tuple1 = wroom.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = uroom.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_room && ! tupleUNegated){
                    if(tupleU == uroom.find(*positiveTuple)){
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
                        }else{
                        }
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
            if(starter.getPredicateName() == &_room && !starter.isNegated()){
                int R = starter[0];
                const Tuple* tupleU = NULL;
                bool tupleUNegated = false;
                Tuple* positiveTuple = factory.addNewInternalTuple({R},&_delete_room);
                const Tuple* tuple1 = wdelete_room.find(*positiveTuple);
                if(tuple1 == tupleU && tupleU == NULL){
                    tuple1 = tupleU = udelete_room.find(*positiveTuple);
                    tupleUNegated=false;
                }else if(tupleU!=NULL && tuple1==NULL && tupleU->getPredicateName() == &_delete_room && ! tupleUNegated){
                    if(tupleU == udelete_room.find(*positiveTuple)){
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
                        }else{
                        }
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
