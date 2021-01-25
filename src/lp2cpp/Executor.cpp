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

typedef TupleWithoutReasons Tuple;
typedef AuxiliaryMap<Tuple> AuxMap;
typedef std::vector<const Tuple* > Tuples;
using PredicateWSet = PredicateSet<Tuple, TuplesHash>;

std::unordered_map<const std::string*, PredicateWSet*> predicateWSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateFSetMap;
std::unordered_map<const std::string*, PredicateWSet*> predicateUSetMap;
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars[0];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars[0];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueNegativeAggrVars[0];
std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefNegativeAggrVars[0];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> maxPossibleNegativeSum[0];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason[0];
std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason[0];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> actualSum[0];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleSum[0];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> actualNegativeSum[0];
std::unordered_map<std::vector<int>, unsigned int,TuplesHash> possibleNegativeSum[0];
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
//printing aux maps needed for reasons of negative literals;
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
    std::cout<<"Negative aggr reason: "<<negativeAggrReason[0][{}].size()<<std::endl;
    std::cout<<"Positive aggr reason: "<<positiveAggrReason[0][{}].size()<<std::endl;
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
    std::cout<<"Unde "<<minus<<var<<std::endl;
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
    std::cout<<"Negative Reason size: "<<negativeAggrReason[0][{}].size()<<std::endl;
    std::cout<<"Positive Reason size: "<<positiveAggrReason[0][{}].size()<<std::endl;
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
}
void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}
void Executor::executeProgramOnFacts(const std::vector<int> & facts) {
    int decisionLevel = facts[0];
    clearPropagations();
    for(unsigned i=1;i<facts.size();i++) {
        onLiteralTrue(facts[i]);
    }
    if(decisionLevel==-1) {
    }//close decision level == -1
    for(unsigned i=1;i<facts.size();i++) {
        unsigned factVar = facts[i] > 0 ? facts[i] : -facts[i];
        Tuple starter = atomsTable[factVar];
        starter.setNegated(facts[i]<0);
    }
}
}
