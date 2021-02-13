/*
 *
 *  Copyright 2016 Bernardo Cuteri, Alessandro De Rosis, Francesco Ricca.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */

#include "language/Rule.h"
#include "CompilationManager.h"
#include "utils/Indentation.h"
#include "utils/SharedFunctions.h"
#include <ostream>
#include <fstream>
#include <cassert>
#include <set>
#include <list>
#include <unordered_map>
#include "DLV2libs/input/InputDirector.h"
#include "parsing/AspCore2ProgramBuilder.h"
#include "language/ArithmeticExpression.h"
#include "language/ArithmeticRelation.h"
#include "language/ArithmeticRelationWithAggregate.h"
#include "datastructures/BoundAnnotatedLiteral.h"
#include <algorithm>
using namespace std;

const std::string tab = "    ";

CompilationManager::CompilationManager(int mode) : out(&std::cout), ind(0) {
    this->mode = mode;

}

void CompilationManager::setOutStream(std::ostream* outputTarget) {
    this->out = outputTarget;
}

void CompilationManager::lp2cpp() {

    generateStratifiedCompilableProgram(builder->getProgram(), builder);
    delete builder;
}

void CompilationManager::loadProgram(const std::string& filename) {
    DLV2::InputDirector director;
    builder = new AspCore2ProgramBuilder();
    director.configureBuilder(builder);
    std::vector<const char*> fileNames;
    fileNames.push_back(filename.c_str());
    director.parse(fileNames);
    bodyPredicates = builder->getProgram().getBodyPredicates();
    headPredicates = builder->getProgram().getHeadPredicates();

}

void CompilationManager::initRuleBoundVariables(std::unordered_set<std::string> & ruleBoundVariables, const BoundAnnotatedLiteral & lit, const aspc::Atom & head, bool printVariablesDeclaration) {
    unsigned counter = 0;
    for (unsigned i = 0; i < lit.getBoundIndexes().size(); i++) {
        if (lit.getBoundIndexes().at(i) && head.isVariableTermAt(i)) {
            if (printVariablesDeclaration && !ruleBoundVariables.count(head.getTermAt(i))) {
                *out << ind << "int " << head.getTermAt(i) << " = " << "lit[" << counter << "];\n";
            }
            ruleBoundVariables.insert(head.getTermAt(i));
            counter++;
        }
    }
}

bool possiblyAddToProcessLiteral(const BoundAnnotatedLiteral & lit, list<BoundAnnotatedLiteral> & toProcessLiterals,
        list<BoundAnnotatedLiteral> & processedLiterals) {
    if (find(toProcessLiterals.begin(), toProcessLiterals.end(), lit) == toProcessLiterals.end()) {
        if (find(processedLiterals.begin(), processedLiterals.end(), lit) == processedLiterals.end()) {
            toProcessLiterals.push_back(lit);
            return true;
        }
    }
    return false;
}

void CompilationManager::writeNegativeReasonsFunctions(const aspc::Program & program, const BoundAnnotatedLiteral & lit,
        list<BoundAnnotatedLiteral> & toProcessLiterals, list<BoundAnnotatedLiteral> & processedLiterals, std::unordered_map <std::string, std::string> & functionsMap) {

    if (lit.isNegated()) {
        *out << ind++ << "void explain_" << lit.getStringRep() << "(const std::vector<int> & lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output){\n";
        if (lit.isGround()) {

            functionsMap[lit.getPredicateName()] = "explain_" + lit.getStringRep();
        }
        if (modelGeneratorPredicates.count(lit.getPredicateName())) {
            if (lit.isGround()) {
                *out << ind << "const auto& find = neg_w" << lit.getPredicateName() << ".find(Tuple(lit, &_" << lit.getPredicateName() << "));\n";
                *out << ind++ << "if(find) {\n";
                *out << ind << "output.push_back(find);\n";
                *out << --ind << "}\n";
            } else {
                //iterate over map of negatives
                std::string mapName = "false_p" + lit.getPredicateName() + "_";
                for (unsigned i = 0; i < lit.getBoundIndexes().size(); i++) {
                    if (lit.getBoundIndexes()[i]) {
                        mapName += std::to_string(i) + "_";
                    }
                }
                *out << ind++ << "for(const Tuple* reason: " << mapName << ".getValues(lit)) {\n";
                *out << ind << "output.push_back(reason);\n";
                *out << --ind << "}\n";
            }
            *out << --ind << "}\n";
            return;

        }

        *out << ind << "std::string canonicalRep = _" << lit.getPredicateName() << ";\n";
        unsigned counter = 0;
        for (unsigned i = 0; i < lit.getBoundIndexes().size(); i++) {
            if (i > 0) {
                *out << ind << "canonicalRep += \",\";\n";
            }
            if (lit.getBoundIndexes()[i]) {
                *out << ind << "canonicalRep += std::to_string(lit[" << counter++ << "]);\n";
            } else {
                *out << ind << "canonicalRep += \"_\";\n";
            }
        }

        *out << ind++ << "if(open_set.find(canonicalRep)!=open_set.end()){\n";
        *out << ind << "return;\n";
        *out << --ind << "}\n";
        *out << ind << "open_set.insert(canonicalRep);\n";


    }

    for (const aspc::Rule & r : program.getRules()) {
        //TODO runtime unification
        if (!r.isConstraint() && lit.getPredicateName() == r.getHead()[0].getPredicateName()) {
            if (lit.isNegated()) {
                *out << ind++ << "{\n";
            }
            unsigned forCounter = 0;
            std::unordered_set<std::string> ruleBoundVariables;
            const aspc::Atom & head = r.getHead()[0];
            initRuleBoundVariables(ruleBoundVariables, lit, head, lit.isNegated());
            std::vector<const aspc::Formula*> orderedFormulas = r.getOrderedBodyForReasons(ruleBoundVariables);
            for (unsigned i = 0; i < r.getBodySize(); i++) {
                const aspc::Formula * f = orderedFormulas[i];
                if (f -> isLiteral()) {
                    const aspc::Literal * bodyLit = (const aspc::Literal *) f;
                    if (lit.isNegated()) {
                        if (!bodyLit->isNegated()) {
                            std::vector<bool> coveredMask;
                            bodyLit->getAtom().getBoundTermsMask(ruleBoundVariables, coveredMask);
                            BoundAnnotatedLiteral bodyBoundLit = BoundAnnotatedLiteral(bodyLit->getPredicateName(), coveredMask, true);
                            possiblyAddToProcessLiteral(bodyBoundLit, toProcessLiterals, processedLiterals);

                            *out << ind << "explain_" << bodyBoundLit.getStringRep() << "({";
                            printLiteralTuple(bodyLit, coveredMask);

                            *out << "}, open_set, output);\n";
                            if (i < r.getBodySize() - 1) {
                                std::string mapVariableName = bodyLit->getPredicateName() + "_";
                                for (unsigned index = 0; index < coveredMask.size(); index++) {
                                    if (bodyBoundLit.getBoundIndexes()[index]) {
                                        mapVariableName += std::to_string(index) + "_";
                                    }
                                }
                                if (bodyBoundLit.isGround()) {
                                    *out << ind++ << "if (w" << bodyLit->getPredicateName() << ".find({";
                                    printLiteralTuple(bodyLit);
                                    *out << "})){\n";
                                } else {
                                    *out << ind++ << "for(const Tuple* tuple" << i << ": p" << mapVariableName << ".getValues({";
                                    printLiteralTuple(bodyLit, coveredMask);
                                    *out << "})){\n";
                                    for (unsigned index = 0; index < coveredMask.size(); index++) {
                                        if (!coveredMask[index]) {
                                            *out << ind << "int " << bodyLit->getTermAt(index) << " = " << "(*tuple" << i << ")[" << index << "];\n";
                                        }
                                    }
                                }

                                forCounter++;
                            }

                            //declareDataStructuresForReasonsOfNegative(program, *bodyLit, true, ruleBoundVariables, openSet);
                        } else {
                            BoundAnnotatedLiteral bodyBoundLit = BoundAnnotatedLiteral(bodyLit->getPredicateName(), std::vector<bool>(bodyLit->getAriety(), true), false);
                            possiblyAddToProcessLiteral(bodyBoundLit, toProcessLiterals, processedLiterals);
                            *out << ind << "const auto & it = w" << bodyLit->getPredicateName() << ".find({";
                            for (unsigned term = 0; term < bodyLit->getAriety(); term++) {
                                if (term > 0) {
                                    *out << ",";
                                }
                                if (!bodyLit->isVariableTermAt(term)) {
                                    *out << "ConstantsManager::getInstance().mapConstant(\"" << escapeDoubleQuotes(bodyLit->getTermAt(term)) << "\")";
                                } else {
                                    *out << bodyLit->getTermAt(term);
                                }
                            }
                            *out << "});\n";
                            *out << ind++ << "if(it) {\n";
                            *out << ind << "explainPositiveLiteral(it, open_set, output);\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else {\n";

                            forCounter++;
                        }
                    } else {
                        if (bodyLit->isNegated()) {
                            BoundAnnotatedLiteral bodyBoundLit = BoundAnnotatedLiteral(bodyLit->getPredicateName(), std::vector<bool>(bodyLit->getAriety(), true), true);
                            possiblyAddToProcessLiteral(bodyBoundLit, toProcessLiterals, processedLiterals);
                        }
                    }
                    for (unsigned t = 0; t < bodyLit->getAriety(); t++) {
                        if (bodyLit -> isVariableTermAt(t)) {
                            ruleBoundVariables.insert(bodyLit->getTermAt(t));
                        }
                    }
                } else {
                    //account value invention relations
                    if (lit.isNegated()) {
                        const aspc::ArithmeticRelation * relation = (const aspc::ArithmeticRelation *) f;
                        if (f->isBoundedValueAssignment(ruleBoundVariables)) {
                            *out << ind << "int " << relation->getAssignmentStringRep(ruleBoundVariables) << ";\n";
                            ruleBoundVariables.insert(relation->getAssignedVariable(ruleBoundVariables));
                        } else {
                            *out << ind++ << "if(" << relation->getStringRep() << ") {\n";
                            forCounter++;
                        }
                    }

                }
            }
            for (unsigned i = 0; i < forCounter; i++) {
                *out << --ind << "}\n";
            }
            if (lit.isNegated()) {
                *out << --ind << "}\n";
            }
        }
    }
    if (lit.isNegated()) {
        *out << ind << "open_set.erase(canonicalRep);\n";
        *out << --ind << "}\n";
    }
}

void CompilationManager::writeNegativeReasonsFunctionsPrototypes(const aspc::Program & program, const BoundAnnotatedLiteral & lit,
        list<BoundAnnotatedLiteral> & toProcessLiterals, list<BoundAnnotatedLiteral> & processedLiterals, std::unordered_map <std::string, std::string> & functionsMap) {


    if (lit.isNegated()) {
        *out << ind << "void explain_" << lit.getStringRep() << "(const std::vector<int> &, std::unordered_set<std::string> &, std::vector<const Tuple *> &);\n";
        if (modelGeneratorPredicates.count(lit.getPredicateName())) {
            return;
        }
    }
    for (const aspc::Rule & r : program.getRules()) {
        //TODO runtime unification
        if (!r.isConstraint() && lit.getPredicateName() == r.getHead()[0].getPredicateName()) {
            std::unordered_set<std::string> ruleBoundVariables;
            const aspc::Atom & head = r.getHead()[0];
            initRuleBoundVariables(ruleBoundVariables, lit, head, false);
            std::vector<const aspc::Formula*> orderedFormulas = r.getOrderedBodyForReasons(ruleBoundVariables);
            for (unsigned i = 0; i < r.getBodySize(); i++) {
                const aspc::Formula * f = orderedFormulas[i];
                if (f -> isLiteral()) {
                    const aspc::Literal * bodyLit = (const aspc::Literal *) f;
                    if (lit.isNegated()) {
                        if (!bodyLit->isNegated()) {
                            std::vector<bool> coveredMask;
                            bodyLit->getAtom().getBoundTermsMask(ruleBoundVariables, coveredMask);
                            BoundAnnotatedLiteral bodyBoundLit = BoundAnnotatedLiteral(bodyLit->getPredicateName(), coveredMask, true);
                            possiblyAddToProcessLiteral(bodyBoundLit, toProcessLiterals, processedLiterals);
                        } else {
                            BoundAnnotatedLiteral bodyBoundLit = BoundAnnotatedLiteral(bodyLit->getPredicateName(), std::vector<bool>(bodyLit->getAriety(), true), false);
                            possiblyAddToProcessLiteral(bodyBoundLit, toProcessLiterals, processedLiterals);
                        }
                    } else {
                        if (bodyLit->isNegated()) {
                            BoundAnnotatedLiteral bodyBoundLit = BoundAnnotatedLiteral(bodyLit->getPredicateName(), std::vector<bool>(bodyLit->getAriety(), true), true);
                            possiblyAddToProcessLiteral(bodyBoundLit, toProcessLiterals, processedLiterals);
                        }
                    }
                    for (unsigned t = 0; t < bodyLit->getAriety(); t++) {
                        if (bodyLit -> isVariableTermAt(t)) {
                            ruleBoundVariables.insert(bodyLit->getTermAt(t));
                        }
                    }
                }
            }

        }
    }
}

BoundAnnotatedLiteral literalToBoundAnnotatedLiteral(const aspc::Literal & lit) {

    return BoundAnnotatedLiteral(lit.getPredicateName(), std::vector<bool>(lit.getAriety(), true), lit.isNegated());

}

BoundAnnotatedLiteral literalToBoundAnnotatedLiteral(const aspc::Literal & lit, std::unordered_set<std::string> & boundVariables) {

    BoundAnnotatedLiteral boundAnnotatedLiteral = BoundAnnotatedLiteral(lit.getPredicateName(), lit.isNegated());
    for (unsigned i = 0; i < lit.getAriety(); i++) {
        if (lit.isVariableTermAt(i) && boundVariables.count(lit.getTermAt(i))) {
            boundAnnotatedLiteral.addBoundInformation(true);
        } else {
            boundAnnotatedLiteral.addBoundInformation(false);
        }
    }
    return boundAnnotatedLiteral;

}

void CompilationManager::writeNegativeReasonsFunctionsPrototypes(aspc::Program & program) {
    *out << ind << "//printing functions prototypes for reasons of negative literals;\n";

    list<BoundAnnotatedLiteral> toProcessLiterals;
    list<BoundAnnotatedLiteral> processedLiterals;
    std::unordered_map <std::string, std::string> functionsMap;

    for (const aspc::Rule & r : program.getRules()) {
        if (r.isConstraint()) {
            for (const aspc::Formula * f : r.getFormulas()) {
                if (f->isLiteral()) {
                    const aspc::Literal & lit = (const aspc::Literal &) * f;
                    possiblyAddToProcessLiteral(literalToBoundAnnotatedLiteral(lit), toProcessLiterals, processedLiterals);
                }
            }
        }
    }
    while (!toProcessLiterals.empty()) {
        BoundAnnotatedLiteral next = toProcessLiterals.back();
        toProcessLiterals.pop_back();
        processedLiterals.push_back(next);
        writeNegativeReasonsFunctionsPrototypes(program, next, toProcessLiterals, processedLiterals, functionsMap);
    }
}

void CompilationManager::writeNegativeReasonsFunctions(aspc::Program & program) {

    *out << ind << "//printing functions for reasons of negative literals;\n";

    list<BoundAnnotatedLiteral> toProcessLiterals;
    list<BoundAnnotatedLiteral> processedLiterals;
    std::unordered_map <std::string, std::string> functionsMap;

    for (const aspc::Rule & r : program.getRules()) {
        if (r.isConstraint()) {
            for (const aspc::Formula * f : r.getFormulas()) {
                if (f->isLiteral()) {
                    const aspc::Literal & lit = (const aspc::Literal &) * f;
                    possiblyAddToProcessLiteral(literalToBoundAnnotatedLiteral(lit), toProcessLiterals, processedLiterals);
                }
            }
        }
    }
    while (!toProcessLiterals.empty()) {
        BoundAnnotatedLiteral next = toProcessLiterals.back();
        toProcessLiterals.pop_back();
        processedLiterals.push_back(next);
        writeNegativeReasonsFunctions(program, next, toProcessLiterals, processedLiterals, functionsMap);
    }

    *out << ind++ << "void createFunctionsMap() {\n";
    for (const auto & entry : functionsMap) {
        *out << ind << "explainNegativeFunctionsMap[&_" << entry.first << "] = " << entry.second << ";\n";
    }
    *out << --ind << "}\n";
}
void CompilationManager::checkExistsShareVariableMap(int ruleId, int aggrIndex,std::string& sharedVariables,bool create){

    //*out << ind << "std::cout<<\"check exists shared value tuple\"<<std::endl;\n";

    int countVar=0;
    std::string indexesToString="";
    for(unsigned varIndex : aggregateVariablesIndex[std::to_string(ruleId)+":"+std::to_string(aggrIndex)]){
        indexesToString+=std::to_string(varIndex);
        if(countVar < aggregateVariablesIndex[std::to_string(ruleId)+":"+std::to_string(aggrIndex)].size()-1)
            indexesToString+=",";
        countVar++;
    }

    if(create){
        *out << ind++ << "if(!sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariables<<"})){\n";
            *out << ind << "sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".insert({"<<sharedVariables<<"});\n";
    }else{
        *out << ind++ << "if(sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariables<<"})!=0){\n";
    }
}
void CompilationManager::printVars(const aspc::Literal& li,std::string tupleName,std::unordered_set<std::string> & boundVars)const{
    //std::cout<<tupleName<<std::endl;
    for (unsigned tiIndex = 0; tiIndex < li.getTerms().size(); tiIndex++) {
        if(li.isVariableTermAt(tiIndex))
            if(!boundVars.count(li.getTermAt(tiIndex))){
    //          std::cout << li.getTermAt(tiIndex) << " printed "<<std::endl;
                *out << ind << "int "<<li.getTermAt(tiIndex) << " = "<<tupleName<<"at("<<tiIndex<<");\n";
                boundVars.insert(li.getTermAt(tiIndex));
            }
    }
}
bool CompilationManager::checkTupleFormat(const aspc::Literal& li,std::string buildIndex,bool tuplePointer){

    std::string point = tuplePointer ? "->":".";
    bool checkVariablesEquals=false;
    for(unsigned i=0;i<li.getAriety();i++){
        for(unsigned j=i+1;j<li.getAriety();j++){
            if(li.isVariableTermAt(i) && li.isVariableTermAt(j) && li.getTermAt(i)==li.getTermAt(j)){
                if(!checkVariablesEquals){
                    *out << ind++ << "if(tuple"<<buildIndex<<point<<"at("<<i<<") == tuple"<<buildIndex<<point<<"at("<<j<<")";
                    checkVariablesEquals=true;
                }else
                    *out << "&& tuple"<<buildIndex<<point<<"at("<<i<<") == tuple"<<buildIndex<<point<<"at("<<j<<")";
            }
        }
        if(!li.isVariableTermAt(i)){
            std::string mapStringConstant = !isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);

            if(!checkVariablesEquals){
                *out << ind++ << "if(tuple"<<buildIndex<<point<<"at("<<i<<") == "<<mapStringConstant;
                checkVariablesEquals=true;
            }else{
                *out << "&& tuple"<<buildIndex<<point<<"at("<<i<<") == "<<mapStringConstant;
            }
        }
    }
    if(checkVariablesEquals){
        *out << "){\n";
    }

    return checkVariablesEquals;
}
void CompilationManager::declareAuxMap(std::string mapVariableName,std::vector<unsigned> keyIndexes,std::string predicateName,bool createFalseAuxMap,bool aggrStruct){
    if(!declaredMaps.count(mapVariableName)){
        *out << ind << "AuxMap p" << mapVariableName << "({";
        for (unsigned k = 0; k < keyIndexes.size(); k++) {
            if (k > 0) {
                *out << ",";
            }
            *out << keyIndexes[k];
        }
        *out << "});\n";

        //TODO remove duplication
        *out << ind << "AuxMap u" << mapVariableName << "({";
        for (unsigned k = 0; k < keyIndexes.size(); k++) {
            if (k > 0) {
                *out << ",";
            }
            *out << keyIndexes[k];
        }
        *out << "});\n";
        if(aggrStruct){
            *out << ind << "AuxMap np" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";

            *out << ind << "AuxMap nu" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";
        }
        if(createFalseAuxMap){
            *out << ind << "AuxMap f" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";
        }
        predicateToAuxiliaryMaps[predicateName].insert(mapVariableName);
        if(aggrStruct){
            predicateToNegativeAuxiliaryMaps[predicateName].insert(mapVariableName);
        }
        if (mode == EAGER_MODE) {
            predicateToUndefAuxiliaryMaps[predicateName].insert(mapVariableName);
            if(aggrStruct){
                predicateToNegativeUndefAuxiliaryMaps[predicateName].insert(mapVariableName);
            }
            if(createFalseAuxMap)
                predicateToFalseAuxiliaryMaps[predicateName].insert(mapVariableName);
        }
        declaredMaps.insert(mapVariableName);
    }
}
void CompilationManager::updateUndefinedSharedVariablesMap(const aspc::Rule& r,int startLit){

    std::unordered_set<std::string> boundVars;
    printVars(r.getBodyLiterals()[startLit],"tuple.",boundVars);
    // *out << ind << "tuple.print();\n";
    // *out << ind << "std::cout<<\"updatesharedvariables\"<<std::endl;\n";
    r.getBodyLiterals()[startLit].addVariablesToSet(boundVars);
    bool checkFormat = checkTupleFormat(r.getBodyLiterals()[startLit],"",false);
    int closingParenthesis = checkFormat ? 1:0;
    const std::vector<unsigned> & joinOrder = r.getOrderedBodyIndexesByStarter(startLit);
    
    for(unsigned i=0;i<joinOrder.size();i++){
        const aspc::Formula* f =r.getFormulas()[joinOrder[i]];

        if(joinOrder[i] !=startLit && !f->containsAggregate()){
            if(f->isBoundedRelation(boundVars)){
                *out << ind << "if("<< ((const aspc::ArithmeticRelation*)f)->getStringRep()<<"){\n";
                closingParenthesis++;
            }else if(f->isBoundedValueAssignment(boundVars)){
                *out << ind << "int " << ((const aspc::ArithmeticRelation*)f)->getAssignmentStringRep(boundVars) << ";\n";
                f->addVariablesToSet(boundVars);
            }else if(!f->isBoundedLiteral(boundVars)){
                const aspc::Literal* l = (const aspc::Literal*)f;
                std::string mapVariableName = l->getPredicateName() + "_";
                for (unsigned tiIndex = 0; tiIndex < l->getAriety(); tiIndex++) {
                    if ((l->isVariableTermAt(tiIndex) && boundVars.count(l->getTermAt(tiIndex))) || !l->isVariableTermAt(tiIndex)) {
                        mapVariableName += std::to_string(tiIndex) + "_";
                    }
                }
                *out << ind << "const std::vector<const Tuple *>& undefTuples"<<i<<" = u"<<mapVariableName<<".getValues({";
                printLiteralTuple(l,boundVars);
                *out << "});\n";
                *out << ind << "const std::vector<const Tuple*>& trueTuples"<<i<<" = p"<<mapVariableName<<".getValues({";
                printLiteralTuple(l,boundVars);
                *out << "});\n";
                *out << ind++ << "for(int i=0;i<undefTuples"<<i<<".size()+trueTuples"<<i<<".size();i++){\n";
                *out << ind << "const Tuple * tuple"<<i<<";\n";

                *out << ind++ << "if(i<undefTuples"<<i<<".size())\n";
                *out << ind << "tuple"<<i<<" = undefTuples"<<i<<"[i];\n";
                *out << --ind << "else tuple"<<i<<" = trueTuples"<<i<<"[i-undefTuples"<<i<<".size()];\n";

                closingParenthesis++;
                printVars(*l,"tuple"+std::to_string(i)+"->",boundVars);
                l->addVariablesToSet(boundVars);
                if(checkTupleFormat(*l,std::to_string(i),true))
                    closingParenthesis++;
            }
        }
    }

    //join partendos dal letterale startLit costruito

    for(const aspc::ArithmeticRelationWithAggregate& ar: r.getArithmeticRelationsWithAggregate()){
        //vedo le variabili condivise tra i letterali del corpo ed ogni aggregato della regola
        std::string key(std::to_string(r.getRuleId())+":"+std::to_string(ar.getFormulaIndex()));


        std::string sharedVarsIndexesToString="";
        for(unsigned varIndex : sharedVariablesIndexesMap[key]){

            //salvo gli indici delle variabili di aggregazione
            sharedVarsIndexesToString+=std::to_string(varIndex)+"_";
        }

        std::string sharedVars = sharedVariablesMap[key];
        if(sharedVars!=""){
            *out << ind++ << "{\n";
                checkExistsShareVariableMap(r.getRuleId(),ar.getFormulaIndex(),sharedVars,true);
                *out << --ind << "}\n";
            *out << --ind << "}\n";
            //*out << ind << "std::cout<<\"True size: \"<<sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<"[sharedTuple]->first->size()<<std::endl;\n";
            //*out << ind << "std::cout<<\"Undef size: \"<<sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<"[sharedTuple]->second->size()<<std::endl;\n";

        }
    }

    for(int i=0;i<closingParenthesis;i++){
        *out << --ind << "}\n";
    }

    //comment
    // *out << ind << "std::cout<<\"saved for all aggregate\"<<std::endl;\n";

}
void CompilationManager::declareDataStructureForAggregate(const aspc::Rule& r,const std::set< pair<std::string, unsigned> >& aggregatePredicates){

    //BUILD AGGREGATE JOIN
    for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
        sharedVariablesMapForAggregateBody[aggr.getJoinTupleName()].push_back("sharedVariables_"+std::to_string(r.getRuleId())+"_ToAggregate_"+std::to_string(aggr.getFormulaIndex()));
        aggrIdentifierForAggregateBody[aggr.getJoinTupleName()].push_back({r.getRuleId(),aggr.getFormulaIndex()});
    
        int startingId = 0;
        for(const aspc::Literal& starter :aggr.getAggregate().getAggregateLiterals()){
            std::unordered_set<std::string> boundVars;
            for(int i=0;i<starter.getAriety();i++){
                if(starter.isVariableTermAt(i)){
                    boundVars.insert(starter.getTermAt(i));
                }
            }
            int liIndex=0;
            for(const aspc::Literal& li :aggr.getAggregate().getAggregateLiterals()){
                std::vector<unsigned> boundIndices;
                std::string auxMapName = li.getPredicateName()+"_";
                if(liIndex!=startingId){
                    for(unsigned i=0;i<li.getAriety();i++){
                        if(!li.isVariableTermAt(i) || boundVars.count(li.getTermAt(i))){
                            boundIndices.push_back(i);
                            auxMapName+=std::to_string(i)+"_";
                        }
                    }
                    for(unsigned i=0;i<li.getAriety();i++){
                        if(li.isVariableTermAt(i))
                            boundVars.insert(li.getTermAt(i));
                    }
                    declareAuxMap(auxMapName,boundIndices,li.getPredicateName(),false,false);
                }
                liIndex++;
            }
            startingId++;
        }
    }
    
    //Jointuple auxMap
    for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
        std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
        std::vector<unsigned int> sharedVariablesIndex(sharedVariablesIndexesMap[aggrIdentifier]);
        std::string sharedVarProj;
        for(unsigned int i : sharedVariablesIndex){
            sharedVarProj+=std::to_string(i)+"_";
        }
        declareAuxMap("_"+aggr.getJoinTupleName()+sharedVarProj,sharedVariablesIndex,aggr.getJoinTupleName(),false,true);
        std::vector<unsigned int> aggrVarIndex(aggregateVariablesIndex[aggrIdentifier]);
        std::string aggrVarProj;
        for(unsigned int i : aggrVarIndex){
            aggrVarProj+=std::to_string(i)+"_";
            sharedVariablesIndex.push_back(i);
        }
        declareAuxMap("_"+aggr.getJoinTupleName()+aggrVarProj,aggrVarIndex,aggr.getJoinTupleName(),false,true);


        declareAuxMap("_"+aggr.getJoinTupleName()+sharedVarProj+aggrVarProj,sharedVariablesIndex,aggr.getJoinTupleName(),false,true);
        int ariety=0;
        for(const aspc::Literal& li : aggr.getAggregate().getAggregateLiterals()){
            std::vector<unsigned int> index;
            std::string proj;
            for(unsigned int i=0;i<li.getAriety();i++){
                proj+=std::to_string(ariety+i)+"_";
                index.push_back(ariety+i);
            }
            declareAuxMap("_"+aggr.getJoinTupleName()+proj,index,aggr.getJoinTupleName(),false,true);
            ariety+=li.getAriety();
        }
        
    }

    int startLit=0;
    for(const aspc::Literal& starter: r.getBodyLiterals()){
        for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
            std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
            std::string auxMapName=starter.getPredicateName()+"_";
            std::vector<unsigned int> boundIndices;
            for(int i=0;i<starter.getAriety();i++){
                if(!starter.isVariableTermAt(i)){
                    auxMapName+=std::to_string(i)+"_";
                    boundIndices.push_back(i);
                }else{
                    for(int v:sharedVariablesIndexesMap[aggrIdentifier]){
                        if(starter.getTermAt(i) == aggr.getTermAt(v)){
                            auxMapName+=std::to_string(i)+"_";
                            boundIndices.push_back(i);
                            break;
                        }
                    }
                }
            }
            declareAuxMap(auxMapName,boundIndices,starter.getPredicateName(),false,false);
        }
    }

    //dichiaro le auxMap che vengono utilizzate per costruire le jointuple
    // for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){

    //     std::string joinTupleName=aggr.getJoinTupleName();
    //     // std::cout<<joinTupleName<<std::endl;
    //     std::set<string> varAlreadyAdded;
    //     std::vector<std::vector<unsigned>> aggregateLiteralIndexes;
    //     int varIndex=0;
    //     int index=0;
    //     std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());

    //     for(const aspc::Literal& li: aggr.getAggregate().getAggregateLiterals()){

    //         aggregateLiteralIndexes.push_back(std::vector<unsigned>());

    //         //creo una mappa per ogni letterale indicizzata su tutte le variabili
    //         std::string mapIndexedAllVars=li.getPredicateName()+"_";

    //         std::vector<unsigned> localIndex;
    //         for (unsigned tiIndex = 0; tiIndex < li.getAriety(); tiIndex++) {

    //             mapIndexedAllVars+=std::to_string(tiIndex)+"_";
    //             aggregateLiteralIndexes[index].push_back(varIndex);
    //             localIndex.push_back(tiIndex);
    //             varIndex++;

    //         }

    //         declareAuxMap(mapIndexedAllVars,localIndex,li.getPredicateName(),true,false);

    //         //creo una mappa non indicizzata per iniziare il join
    //         declareAuxMap(li.getPredicateName() + "_",std::vector<unsigned>(),li.getPredicateName(),true,false);

    //         //creo una mappa per gli altri letterali indicizzata rispetto al letterale corrente
    //         std::unordered_set<std::string> boundVariables;
    //         li.addVariablesToSet(boundVariables);
    //         int buildIndex=0;
    //         for(const aspc::Literal& li_: aggr.getAggregate().getAggregateLiterals()){
    //             std::string mapVariableName = li_.getPredicateName() + "_";
    //             std::vector< unsigned > keyIndexes;
    //             if(buildIndex != index){
    //                 for (unsigned tiIndex = 0; tiIndex < li_.getAriety(); tiIndex++) {
    //                     if ((li_.isVariableTermAt(tiIndex) && boundVariables.count(li_.getTermAt(tiIndex))) || !li_.isVariableTermAt(tiIndex)) {
    //                         mapVariableName += std::to_string(tiIndex) + "_";
    //                         keyIndexes.push_back(tiIndex);

    //                     }
    //                 }
    //                 li_.addVariablesToSet(boundVariables);
    //                 declareAuxMap(mapVariableName,keyIndexes,li_.getPredicateName(),true,false);
    //             }
    //             buildIndex++;
    //         }
    //         index++;
    //     }
    //     sharedVariablesMapForAggregateBody[joinTupleName].push_back("sharedVariables_"+std::to_string(r.getRuleId())+"_ToAggregate_"+std::to_string(aggr.getFormulaIndex()));
    //     aggrIdentifierForAggregateBody[aggr.getJoinTupleName()].push_back({r.getRuleId(),aggr.getFormulaIndex()});
    //     /*for(const std::string& v : aggr.getAggregate().getAggregateVariables()){
    //         int joinTupleIndex=0;
    //         for(const aspc::Literal& li: aggr.getAggregate().getAggregateLiterals()){
    //             for (unsigned tiIndex = 0; tiIndex < li.getAriety(); tiIndex++) {

    //                 if( v == li.getTermAt(tiIndex)){make
    //                     if(!varAlreadyAdded.count(li.getTermAt(tiIndex))){
    //                         aggregateVariablesIndex[aggrIdentifier].push_back(joinTupleIndex);
    //                         varAlreadyAdded.insert(li.getTermAt(tiIndex));
    //                     }
    //                 }
    //                 joinTupleIndex++;
    //             }
    //         }
    //     }*/
    //     //dichiaro una mappa per le joinTuple indicizzata sulle variabili di aggregazione
    //     std::string aggregateVarsIndex="";
    //     for(unsigned index_ : aggregateVariablesIndex[aggrIdentifier]){
    //         aggregateVarsIndex+=std::to_string(index_)+"_";

    //     }
    //     declareAuxMap("_"+joinTupleName+aggregateVarsIndex,aggregateVariablesIndex[aggrIdentifier],joinTupleName,false,true);


    //     //dichiaro una mappa per le joinTuple non indicizzata
    //     // declareAuxMap("_"+joinTupleName,std::vector<unsigned>(),joinTupleName,false,true);


    //     //dichiaro una mappa per le joinTuple indicizzata sulle variabili condivise con il corpo
    //     std::string sharedVarsIndexToString="";
    //     for(unsigned index_ : sharedVariablesIndexesMap[aggrIdentifier])
    //         sharedVarsIndexToString+=std::to_string(index_)+"_";
    //     std::vector<unsigned> sharedVarsIndex = sharedVariablesIndexesMap[aggrIdentifier];
    //     declareAuxMap("_"+joinTupleName+sharedVarsIndexToString,sharedVarsIndex,joinTupleName,false,true);
        
    //     //mappa indicizzata su aggrVars and sharedVars
    //     std::vector<unsigned> sharedAndAggrVarIndex(sharedVarsIndex);
    //     for(unsigned index_ : aggregateVariablesIndex[aggrIdentifier])
    //         sharedAndAggrVarIndex.push_back(index_);
    //     declareAuxMap("_"+joinTupleName+sharedVarsIndexToString+aggregateVarsIndex,sharedAndAggrVarIndex,joinTupleName,false,true);
        
    //     // int totalAriety=0;
    //     // for(const aspc::Literal& l : aggr.getAggregate().getAggregateLiterals()){
    //     //     std::string lit_indeces="";
    //     //     std::vector<unsigned> total_indeces(sharedVarsIndex);
    //     //     for(int i=0;i<l.getAriety();i++){
    //     //         lit_indeces+=std::to_string(i+totalAriety)+"_";
    //     //         total_indeces.push_back(i+totalAriety);
    //     //     }
    //     //     declareAuxMap("_"+joinTupleName+sharedVarsIndexToString+lit_indeces,total_indeces,joinTupleName,false,true);
    //     //     totalAriety+=l.getAriety();
    //     // }
    //     std::string sharedVariables = sharedVariablesMap[aggrIdentifier];

    //     //dichiaro una mappa per le join tuples indicizzata sull variabili di ogni letterale nell'aggregato
    //     index=0;
    //     for(std::vector<unsigned>& indexes : aggregateLiteralIndexes){
    //         std::string literalTermIndex="";
    //         for(unsigned var : indexes)
    //             literalTermIndex = literalTermIndex + std::to_string(var) + "_";
    //         //salvo per ogni letterale il nome dell'AuxMap delle join tuple indicizzata secondo il letterale
    //         // aggregateLiteralToAuxiliaryMap[aggr.getAggregate().getAggregateLiterals()[index].getPredicateName()+"_"+std::to_string(index)+"_"+aggrIdentifier]=std::string("_"+joinTupleName+literalTermIndex);
    //         // aggregateLiteralToPredicateWSet[aggr.getAggregate().getAggregateLiterals()[index].getPredicateName()+"_"+aggrIdentifier]=std::string(joinTupleName);

    //         declareAuxMap("_"+joinTupleName+literalTermIndex,indexes,joinTupleName,false,true);
    //         // for(unsigned var :sharedVariablesIndexesMap[aggrIdentifier])
    //         //     indexes.push_back(var);
    //         // if(sharedVariables!="")
    //         //     declareAuxMap("_"+joinTupleName+literalTermIndex+sharedVarsIndexToString,indexes,joinTupleName,false,true);
    //         // for(unsigned v : aggregateVariablesIndex[aggrIdentifier]){
    //         //     indexes.push_back(v);
    //         // }
    //         // declareAuxMap("_"+joinTupleName+literalTermIndex+sharedVarsIndexToString+aggregateVarsIndex,indexes,joinTupleName,false,true);
            
    //         index++;
    //     }

    //     if(sharedVariables!=""){

    //         //dichiaro una mappa per ogni letterale del corpo indicizzata sulle shared variable e costanti
    //         int literalIndex=0;
    //         //std::cout<<"Declaring map for external predicates"<<std::endl;
    //         for(const aspc::Literal& bodyLiteral : r.getBodyLiterals()){
    //             //std::cout<<"Start from ";
    //             //bodyLiteral.print();
    //             //std::cout<<std::endl;

    //             std::string auxMapName = bodyLiteral.getPredicateName()+"_";
    //             std::unordered_set<std::string> boundVars;
    //             std::vector<unsigned> indexes;
    //             for(int i=0;i<bodyLiteral.getAriety();i++){
    //                 if(sharedVariables.find(bodyLiteral.getTermAt(i))!=std::string::npos || !bodyLiteral.isVariableTermAt(i)){
    //                     auxMapName+=std::to_string(i)+"_";
    //                     indexes.push_back(i);
    //                 }
    //                 if(bodyLiteral.isVariableTermAt(i)){
    //                     boundVars.insert(bodyLiteral.getTermAt(i));
    //                 }
    //             }

    //             bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(bodyLiteral.getPredicateName(),bodyLiteral.getAriety()))!=0;
    //             declareAuxMap(auxMapName,indexes,bodyLiteral.getPredicateName(),declareFalseAuxMap,false);

    //             //join dei letterali del corpo considerando le sharedVariables bound
    //             int bodyLiteralIndex=0;
    //             for(const aspc::Literal& buildBodyLiteral : r.getBodyLiterals()){
    //                 if(bodyLiteralIndex!=literalIndex){
    //                     std::string buildAuxMapName = buildBodyLiteral.getPredicateName()+"_";
    //                     std::vector<unsigned> buildindexes;

    //                     for(int i=0;i<buildBodyLiteral.getAriety();i++){
    //                         if(sharedVariables.find(buildBodyLiteral.getTermAt(i))!=std::string::npos || !buildBodyLiteral.isVariableTermAt(i) || boundVars.count(buildBodyLiteral.getTermAt(i))){
    //                             buildAuxMapName+=std::to_string(i)+"_";
    //                             buildindexes.push_back(i);
    //                         }
    //                         if(buildBodyLiteral.isVariableTermAt(i)){
    //                             boundVars.insert(buildBodyLiteral.getTermAt(i));
    //                         }
    //                     }
    //                     bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(buildBodyLiteral.getPredicateName(),buildBodyLiteral.getAriety()))!=0;
    //                     //std::cout<<"Declare "<<buildAuxMapName<<std::endl;
    //                     declareAuxMap(buildAuxMapName,buildindexes,buildBodyLiteral.getPredicateName(),declareFalseAuxMap,false);

    //                 }
    //                 bodyLiteralIndex++;
    //             }
    //             literalIndex++;
    //         }
    //         for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
    //             int literalIndex=0;
    //             for(const aspc::Literal& aggrLit : aggr.getAggregate().getAggregateLiterals()){
    //                 std::string auxMapName = aggrLit.getPredicateName()+"_";
    //                 std::unordered_set<std::string> boundVars;
    //                 std::vector<unsigned> indexes;
    //                 for(int i=0;i<aggrLit.getAriety();i++){
    //                     if(sharedVariables.find(aggrLit.getTermAt(i))!=std::string::npos || !aggrLit.isVariableTermAt(i)){
    //                         auxMapName+=std::to_string(i)+"_";
    //                         indexes.push_back(i);
    //                     }
    //                     if(aggrLit.isVariableTermAt(i)){
    //                         boundVars.insert(aggrLit.getTermAt(i));
    //                     }
    //                 }

    //                 bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(aggrLit.getPredicateName(),aggrLit.getAriety()))!=0;
    //                 declareAuxMap(auxMapName,indexes,aggrLit.getPredicateName(),declareFalseAuxMap,false);

    //                 //join dei letterali del corpo considerando le sharedVariables bound
    //                 int bodyLiteralIndex=0;
    //                 for(const aspc::Literal& buildAggrLiteral : aggr.getAggregate().getAggregateLiterals()){
    //                     if(bodyLiteralIndex!=literalIndex){
    //                         std::string buildAuxMapName = buildAggrLiteral.getPredicateName()+"_";
    //                         std::vector<unsigned> buildindexes;

    //                         for(int i=0;i<buildAggrLiteral.getAriety();i++){
    //                             if(sharedVariables.find(buildAggrLiteral.getTermAt(i))!=std::string::npos || !buildAggrLiteral.isVariableTermAt(i) || boundVars.count(buildAggrLiteral.getTermAt(i))){
    //                                 buildAuxMapName+=std::to_string(i)+"_";
    //                                 buildindexes.push_back(i);
    //                             }
    //                             if(buildAggrLiteral.isVariableTermAt(i)){
    //                                 boundVars.insert(buildAggrLiteral.getTermAt(i));
    //                             }
    //                         }
    //                         bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(buildAggrLiteral.getPredicateName(),buildAggrLiteral.getAriety()))!=0;
    //                         //std::cout<<"Declare "<<buildAuxMapName<<std::endl;
    //                         declareAuxMap(buildAuxMapName,buildindexes,buildAggrLiteral.getPredicateName(),declareFalseAuxMap,false);
    //                     }
    //                     bodyLiteralIndex++;
    //                 }
    //                 literalIndex++;
    //             }
    //         }
    //     }
    // }
}
void CompilationManager::generateStratifiedCompilableProgram(aspc::Program & program, AspCore2ProgramBuilder* builder) {

    bool programHasConstraint = program.hasConstraint();

    *out << ind << "#include \"Executor.h\"\n\n";
    *out << ind << "#include \"utils/ConstantsManager.h\"\n\n";
    *out << ind << "#include \"DLV2libs/input/InputDirector.h\"\n\n";
    *out << ind << "#include \"parsing/AspCore2InstanceBuilder.h\"\n\n";
    *out << ind << "#include \"datastructures/PredicateSet.h\"\n\n";
    *out << ind << "#include \"datastructures/ReasonTable.h\"\n\n";
    *out << ind << "#include \"datastructures/PostponedReasons.h\"\n\n";
    *out << ind << "#include<ctime>\n\n";
    *out << ind << "#include<ctime>\n\n";
    *out << ind << "#include<map>\n\n";
    *out << ind << "namespace aspc {\n";
    *out << ind++ << "extern \"C\" Executor* create_object() {\n";

    *out << ind << "return new Executor;\n";
    *out << --ind << "}\n";

    *out << ind++ << "extern \"C\" void destroy_object( Executor* object ) {\n";
    *out << ind << "delete object;\n";
    *out << --ind << "}\n";



    *out << ind << "Executor::Executor() {}\n\n";

    //typedefs

    if (programHasConstraint) {
        *out << ind << "typedef TupleWithReasons Tuple;\n";
    } else {
        *out << ind << "typedef TupleWithoutReasons Tuple;\n";
    }
    *out << ind << "typedef AuxiliaryMap<Tuple> AuxMap;\n";

    *out << ind << "typedef std::vector<const Tuple* > Tuples;\n";
    *out << ind << "using PredicateWSet = PredicateSet<Tuple, TuplesHash>;\n\n";

    if (mode == LAZY_MODE) {
        *out << ind << "std::unordered_map<std::string, PredicateWSet*> predicateWSetMap;\n";
        *out << ind << "std::unordered_map<std::string, PredicateWSet*> predicateFSetMap;\n";
    }

    if (mode == EAGER_MODE) {
        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*> predicateWSetMap;\n";
        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*> predicateFSetMap;\n";
        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*> predicateUSetMap;\n";
    }

    //contiene predicati con la rispettiva arità
    const set< pair<std::string, unsigned> >& predicates = program.getPredicates();

    for (const pair<std::string, unsigned>& predicate : predicates) {
        //*out << ind << "const std::string & "<< predicate.first << " = ConstantsManager::getInstance().getPredicateName("<< predicate.first <<");\n";
        *out << ind << "const std::string _" << predicate.first << " = \"" << predicate.first << "\";\n";
        *out << ind << "PredicateWSet w" << predicate.first << "(" << predicate.second << ");\n";
        *out << ind << "PredicateWSet u" << predicate.first << "(" << predicate.second << ");\n";
        *out << ind << "PredicateWSet f" << predicate.first << "(" << predicate.second << ");\n";

    }
    const std::set< pair<std::string, unsigned> >& aggregatePredicates = program.getAggregatePredicates();

    for(const std::pair<std::string, unsigned>& predicate : aggregatePredicates){
        if(!predicates.count(predicate)){
            *out << ind << "const std::string _" << predicate.first << " = \"" << predicate.first << "\";\n";
            *out << ind << "PredicateWSet w" << predicate.first << "(" << predicate.second << ");\n";
            *out << ind << "PredicateWSet u" << predicate.first << "(" << predicate.second << ");\n";
            *out << ind << "PredicateWSet f" << predicate.first << "(" << predicate.second << ");\n";

        }
    }
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<std::vector<int>>>> trueAggrVars;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<std::vector<int>>>> undefAggrVars;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<int>>> positiveAggrReason;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<int>>> negativeAggrReason;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>, unsigned int>> actualSum;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>, unsigned int>> possibleSum;\n";
    //dichiaro predicateWSet per joinTuple
    std::unordered_set<std::string> declaredJoinTupleSet;

    for(aspc::Rule & r : program.getRules()){
        if(r.isConstraint() && r.containsAggregate()){
            for(const aspc::ArithmeticRelationWithAggregate& ar : r.getArithmeticRelationsWithAggregate()){

                std::string joinTupleName =ar.getJoinTupleName();

                //contains variable index inside jointuple
                std::vector<pair<std::string,int>> bodyAggregateVars;
                std::unordered_set<std::string> vars;
                int arity=0;
                for(const aspc::Literal& l : ar.getAggregate().getAggregateLiterals()){
                    for(unsigned i=0;i<l.getAriety();i++){
                        if(l.isVariableTermAt(i) && l.getTermAt(i)!="_"){
                            bodyAggregateVars.push_back(std::pair<std::string,int>(l.getTermAt(i),arity+i));
                            vars.insert(l.getTermAt(i));
                        }
                    }
                    arity+=l.getAriety();
                }
                std::vector<pair<std::string,int>> inequalityAggregateVars;
                for(const aspc::ArithmeticRelation& inequality : ar.getAggregate().getAggregateInequalities()){
                    if(inequality.isBoundedValueAssignment(vars)){
                        std::string v = inequality.getAssignedVariable(vars);
                        inequalityAggregateVars.push_back(std::pair<std::string,int>({v,arity}));
                        vars.insert(v);
                        arity++;
                    }
                }
                for(auto pair : inequalityAggregateVars){
                    bool found = false;
                    for(const aspc::Literal& l : r.getBodyLiterals()){
                        if(l.getVariables().count(pair.first)!=0){
                            found=true;
                            break;
                        }
                    }
                    bodyAggregateVars.push_back(pair);
                    joinTupleName+=pair.first+"_";
                }
                //dichiaro le shared variables per l'aggregato formulaIndex e la regola
                std::string key(std::to_string(r.getRuleId())+":"+std::to_string(ar.getFormulaIndex()));
                std::unordered_set<std::string> sharedVars;
                for(std::string v: ar.getAggregate().getAggregateVariables()){
                    if(isVariable(v)){
                        for(auto pair : bodyAggregateVars)
                            if(v==pair.first){
                                aggregateVariablesIndex[key].push_back(pair.second);
                                break;
                            }
                    }else{
                        std::cout<<v<<std::endl;
                    }
                }
                bool firstVarAdded=false;
                for(auto pair : bodyAggregateVars){
                    bool found=false;
                    std::unordered_set<std::string> boundVars;
                    for(const aspc::Literal& l : r.getBodyLiterals()){
                        l.addVariablesToSet(boundVars);
                        if(l.getVariables().count(pair.first)!=0){
                            found=true;
                            if (firstVarAdded){
                                sharedVariablesMap[key]+=",";
                            }
                            firstVarAdded=true;
                            sharedVariablesMap[key]+=pair.first;
                            sharedVariablesIndexesMap[key].push_back(pair.second);
                            //variable founded in at least one body literal
                            break;
                        }
                    }
                    if(!found){
                        for(const aspc::ArithmeticRelation& inequality : r.getArithmeticRelations()){
                            if(inequality.isBoundedValueAssignment(boundVars)){
                                if(pair.first == inequality.getAssignedVariable(boundVars)){
                                    found=true;
                                    if (firstVarAdded){
                                        sharedVariablesMap[key]+=",";
                                    }
                                    firstVarAdded=true;
                                    sharedVariablesMap[key]+=pair.first;
                                    sharedVariablesIndexesMap[key].push_back(pair.second);
                                    //variable founded in at least one body literal
                                    break;
                                }
                            }
                        }
                    }
                }


                r.updateJoinTupleName(ar.getFormulaIndex(),joinTupleName);
                if(!declaredJoinTupleSet.count(joinTupleName)){
                    *out << ind << "const std::string _" << joinTupleName << " = \"" << joinTupleName << "\";\n";
                    *out << ind << "PredicateWSet w"<<joinTupleName<<"("<<arity<<");\n";
                    *out << ind << "PredicateWSet u"<<joinTupleName<<"("<<arity<<");\n";
                    *out << ind << "PredicateWSet nw"<<joinTupleName<<"("<<arity<<");\n";
                    *out << ind << "PredicateWSet nu"<<joinTupleName<<"("<<arity<<");\n";
                    declaredJoinTupleSet.insert(joinTupleName);
                }
                
                aggregateToStructure.insert({joinTupleName+sharedVariablesMap[key]+ar.getAggrVarAsString(),aggregateToStructure.size()});
                // std::cout << joinTupleName<<sharedVariablesMap[key]<<ar.getAggrVarAsString()<<" "<<aggregateToStructure[joinTupleName+sharedVariablesMap[key]+ar.getAggrVarAsString()]<<std::endl;
                *out << ind << "std::set<std::vector<int>> sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<";\n";
                // *out << ind << "std::map<std::vector<int>, std::pair< AuxMap*,AuxMap*>*> sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<";\n";
            }
        }
    }
    *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueNegativeAggrVars["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefNegativeAggrVars["<<aggregateToStructure.size()<<"];\n";
    
    *out << ind << "std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason["<<aggregateToStructure.size()<<"];\n";
    
    *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> actualSum["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> possibleSum["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> actualNegativeSum["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> possibleNegativeSum["<<aggregateToStructure.size()<<"];\n";
    
    *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> maxPossibleNegativeSum["<<aggregateToStructure.size()<<"];\n";
    *out << ind << "int currentReasonLevel=0;\n";
    *out << ind << "PostponedReasons reasonMapping;\n";
    *out << ind << "bool first=true;\n";

    *out << ind++ << "Executor::~Executor() {\n";
    // for(const aspc::Rule & r : program.getRules()){
    //     if(r.isConstraint() && r.containsAggregate()){
    //         for(const aspc::ArithmeticRelationWithAggregate& ar: r.getArithmeticRelationsWithAggregate()){
    //             *out << ind++ << "for(auto sharedVar : sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<"){\n";
    //             *out << ind << "delete sharedVar.second->first;\n";
    //             *out << ind << "delete sharedVar.second->second;\n";
    //             *out << ind << "delete sharedVar.second;\n";
    //             *out << --ind << "}\n";
    //         }
    //     }
    // }
    *out << --ind << "}\n\n";

    *out << ind << "\n";
    *out << ind << "const std::vector<const Tuple* > EMPTY_TUPLES;\n";
    *out << ind << "std::unordered_map<std::string, const std::string * > stringToUniqueStringPointer;\n";

    *out << ind << "typedef void (*ExplainNegative)(const std::vector<int> & lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output);\n\n";

    *out << ind << "std::vector<Tuple> atomsTable;\n\n";

    *out << ind << "std::unordered_map<Tuple, unsigned, TuplesHash> tupleToVar;\n\n";

    *out << ind << "std::unordered_map<const std::string*, ExplainNegative> explainNegativeFunctionsMap;\n\n";

    *out << ind++ << "Tuple parseTuple(const std::string & literalString) {\n";

    *out << ind << "std::string predicateName;\n";
    *out << ind << "unsigned i = 0;\n";
    *out << ind++ << "for (i = 0; i < literalString.size(); i++) {\n";
    *out << ind++ << "if (literalString[i] == '(') {\n";
    *out << ind << "predicateName = literalString.substr(0, i);\n";
    *out << ind << "break;\n";
    *out << --ind << "}\n";
    *out << ind++ << "if (i == literalString.size() - 1) {\n";
    *out << ind << "predicateName = literalString.substr(0);\n";
    *out << --ind << "}\n";
    *out << --ind << "}\n";
    *out << ind << "std::vector<int> terms;\n";
    *out << ind++ << "for (; i < literalString.size(); i++) {\n";
    *out << ind << "char c = literalString[i];\n";
    *out << ind++ << "if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '-') {\n";
    *out << ind << "int start = i;\n";
    *out << ind << "int openBrackets = 0;\n";
    *out << ind++ << "while ((c != ' ' && c != ',' && c != ')') || openBrackets > 0) {\n";
    *out << ind++ << "if (c == '(') {\n";
    *out << ind << "openBrackets++;\n";
    *out << ind-- << "} else if (c == ')') {\n";
    ind++;
    *out << ind << "openBrackets--;\n";
    *out << ind-- << "}\n";
    *out << ind << "i++;\n";
    *out << ind << "c = literalString[i];\n";
    *out << --ind << "}\n";
    *out << ind << "terms.push_back(ConstantsManager::getInstance().mapConstant(literalString.substr(start, i - start)));\n";
    *out << --ind << "}\n";
    *out << --ind << "}\n";
    *out << ind << "return Tuple(terms, stringToUniqueStringPointer[predicateName]);\n";
    *out << --ind << "}\n";

    *out << ind << "//only ground lit function calls are not known a priori\n";

    *out << ind++ << "void explainNegativeLiteral(const Tuple * lit, std::unordered_set<std::string> & open_set, std::vector<const Tuple *> & output) {\n";
    *out << ind << "explainNegativeFunctionsMap[lit->getPredicateName()](*lit, open_set, output);\n";
    *out << --ind << "}\n\n";


    //perform join functions


    GraphWithTarjanAlgorithm& graphWithTarjanAlgorithm = builder->getGraphWithTarjanAlgorithm();
    std::vector< std::vector <int> > sccs = graphWithTarjanAlgorithm.SCC();

    //print working set
    //     for (const pair<std::string, unsigned>& predicate : predicates) {
    //        *out << ind << "w" << predicate.first <<".printTuples(\""<<predicate.first<<"\");\n";
    //    }
    const std::unordered_map<int, Vertex>& vertexByID = builder->getVertexByIDMap();

    //compute levels of each predicate
    std::vector< unsigned > predicateLevels(vertexByID.size());
    for (int i = sccs.size() - 1; i >= 0; i--) {
        const std::vector<int>& scc = sccs[i];
        for (int c : scc) {
            predicateLevels[c] = sccs.size() - i - 1;
        }
    }


    if (mode == LAZY_MODE) {
        *out << ind << "std::unordered_map <std::string, std::vector <AuxMap*> > predicateToAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <std::string, std::vector <AuxMap*> > predicateToUndefAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <std::string, std::vector <AuxMap*> > predicateToFalseAuxiliaryMaps;\n";
    } else {
        *out << ind << "std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToUndefAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToNegativeAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToNegativeUndefAuxiliaryMaps;\n";

        *out << ind << "std::unordered_map <const std::string*, std::vector <AuxMap*> > predicateToFalseAuxiliaryMaps;\n";
    }
    unsigned sccsSize = sccs.size();
    if (programHasConstraint) {
        sccsSize++;
    }
    std::vector< std::unordered_map<std::string, std::vector<unsigned>>> starterToExitRulesByComponent(sccsSize);
    std::vector < std::unordered_map < std::string, std::vector<pair<unsigned, unsigned> > >> starterToRecursiveRulesByComponent(sccsSize);
    std::vector<bool> exitRules(program.getRulesSize(), false);
    const std::unordered_map<std::string, int>& predicateIDs = builder->getPredicateIDsMap();


    for (aspc::Rule& r : program.getRules()) {
        //r is a constraint
        bool exitRule = true;
        unsigned lIndex = 0;
        unsigned headLevel = sccs.size();
        if (!r.isConstraint()) {
            std::vector<unsigned> starters;
            headLevel = predicateLevels[predicateIDs.at(r.getHead().at(0).getPredicateName())];
            for (const aspc::Formula* f : r.getFormulas()) {
                if (f->isLiteral()) {
                    const aspc::Literal * l = (const aspc::Literal*) f;
                    unsigned predicateID = predicateIDs.at(l->getPredicateName());
                    if (predicateLevels.at(predicateID) == headLevel) {
                        if (l->isNegated()) {
                            throw std::runtime_error("The input program is not stratified because of " + l->getPredicateName());
                        }
                        exitRule = false;
                        starterToRecursiveRulesByComponent[headLevel][l->getPredicateName()].push_back(pair<unsigned, unsigned>(r.getRuleId(), lIndex));
                        starters.push_back(lIndex);
                    }
                }
                lIndex++;
            }
            r.bodyReordering(starters);
        }
        if (exitRule || r.isConstraint()) {
            if (mode == LAZY_MODE) {
                r.bodyReordering();
                unsigned starter = r.getStarters()[0];
                aspc::Literal* starterL = (aspc::Literal*) r.getFormulas()[starter];
                starterToExitRulesByComponent[headLevel][starterL->getPredicateName()].push_back(r.getRuleId());
            } else {
                //mode == EAGER

                vector<unsigned> starters;
                for (unsigned i = 0; i < r.getBodySize(); i++) {

                    if (r.getFormulas()[i]->isLiteral() || r.getFormulas()[i]->containsAggregate()) {
                        starters.push_back(i);
                    }
                }
                if (r.isConstraint()) {
                    starters.push_back(r.getBodySize());
                }
                r.bodyReordering(starters);

                for (unsigned i = 0; i < starters.size(); i++) {
                    unsigned starter = r.getStarters()[i];
                    if (starter != r.getBodySize()) {
                        string pred_name;

                        if(r.getFormulas()[starter]->isLiteral()){
                            aspc::Literal* starterL = (aspc::Literal*) r.getFormulas()[starter];
                            pred_name=starterL->getPredicateName();
                        }else if(r.getFormulas()[starter]->containsAggregate()){
                            aspc::ArithmeticRelationWithAggregate* starterAggr = (aspc::ArithmeticRelationWithAggregate*) r.getFormulas()[starter];
                            pred_name="#"+std::to_string(r.getRuleId())+":"+std::to_string(starter);
                        }
                        auto & rules = starterToExitRulesByComponent[headLevel][pred_name];
                        bool alreadyAdded = false;
                        for (unsigned rule : rules) {
                            alreadyAdded = alreadyAdded | (rule == r.getRuleId());
                        }
                        if (!alreadyAdded) {
                            rules.push_back(r.getRuleId());
                        }


                    }
                }

            }
            exitRules[r.getRuleId()] = true;
        }
        if(r.containsAggregate()){
            declareDataStructureForAggregate(r,aggregatePredicates);
        }

        for (unsigned starter : r.getStarters()) {
            declareDataStructures(r, starter,aggregatePredicates);
        }

    }

    declareDataStructuresForReasonsOfNegative(program);

    for (const std::string & predicate : modelGeneratorPredicatesInNegativeReasons) {
        //*out << ind << "const std::string & "<< predicate.first << " = ConstantsManager::getInstance().getPredicateName("<< predicate.first <<");\n";
        *out << ind << "PredicateWSet neg_w" << predicate << "(" << predicateArieties[predicate] << ");\n";
    }

    // *out << ind++ << "void explainAggrLiteral(int var){\n";
    *out << ind++ << "void Executor::explainAggrLiteral(int var,std::vector<int>& reas){\n";
        *out << ind << "int v = var==-1?var:-var;\n";
        // *out << ind << "std::cout << \"Explain \" << v << std::endl;\n";

        *out << ind << "PostponedReasonData* data = &reasonMapping[v];\n";
        *out << ind << "if(data->getPropagationLevel() == -1) return;\n";
        *out << ind << "std::vector<int> aggregates_id = data->getAggregateId();\n";
        *out << ind++ << "for(int i=0; i < aggregates_id.size();i++){\n";
            *out << ind << "int aggr_index=aggregates_id[i];\n";
            // *out << ind << "std::cout << \"Collecting reason from aggr \" <<aggr_index<<std::endl;\n";
            *out << ind++ << "if(data->isPositive(i)){\n";
                // *out << ind << "std::cout<<\"Positive\"<<std::endl;\n";
                *out << ind++ << "for(int lit :positiveAggrReason[aggr_index][data->getSharedVariables()].getLiteralUntil(data->getPropagationLevel())){\n";

                    *out << ind << "reas.push_back(lit);\n";
                    // *out << ind << "int uLit= lit>=0 ? lit : -1*lit;\n";
                    // *out << ind << "std::string m= lit>=0 ? \"\" : \"-\";\n";
                    // *out << ind << "std::cout << m; atomsTable[uLit].print(); std::cout<<std::endl;\n";
                    // *out << ind << "std::cout << lit << std::endl;\n";
                *out << --ind << "}\n";
            *out << --ind << "}else{\n";
                ind++;
                // *out << ind << "std::cout << \"Negative\" <<std::endl;\n";
                *out << ind++ << "for(int lit :negativeAggrReason[aggr_index][data->getSharedVariables()].getLiteralUntil(data->getPropagationLevel())){\n";
                    *out << ind << "reas.push_back(lit);\n";
                    // *out << ind << "int uLit= lit>=0 ? lit : -1*lit;\n";
                    // *out << ind << "std::string m= lit>=0 ? \"\" : \"-\";\n";
                    // *out << ind << "std::cout << m; atomsTable[uLit].print(); std::cout<<std::endl;\n";
                    // *out << ind << "std::cout << lit << std::endl;\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        // *out << ind << "std::cout << \"Collecting reason from constraint body \" <<std::endl;\n";
            
        *out << ind++ << "for(int l : data->getBodyReason()){\n";
            // *out << ind << "int uLit= l>=0 ? l : -1*l;\n";
            // *out << ind << "std::string m= l>=0 ? \"\" : \"-\";\n";
            // *out << ind << "std::cout << m; atomsTable[uLit].print(); std::cout<<std::endl;\n";
            // *out << ind << "std::cout << l << std::endl;\n";

            *out << ind << "reas.push_back(l);\n";
        *out << --ind << "}\n";
        // *out << ind << "std::cout << \"reason computed\" <<std::endl;\n";
        
        *out << ind << "return;\n";
    *out << --ind << "}\n";
        
    if (program.hasConstraint()) {
        writeNegativeReasonsFunctionsPrototypes(program);
        *out << ind << "void explainPositiveLiteral(const Tuple *, std::unordered_set<std::string> &, std::vector<const Tuple*> &);\n";
        writeNegativeReasonsFunctions(program);
    }

    //generateFindSharedValueInJoinTuple(program);

    //print tuples
    *out << ind++ << "void printTuples(const std::string & predicateName, const Tuples & tuples) {\n";
    *out << ind++ << "for (const std::vector<int> * tuple : tuples) {\n";
    *out << ind << "std::cout <<predicateName<< \"(\";\n";
    *out << ind++ << "for (unsigned i = 0; i < tuple->size(); i++) {\n";
    *out << ind++ << "if (i > 0) {\n";
    *out << ind << "std::cout << \",\";\n";
    *out << --ind << "}\n";
    *out << ind << "std::cout << ConstantsManager::getInstance().unmapConstant((*tuple)[i]);\n";
    *out << --ind << "}\n";
    *out << ind << "std::cout << \").\\n\";\n";
    *out << --ind << "}\n";
    *out << --ind << "}\n";
    //handle arieties
    *out << ind++ << "void Executor::executeFromFile(const char* filename) {\n";
    *out << ind << "DLV2::InputDirector director;\n";
    *out << ind << "AspCore2InstanceBuilder* builder = new AspCore2InstanceBuilder();\n";
    *out << ind << "director.configureBuilder(builder);\n";
    *out << ind << "std::vector<const char*> fileNames;\n";
    *out << ind << "fileNames.push_back(filename);\n";
    *out << ind << "director.parse(fileNames);\n";
    *out << ind << "executeProgramOnFacts(builder->getProblemInstance());\n";
    *out << ind << "delete builder;\n";
    *out << --ind << "}\n\n";


    if (programHasConstraint) {
        *out << ind++ << "void explainPositiveLiteral(const Tuple * tuple, std::unordered_set<std::string> & open_set, std::vector<const Tuple*> & outputReasons) {\n";
        //*out << ind << "const std::vector<const Tuple*> & tupleReasons = predicateReasonsMap.at(*tuple->getPredicateName())->at(tuple->getId());\n";
        *out << ind << "std::cout << \"explainPositiveLiteral\" <<std::endl;\n";
        *out << ind << "const std::vector<const Tuple*> & tupleReasons = tuple->getPositiveReasons();\n";
        *out << ind++ << " if (tupleReasons.empty()) {\n";
        *out << ind << "outputReasons.push_back(tuple);\n";
        *out << --ind << "}\n";
        *out << ind++ << "else {\n";
        *out << ind++ << "for (const Tuple * reason : tupleReasons) {\n";
        *out << ind << "explainPositiveLiteral(reason, open_set, outputReasons);\n";
        *out << --ind << "}\n";


        *out << --ind << "}\n";
        *out << ind++ << "for (const Tuple & reason : tuple->getNegativeReasons()) {\n";
        *out << ind << "explainNegativeLiteral(&reason, open_set, outputReasons);\n";
        //*out << ind << "outputReasons.push_back(&reason);\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n\n";

        *out << ind++ << "aspc::Literal tupleToLiteral(const Tuple & tuple) {\n";
        *out << ind << "aspc::Literal literal(*tuple.getPredicateName(), tuple.isNegated());\n";
        *out << ind++ << "for (int v : tuple) {\n";
        *out << ind << "literal.addTerm(ConstantsManager::getInstance().unmapConstant(v));\n";
        *out << --ind << "}\n";
        *out << ind << "return literal;\n";
        *out << --ind << "}\n";

    }


    string tupleType = "WithoutReasons";
    if (programHasConstraint) {
        tupleType = "WithReasons";
    }
    // ---------------------- onLiteralTrue(const aspc::Literal* l) --------------------------------------//

    *out << ind++ << "inline void Executor::onLiteralTrue(const aspc::Literal* l) {\n";
    if (mode == LAZY_MODE) {

        *out << ind++ << "if(!l->isNegated()) {\n";
        //*out << ind << "std::cout<<i<<\"\\n\";\n";
        *out << ind << "std::unordered_map<std::string,PredicateWSet*>::iterator it = predicateWSetMap.find(l->getPredicateName());\n";
        *out << ind++ << "if(it==predicateWSetMap.end()) {\n";
        if (!programHasConstraint) {
            *out << ind << "l->print();\n";
            *out << ind << "std::cout<<\".\\n\";\n";
        }
        *out << --ind << "}\n";
        *out << ind++ << "else {\n";

        *out << ind << "const auto& insertResult=it->second->insert(l->getTuple" << tupleType << "());\n";

        *out << ind++ << "if(insertResult.second){\n";
        //    *out << ind << "it->second->insert(tuple);\n";
        *out << ind++ << "for(AuxMap* auxMap:predicateToAuxiliaryMaps[it->first]){\n";
        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << ind++ << "else {\n";
        *out << ind << "std::unordered_map<std::string,PredicateWSet*>::iterator it = predicateFSetMap.find(l->getPredicateName());\n";
        *out << ind++ << "if(it!=predicateFSetMap.end()) {\n";
        *out << ind << "const auto& insertResult=it->second->insert(l->getTuple" << tupleType << "());\n";
        *out << ind++ << "if(insertResult.second){\n";
        *out << ind++ << "for(AuxMap* auxMap:predicateToFalseAuxiliaryMaps[it->first]){\n";
        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
    }
    *out << --ind << "}\n";
    // ---------------------- end onLiteralTrue(const aspc::Literal* l) --------------------------------------//

    // ---------------------- onLiteralUndef(const aspc::Literal* l) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralUndef(const aspc::Literal* l) {\n";
    //*out << ind << "std::cout<<i<<\"\\n\";\n";

    //    if (mode == LAZY_MODE) {
    //        *out << ind << "std::unordered_map<std::string,PredicateWSet*>::iterator it = predicateUSetMap.find(l->getPredicateName());\n";
    //        *out << ind++ << "if(it==predicateUSetMap.end()) {\n";
    //        if (!programHasConstraint) {
    //            *out << ind << "l->print();\n";
    //            *out << ind << "std::cout<<\".\\n\";\n";
    //        }
    //        *out << --ind << "}\n";
    //        *out << ind++ << "else {\n";
    //        *out << ind << "const auto& insertResult=it->second->insert(l->getTuple" << tupleType << "());\n";
    //
    //        *out << ind++ << "if(insertResult.second){\n";
    //        //    *out << ind << "it->second->insert(tuple);\n";
    //        *out << ind++ << "for(AuxMap* auxMap:predicateToUndefAuxiliaryMaps[it->first]){\n";
    //        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
    //        *out << --ind << "}\n";
    //        *out << --ind << "}\n";
    //        *out << --ind << "}\n";
    //    }
    *out << --ind << "}\n";
    // ---------------------- end onLiteralTrue() --------------------------------------//
    // ---------------------- onLiteralTrue(int var) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralTrue(int var) {\n";
    if (mode == EAGER_MODE) {
        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "const Tuple & tuple = atomsTable[uVar];\n";
        *out << ind << "std::unordered_map<const std::string*,int>::iterator sum_it;\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";
        // *out << ind << "std::cout<<\"True \"<<minus;tuple.print();std::cout<<std::endl;\n";
        // *out << ind << "std::cout<<\"True \"<<var<<std::endl;\n";
        *out << ind << "first=true;\n";
        
        *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple.getPredicateName());\n";
        *out << ind++ << "if(uSetIt!=predicateUSetMap.end()) {\n";
        *out << ind << "uSetIt->second->erase(tuple);\n";
        *out << --ind << "}\n";

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple.getPredicateName());\n";
        *out << ind++ << "if (it == predicateWSetMap.end()) {\n";
        *out << ind << "} else {\n";
            *out << ind++ << "if (var > 0) {\n";

                *out << ind << "const auto& insertResult = it->second->insert(Tuple(tuple));\n";
                *out << ind++ << "if (insertResult.second) {\n";

                    *out << ind++ << "for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {\n";
                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
//        *out << ind << "std::cout<<\"True saved\"<<std::endl;\n";//DEBUG_PRINTING
                        
        //salvo i letterali falsi dei predicati che appaiono nel corpo di qualche aggregato

        // if(program.getAggregatePredicates().size() > 0){
        //     *out << ind++ << "if(var<0 && (";
        //     int predicateIndex=0;
        //     std::unordered_set<std::string> checkPredNames;
        //     for(const auto &  predicate :program.getAggregatePredicates()){
        //         if(checkPredNames.count(predicate.first)<=0){
        //             if(predicateIndex>0)
        //                 *out << " ||";
        //             *out << " tuple.getPredicateName() == &_"<<predicate.first;
        //             predicateIndex++;
        //             checkPredNames.insert(predicate.first);
        //         }
        //     }
        //     *out << ")){\n";
        //         *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it_false = predicateFSetMap.find(tuple.getPredicateName());\n";
        //         *out << ind++ << "if (it_false == predicateFSetMap.end()) {\n";
        //         *out << ind << "} else {\n";
        //             *out << ind << "const auto& insertResult = it_false->second->insert(Tuple(tuple));\n";
        //             *out << ind++ << "if (insertResult.second) {\n";
        //                 *out << ind++ << "for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[it_false->first]) {\n";
        //                     *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        //                 *out << --ind << "}\n";
        //             *out << --ind << "}\n";
        //         *out << --ind << "}\n";
        //     *out << --ind << "}\n";

        // }
        
        //--------------------------------------------------Aggregate structure update--------------------------------------------------
        *out << ind++ << "for(auto& reasonMap:positiveAggrReason){\n";
            *out << ind++ << "for(auto& pair :reasonMap){\n";
                *out << ind << "pair.second.addLevel();\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << ind++ << "for(auto& reasonMap:negativeAggrReason){\n";
            *out << ind++ << "for(auto& pair :reasonMap){\n";
                *out << ind << "pair.second.addLevel();\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

        *out << ind << "currentReasonLevel++;\n";
        for(const auto& pair: aggrIdentifierForAggregateBody){
            const aspc::ArithmeticRelationWithAggregate* aggr = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[pair.second[0].first].getFormulas()[pair.second[0].second];
            int startingLiteral=0;
            for(const aspc::Literal& starter : aggr->getAggregate().getAggregateLiterals()){
                *out << ind++ << "if(tuple.getPredicateName() == &_"<<starter.getPredicateName()<<"){\n";
//                *out << ind << "std::cout<<\""<<starter.getPredicateName()<<" lit\"<<std::endl;\n";//DEBUG_PRINTING
                        
                bool checkFormat = checkTupleFormat(starter,"",false);
                std::unordered_set<std::string> boundVars;
                
                for(int i=0;i<starter.getAriety();i++){
                    if(starter.isVariableTermAt(i)&&boundVars.count(starter.getTermAt(i))==0){
                        *out << ind << "int "<<starter.getTermAt(i)<<" = tuple["<<i<<"];\n";
                        boundVars.insert(starter.getTermAt(i));
                    }
                }
                if(!starter.isNegated())
                    *out << ind++ << "if(var > 0){\n";
                else
                    *out << ind++ << "if(var < 0){\n";
                        int closingPars=0;
                        int buildIndex=0;
                        std::string jointuple;
                        std::vector<std::vector<std::string>> previousLit;
                        previousLit.push_back({starter.getPredicateName(),std::to_string(starter.isNegated()),std::to_string(startingLiteral)});
                        for(const aspc::Literal& li : aggr->getAggregate().getAggregateLiterals()){
                            for(int i=0;i<li.getAriety();i++){
                                std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
                                jointuple+=mapStringConstant+",";
                            }
                            if(buildIndex!=startingLiteral){
                                
                                if(li.isBoundedLiteral(boundVars)){
                                    std::string literalTerms;
                                    for(int i=0;i<li.getAriety();i++){
                                        if(i>0)
                                            literalTerms+=",";
                                        std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
                                        literalTerms+=mapStringConstant;
                                    }
                                    
                                    if(li.isPositiveLiteral()){
                                        *out << ind << "const Tuple* tuple"<<buildIndex<<" = w"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
                                        *out << ind++ << "if(tuple"<<buildIndex<<"!=NULL){\n";
                                        for(auto & pair:previousLit){
                                            if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
                                                std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
                                                *out << ind++ << "if(";
                                                for(int i=0;i<li.getAriety();i++){
                                                    if (i>0){
                                                        *out << " || ";
                                                    }
                                                    *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
                                                }
                                                *out << "){\n";
                                                
                                                closingPars++;
                                            }
                                        }

                                    }else{
                                        *out << ind << "const Tuple negativeTuple"<<buildIndex<<"({"<<literalTerms<<"},&_"<<li.getPredicateName()<<",true);\n";
                                        *out << ind << "const Tuple* tuple"<<buildIndex<<" = u"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
                                        *out << ind++ << "if(w"<<li.getPredicateName()<<".find(negativeTuple"<<buildIndex<<")==NULL && tuple"<<buildIndex<<"==NULL){\n";
                                            *out << ind << "tuple"<<buildIndex<<"=&negativeTuple"<<buildIndex<<";\n";
                                            for(auto & pair:previousLit){
                                                if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
                                                    std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
                                                    *out << ind++ << "if(";
                                                    for(int i=0;i<li.getAriety();i++){
                                                        if (i>0){
                                                            *out << " || ";
                                                        }
                                                        *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
                                                    }
                                                    *out << "){\n";
                                                    
                                                    closingPars++;
                                                }
                                            }
                                    }
                                    closingPars++;
                                }else{
                                    std::string literalTerms;
                                    std::string boundTermsIndex;
                                    bool first=true;
                                    for(int i=0;i<li.getAriety();i++){
                                        if(!li.isVariableTermAt(i) || boundVars.count(li.getTermAt(i))>0){
                                            if(!first)
                                                literalTerms+=",";
                                            std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
                                            literalTerms+=mapStringConstant;
                                            first=false;
                                            boundTermsIndex+= std::to_string(i)+"_";
                                        }
                                    }
                                    *out << ind << "const std::vector<const Tuple*>* tuples"<<buildIndex<<" = &p"<<li.getPredicateName()<<"_"<<boundTermsIndex<<".getValues({"<<literalTerms<<"});\n";
                                    *out << ind++ << "for(int i_"<<buildIndex<<"=0;i_"<<buildIndex<<"<tuples"<<buildIndex<<"->size();i_"<<buildIndex<<"++){\n";
                                    closingPars++;
                                    *out << ind << "const Tuple* tuple"<<buildIndex<<"=tuples"<<buildIndex<<"->at(i_"<<buildIndex<<");\n";
                                    if(checkTupleFormat(li,std::to_string(buildIndex),true))
                                        closingPars++;

                                    for(auto & pair:previousLit){
                                        if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
                                            std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
                                            *out << ind++ << "if(";
                                            for(int i=0;i<li.getAriety();i++){
                                                if (i>0){
                                                    *out << " || ";
                                                }
                                                *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
                                            }
                                            *out << "){\n";
                                            
                                            closingPars++;
                                        }
                                    }
                                    
                                    for(int i=0;i<li.getAriety();i++){
                                        if(li.isVariableTermAt(i)&&boundVars.count(li.getTermAt(i))==0){
                                            *out << ind << "int "<<li.getTermAt(i)<<" = tuple"<<buildIndex<<"->at("<<i<<");\n";
                                            boundVars.insert(li.getTermAt(i));
                                        }
                                    }
                                        
                                }
                                previousLit.push_back({li.getPredicateName(),std::to_string(li.isNegated()),std::to_string(buildIndex)});
                            }
                            buildIndex++;
                        }
//                        *out << ind << "std::cout<<\"End literals\"<<std::endl;\n";//DEBUG_PRINTING
                                
                        for(const aspc::ArithmeticRelation& inequality : aggr->getAggregate().getAggregateInequalities()){
                            if(inequality.isBoundedRelation(boundVars)){
                                *out << ind++ << "if("<<inequality.getStringRep()<<"){\n";
                                closingPars++;
                            }else if(inequality.isBoundedValueAssignment(boundVars)){
                                jointuple+=inequality.getAssignedVariable(boundVars)+",";
                                *out << ind << "int "<<inequality.getAssignmentStringRep(boundVars)<<";\n";
                                boundVars.insert(inequality.getAssignedVariable(boundVars));
                            }
                        }
                            *out << ind << "Tuple t({"<<jointuple.substr(0,jointuple.length()-1)<<"},&_"<<aggr->getJoinTupleName()<<");\n";

                            for(const auto& aggrIdentifier: pair.second){
                                const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
                                int ruleId = aggrIdentifier.first;
                                int aggrIndex = aggrIdentifier.second;
                                std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);

                                *out << ind++ << "{\n";
                                        //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                        *out << ind << "std::vector<int> aggrKey({";
                                        bool first=true;
                                        std::string aggrVarProj;
                                        std::string aggrVarTuple;
                                        for(unsigned v: aggregateVariablesIndex[key]){
                                            if(!first){
                                                *out << ",";
                                                aggrVarTuple+=",";
                                            }
                                            *out << "t["<<v<<"]";
                                            aggrVarTuple+="t["+std::to_string(v)+"]";
                                            aggrVarProj+=std::to_string(v)+"_";
                                            first=false;
                                        }
                                        *out << "});\n";
                                        
                                        *out << ind++ << "if(aggrKey[0]>=0){\n";
                                        {
                                            //Positive aggr var
                                            //--------------------------SAVING NEW TRUE JOIN TUPLE--------------------------
                                            *out << ind++ << "if(w"<<aggregate->getJoinTupleName()<<".find(t)==NULL){\n";
                                                *out << ind++ << "if(u"<< aggregate->getJoinTupleName() <<".find(t))\n";
                                                *out << ind-- << "u" << aggregate->getJoinTupleName() <<".erase(t);\n";

                                                *out << ind << "const auto& insertResult = w" << aggregate->getJoinTupleName() <<".insert(Tuple(t));\n";
                                                *out << ind++ << "if (insertResult.second) {\n";
                                                    *out << ind++ << "for(AuxMap* auxMap : predicateToAuxiliaryMaps[&_"<<aggregate->getJoinTupleName()<<"]){\n";
                                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                                //--------------------------END SAVING NEW TRUE JOIN TUPLE--------------------------
                                                std::string sharedVarIndex;
                                                for(unsigned v: sharedVariablesIndexesMap[key])
                                                    sharedVarIndex+=std::to_string(v)+"_";
                                                std::string comma=sharedVarIndex==""? "":",";
                                                *out << ind << "auto& trueSet = trueAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                                *out << ind << "auto& undefSet = undefAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            
                                                *out << ind++ << "if(undefSet.find(aggrKey)!=undefSet.end()){\n";
                                                    *out << ind << "undefSet.erase(aggrKey);\n";
                                                    if(aggregate->getAggregate().isSum()){
                                                        *out << ind << "possibleSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                                    }
                                                *out << --ind << "}\n";

                                                *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                    *out << ind << "trueSet.insert(aggrKey);\n";
                                                    if(aggregate->getAggregate().isSum()){
                                                        *out << ind << "actualSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]+=aggrKey[0];\n";
                                                    }
                                                    //--------------------------UPDATE POSITIVE REASON STRUCTURE--------------------------
                                                    int buildIndex=0;

                                                    *out << ind << "auto& reas = positiveAggrReason["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                                    
                                                    *out << ind++ << "while(reas.getCurrentLevel()<currentReasonLevel)\n";
                                                        *out << ind-- << "reas.addLevel();\n";
                                                    *out << ind << "reas.insert(var);\n";
                                                    // *out << ind << "std::cout << currentReasonLevel <<std::endl;\n";
                                                    // *out << ind << "tuple.print();std::cout<<\"Added to positive reason\"<<std::endl;\n";
                                                    for(const aspc::Literal& li : aggregate->getAggregate().getAggregateLiterals()){
                                                        if(buildIndex!=startingLiteral){
                                                            *out << ind++ << "{\n";
                                                                *out << ind << "const auto & it = tupleToVar.find(*tuple"<<buildIndex<<");\n";
                                                                *out << ind++ << "if(it != tupleToVar.end()) {\n";
                                                                    std::string sign = li.isNegated() ? "*-1":"";
                                                                    // *out << ind << "tuple"<<buildIndex<<"->print();std::cout<<\"Added to positive reason\"<<std::endl;\n";
                                                                    *out << ind << "reas.insert(it->second"<<sign<<");\n";
                                                                *out << --ind << "}\n";
                                                            *out << --ind << "}\n";
                                                        }else{
                                                        }
                                                        buildIndex++;
                                                    }
                                                    //--------------------------END UPDATE POSITIVE REASON STRUCTURE--------------------------
                                                *out << --ind << "}\n";
                                                //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                            *out << --ind << "}\n"; 
                                            
                                        }
                                        *out << --ind << "}else{\n";
                                        {
                                            ind++;
                                            //--------------------------SAVING NEW TRUE JOIN TUPLE--------------------------
                                            *out << ind++ << "if(nw"<<aggregate->getJoinTupleName()<<".find(t)==NULL){\n";
                                                *out << ind++ << "if(nu"<< aggregate->getJoinTupleName() <<".find(t))\n";
                                                *out << ind-- << "nu" << aggregate->getJoinTupleName() <<".erase(t);\n";

                                                *out << ind << "const auto& insertResult = nw" << aggregate->getJoinTupleName() <<".insert(Tuple(t));\n";
                                                *out << ind++ << "if (insertResult.second) {\n";
                                                    *out << ind++ << "for(AuxMap* auxMap : predicateToNegativeAuxiliaryMaps[&_"<<aggregate->getJoinTupleName()<<"]){\n";
                                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n"; 
                                            //--------------------------END SAVING NEW TRUE JOIN TUPLE--------------------------
                                            std::string sharedVarIndex;
                                            for(unsigned v: sharedVariablesIndexesMap[key])
                                                sharedVarIndex+=std::to_string(v)+"_";
                                            std::string comma=sharedVarIndex==""? "":",";
                                            *out << ind << "auto& trueSet = trueNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            *out << ind << "auto& undefSet = undefNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            if(aggregate->getAggregate().isSum()){
                                                *out << ind++ << "if(undefSet.find(aggrKey)!=undefSet.end()){\n";
                                                    *out << ind << "undefSet.erase(aggrKey);\n";
                                                    //--------------------------UPDATE NEGATIVE REASON STRUCTURE--------------------------
                                                    int buildIndex=0;

                                                    *out << ind << "auto& reas = negativeAggrReason["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                                    
                                                    *out << ind++ << "while(reas.getCurrentLevel()<currentReasonLevel)\n";
                                                        *out << ind-- << "reas.addLevel();\n";
                                                    *out << ind << "reas.insert(var);\n";
                                                    // *out << ind << "tuple.print();std::cout<<\"Added to positive reason\"<<std::endl;\n";

                                                    for(const aspc::Literal& li : aggregate->getAggregate().getAggregateLiterals()){
                                                        if(buildIndex!=startingLiteral){
                                                            *out << ind++ << "{\n";
                                                                *out << ind << "const auto & it = tupleToVar.find(*tuple"<<buildIndex<<");\n";
                                                                *out << ind++ << "if(it != tupleToVar.end()) {\n";
                                                                    std::string sign = li.isNegated() ? "*-1":"";
                                                                    // *out << ind << "tuple"<<buildIndex<<"->print();std::cout<<\"Added to positive reason\"<<std::endl;\n";
                                                                    *out << ind << "reas.insert(it->second"<<sign<<");\n";
                                                                *out << --ind << "}\n";
                                                            *out << --ind << "}\n";
                                                        }else{
                                                        }
                                                        buildIndex++;
                                                    }
                                                    //--------------------------END UPDATE NEGATIVE REASON STRUCTURE--------------------------
                                                    *out << ind << "possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]+=aggrKey[0];\n";
                                                *out << --ind << "}\n";
                                            }else{
                                                *out << ind++ << "if(undefSet.find(aggrKey)!=undefSet.end()){\n";
                                                    *out << ind << "undefSet.erase(aggrKey);\n";
                                                *out << --ind << "}\n";
                                                *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                    *out << ind << "trueSet.insert(aggrKey);\n";
                                                    //--------------------------UPDATE NEGATIVE REASON STRUCTURE--------------------------
                                                    int buildIndex=0;

                                                    *out << ind << "auto& reas = positiveAggrReason["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                                    
                                                    *out << ind++ << "while(reas.getCurrentLevel()<currentReasonLevel)\n";
                                                        *out << ind-- << "reas.addLevel();\n";
                                                    *out << ind << "reas.insert(var);\n";
                                                    // *out << ind << "tuple.print();std::cout<<\"Added to positive reason\"<<std::endl;\n";

                                                    for(const aspc::Literal& li : aggregate->getAggregate().getAggregateLiterals()){
                                                        if(buildIndex!=startingLiteral){
                                                            *out << ind++ << "{\n";
                                                                *out << ind << "const auto & it = tupleToVar.find(*tuple"<<buildIndex<<");\n";
                                                                *out << ind++ << "if(it != tupleToVar.end()) {\n";
                                                                    std::string sign = li.isNegated() ? "*-1":"";
                                                                    // *out << ind << "tuple"<<buildIndex<<"->print();std::cout<<\"Added to positive reason\"<<std::endl;\n";
                                                                    *out << ind << "reas.insert(it->second"<<sign<<");\n";
                                                                *out << --ind << "}\n";
                                                            *out << --ind << "}\n";
                                                        }else{
                                                        }
                                                        buildIndex++;
                                                    }
                                                    //--------------------------END UPDATE NEGATIVE REASON STRUCTURE--------------------------
                                                *out << --ind << "}\n";
                                            }
                                            
                                        }
                                        *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            }

                        while(closingPars>0){
                            closingPars--;
                            *out << --ind << "}\n";
                        }
                        
                    *out << --ind << "}else{\n";
                        boundVars.clear();
                        *out << ++ind << "const std::vector<const Tuple*>& tuplesU = u_"<<aggr->getJoinTupleName()<<aggr->getAggrLitProj(startingLiteral)<<".getValues({";
                        for(int i=0;i<starter.getAriety();i++){
                            if(i>0)
                                *out << ",";
                            std::string mapStringConstant =  !isVariable(starter.getTermAt(i)) &&!isInteger(starter.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(starter.getTermAt(i)) + "\")" : starter.getTermAt(i);

                            *out << mapStringConstant;
                            if(starter.isVariableTermAt(i))
                                boundVars.insert(starter.getTermAt(i)); 
                        }
                        *out << "});\n";
                        *out << ind++ << "while(!tuplesU.empty()){\n";
                            
                            *out << ind << "Tuple t(*tuplesU.back());\n";
                            //--------------------------EREASING UNDEF--------------------------
                            *out << ind << "u"<<aggr->getJoinTupleName()<<".erase(*tuplesU.back());\n";
                            // *out << ind << "std::cout<<\"Erasing from undef \"<<u"<<aggr->getJoinTupleName()<<".getTuples().size()<<\" \"<<u_"<<aggr->getJoinTupleName()<<".getValues({}).size()<<std::endl;\n";

                            //--------------------------END EREASING UNDEF--------------------------

                            for(const auto& aggrIdentifier: pair.second){
                            const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
                            int ruleId = aggrIdentifier.first;
                            int aggrIndex = aggrIdentifier.second;
                            std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);
                            *out << ind++ << "{\n";
                                boundVars.clear();
                                for(int i=0;i<starter.getAriety();i++){
                                    if(starter.isVariableTermAt(i))
                                        boundVars.insert(starter.getTermAt(i)); 
                                }
                                for(unsigned v : sharedVariablesIndexesMap[key]){
                                    if(boundVars.count(aggregate->getAggregate().getTermAt(v))<=0){
                                        boundVars.insert(aggregate->getAggregate().getTermAt(v));
                                        *out << ind << "int "<<aggregate->getAggregate().getTermAt(v)<<" = t["<<v<<"];\n";
                                    }else{
                                        *out << ind << "//bound var"<<v<<"\n";
                                    }
                                }
                                //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                *out << ind << "std::vector<int> aggrKey({";
                                bool first=true;
                                std::string aggrVarProj;
                                std::string aggrVarTuple;
                                for(unsigned v: aggregateVariablesIndex[key]){
                                    if(!first){
                                        *out << ",";
                                        aggrVarTuple+=",";
                                    }
                                    *out << "t["<<v<<"]";
                                    aggrVarTuple+="t["+std::to_string(v)+"]";
                                    aggrVarProj+=std::to_string(v)+"_";
                                    first=false;
                                }
                                *out << "});\n";
                                *out << ind << "auto& undefSet = undefAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                        
                                std::string sharedVarProj;
                                for(unsigned v: sharedVariablesIndexesMap[key]){
                                    sharedVarProj+=std::to_string(v)+"_";
                                }
                                if(sharedVariablesMap[key]!=""){
                                    *out << ind++ << "if(u_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                }else{
                                    *out << ind++ << "if(u_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                }
                                    *out << ind++ << "if(undefSet.find(aggrKey)!=undefSet.end()){\n";
                                        *out << ind << "undefSet.erase(aggrKey);\n";
                                        if(aggregate->getAggregate().isSum()){
                                            *out << ind << "possibleSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                        }
                                        
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                //--------------------------UPDATE NEGATIVE RESON STRUCTURE--------------------------
                                *out << ind << "auto& reas = negativeAggrReason["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                                
                                *out << ind++ << "while(reas.getCurrentLevel()<currentReasonLevel)\n";
                                    *out << ind-- << "reas.addLevel();\n";
                                *out << ind << "reas.insert(var);\n";
                                // *out << ind << "tuple.print();std::cout<<\"Added to negative reason\"<<std::endl;\n";
                            
                                //--------------------------END UPDATE NEGATIVE RESON STRUCTURE--------------------------

                            *out << --ind << "}\n";
                            }
                        *out << --ind << "}\n";
                        boundVars.clear();
                        *out << ind << "const std::vector<const Tuple*>& tuplesNU = nu_"<<aggr->getJoinTupleName()<<aggr->getAggrLitProj(startingLiteral)<<".getValues({";
                        for(int i=0;i<starter.getAriety();i++){
                            if(i>0)
                                *out << ",";
                            std::string mapStringConstant =  !isVariable(starter.getTermAt(i)) &&!isInteger(starter.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(starter.getTermAt(i)) + "\")" : starter.getTermAt(i);
                            *out << mapStringConstant;
                            if(starter.isVariableTermAt(i))
                                boundVars.insert(starter.getTermAt(i)); 
                            
                        }
                        *out << "});\n";
                        *out << ind++ << "while(!tuplesNU.empty()){\n";
                            
                            *out << ind << "Tuple t(*tuplesNU.back());\n";
                            //--------------------------EREASING UNDEF--------------------------
                            *out << ind << "nu"<<aggr->getJoinTupleName()<<".erase(*tuplesNU.back());\n";
                            // *out << ind << "std::cout<<\"Erasing from undef \"<<u"<<aggr->getJoinTupleName()<<".getTuples().size()<<\" \"<<u_"<<aggr->getJoinTupleName()<<".getValues({}).size()<<std::endl;\n";

                            //--------------------------END EREASING UNDEF--------------------------

                            for(const auto& aggrIdentifier: pair.second){
                            const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
                            int ruleId = aggrIdentifier.first;
                            int aggrIndex = aggrIdentifier.second;
                            std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);
                            *out << ind++ << "{\n";
                                boundVars.clear();
                                for(int i=0;i<starter.getAriety();i++){
                                    if(starter.isVariableTermAt(i))
                                        boundVars.insert(starter.getTermAt(i)); 
                                }
                                for(unsigned v : sharedVariablesIndexesMap[key]){
                                    if(boundVars.count(aggregate->getAggregate().getTermAt(v))<=0){
                                        boundVars.insert(aggregate->getAggregate().getTermAt(v));
                                        *out << ind << "int "<<aggregate->getAggregate().getTermAt(v)<<" = t["<<v<<"];\n";
                                    }else{
                                        *out << ind << "//bound var"<<v<<"\n";
                                    }
                                }
                                //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                *out << ind << "std::vector<int> aggrKey({";
                                bool first=true;
                                std::string aggrVarProj;
                                std::string aggrVarTuple;
                                for(unsigned v: aggregateVariablesIndex[key]){
                                    if(!first){
                                        *out << ",";
                                        aggrVarTuple+=",";
                                    }
                                    *out << "t["<<v<<"]";
                                    aggrVarTuple+="t["+std::to_string(v)+"]";
                                    aggrVarProj+=std::to_string(v)+"_";
                                    first=false;
                                }
                                *out << "});\n";
                                *out << ind << "auto& undefSet = undefNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                *out << ind << "auto& trueSet = trueNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                std::string sharedVarProj;
                                for(unsigned v: sharedVariablesIndexesMap[key]){
                                    sharedVarProj+=std::to_string(v)+"_";
                                }
                                if(sharedVariablesMap[key]!=""){
                                    *out << ind++ << "if(nu_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                }else{
                                    *out << ind++ << "if(nu_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                }
                                    if(sharedVariablesMap[key]!=""){
                                        *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                    }else{
                                        *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                    }
                                        *out << ind++ << "if(undefSet.find(aggrKey)!=undefSet.end()){\n";
                                            *out << ind << "undefSet.erase(aggrKey);\n";
                                            //add negative key to possible sum
                                            *out << ind << "possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]+=aggrKey[0];\n";
                                        *out << --ind << "}\n";
                                        if(aggregate->getAggregate().isSum()){
                                            
                                            *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                *out << ind << "trueSet.insert(aggrKey);\n";
                                                //sub negative key to actual sum
                                                *out << ind << "actualNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                            *out << --ind << "}\n";
                                        }
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                if(aggregate->getAggregate().isSum()){
                                    *out << ind << "auto& reas = positiveAggrReason["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                }else{
                                    *out << ind << "auto& reas = negativeAggrReason["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                }
                                *out << ind++ << "while(reas.getCurrentLevel()<currentReasonLevel)\n";
                                    *out << ind-- << "reas.addLevel();\n";
                                *out << ind << "reas.insert(var);\n";
                            *out << --ind << "}\n";
                            }
                        *out << --ind << "}\n";

                    *out << --ind << "}\n";
                    if(checkFormat)
                            *out << --ind << "}\n";
                *out << --ind << "}\n";
                startingLiteral++;
            }
        }
        for(const aspc::Rule& r: program.getRules()){
            int litIndex=0;
            for(const aspc::Literal&  l : r.getBodyLiterals()){
                bool hasSharedVar = false;
                for(const aspc::ArithmeticRelationWithAggregate& aggr:r.getArithmeticRelationsWithAggregate()){
                    if(sharedVariablesMap[std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex())]!="")
                        hasSharedVar=true;

                }
                if(hasSharedVar){
                    *out << ind++ << "if(tuple.getPredicateName() == &_" << l.getPredicateName()<<"){\n";
                        updateUndefinedSharedVariablesMap(r,litIndex);
                    *out << --ind <<"}\n";
                }
                litIndex++;
            }
        }

        // *out << ind << "positiveAggrReason[0][{}].print();\n";
        // *out << ind << "std::cout<<\"Current level \"<<positiveAggrReason[0][{}].getCurrentLevel()<<std::endl;\n";
        // *out << ind << "std::cout<<\"End lit true\"<<std::endl;\n";
        // *out << ind << "std::cout<<\"Negative aggr reason: \"<<negativeAggrReason[0][{}].size()<<std::endl;\n";
        // *out << ind << "for(auto& pair :negativeAggrReason[0]){ std::cout<<pair.first.size()<<std::endl; for(int v: pair.second) {unsigned uv = v > 0 ? v : -v; atomsTable[uv].print();}std::cout<<std::endl;}\n";
        // *out << ind << "std::cout<<\"Positive aggr reason: \"<<positiveAggrReason[0][{}].size()<<std::endl;\n";
        // *out << ind << "for(int v:positiveAggrReason[0][{}]){unsigned uv = v > 0 ? v : -v; atomsTable[uv].print();}std::cout<<std::endl;\n";
        // *out << ind << "for(const auto& p : actualSum[0]) std::cout<<\"true sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : possibleSum[0]) std::cout<<\"undef sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : actualNegativeSum[0]) std::cout<<\"true negative sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : possibleNegativeSum[0]) std::cout<<\"undef negative sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : trueAggrVars[0]) std::cout<<\"true count \"<<p.second.size()<<std::endl;\n";
        // *out << ind << "for(const auto& p : undefAggrVars[0]) std::cout<<\"undef count \"<<p.second.size()<<std::endl;\n";
        // *out << ind << "for(const auto& p : trueNegativeAggrVars[0]) std::cout<<\"true negative count \"<<p.second.size()<<std::endl;\n";
        // *out << ind << "for(const auto& p : undefNegativeAggrVars[0]) std::cout<<\"undef negative count \"<<p.second.size()<<std::endl;\n";
#ifdef EAGER_DEBUG
        *out << ind << "std::cout<<\"on literal true \";\n";
        *out << ind << "std::cout<<var<<\"\\n\";\n";
        *out << ind << "tuple.print();\n";
        *out << ind << "std::cout<<\"\\n\";\n";
#endif

    }
    
    *out << --ind << "}\n";


    // ---------------------- onLiteralUndef(int var) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralUndef(int var) {\n";
    if (mode == EAGER_MODE) {
        //*out << ind << "std::cout<<\"undef \"<<var<<std::endl;\n";
        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "const Tuple & tuple = atomsTable[uVar];\n";

        *out << ind << "std::unordered_map<const std::string*,int>::iterator sum_it;\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";
        // *out << ind << "std::cout<<\"Undef \"<<minus;tuple.print();std::cout<<std::endl;\n";

        *out << ind << "reasonMapping.erase(-var);\n";
        *out << ind << "reasonMapping.erase(-1);\n";
        *out << ind++ << "if(first){\n";
            // *out << ind << "first=false;";
            // *out << ind << "std::cout<<\"Explain propagation \"<<reasonMapping.size()<<std::endl;\n";
            // *out << ind++ << "for(int i=2;i<reasonMapping.size();i++){\n";
            //     *out << ind << "std::cout<<\"Explain \"<<i<<std::endl;\n";
            //     *out << ind << "explainAggrLiteral(i);\n";
            // *out << --ind << "}\n";
            // *out << ind << "reasonMapping.clear();\n";
        *out << --ind << "}\n";
        // *out << ind << "std::cout<<\"Unde \"<<minus<<var<<std::endl;\n";
        // *out << ind << "std::cout<<\"Undef \"<<std::endl;\n";
#ifdef EAGER_DEBUG
        *out << ind << "std::cout<<\"on literal undef \";\n";
        *out << ind << "std::cout<<var<<\"\\n\";\n";
        *out << ind << "tuple.print();\n";
        *out << ind << "std::cout<<\"\\n\";\n";
#endif

        *out << ind++ << "if (var > 0) {\n";
            *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple.getPredicateName());\n";
            *out << ind++ << "if (wSetIt != predicateWSetMap.end()) {\n";
                // *out << ind << "std::cout<<\"Erase from true\"<<std::endl;\n";
                *out << ind << "wSetIt->second->erase(tuple);\n";
                // *out << ind << "if(wSetIt->second->find(tuple)!=NULL) std::cout<<\"Tuple not erased from true for \"<<tuple.getPredicateName()<<std::endl;\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

        // if(program.getAggregatePredicates().size() > 0){
        //     *out << ind++ << "if(var<0 && (";
        //     int predicateIndex=0;
        //     for(const auto &  predicate :program.getAggregatePredicates()){
        //         if(predicateIndex>0)
        //             *out << " ||";
        //         *out << " tuple.getPredicateName() == &_"<<predicate.first;
        //         predicateIndex++;
        //     }
        //     *out << ")){\n";
        //         *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator falseSetIt = predicateFSetMap.find(tuple.getPredicateName());\n";
        //         *out << ind++ << "if (falseSetIt != predicateFSetMap.end()) {\n";
        //         // *out << ind << "std::cout<<\"Erase from false\"<<std::endl;\n";
        //         *out << ind << "falseSetIt->second->erase(tuple);\n";
        //         // *out << ind << "if(falseSetIt->second->find(tuple)!=NULL) std::cout<<\"Tuple not erased from false for \"<<tuple.getPredicateName()<<std::endl;\n";
        //         *out << --ind << "}\n";
        //     *out << --ind << "}\n";
        // }

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple.getPredicateName());\n";
        *out << ind++ << "if (it == predicateUSetMap.end()) {\n";
        *out << ind << "} else {\n";
        
        *out << ind << "const auto& insertResult = it->second->insert(Tuple(tuple));\n";
        *out << ind++ << "if (insertResult.second) {\n";
        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[it->first]) {\n";
        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";

        //--------------------------------------------------Aggregate structure update--------------------------------------------------

        *out << ind++ << "for(auto& reasonMap:positiveAggrReason){\n";
            *out << ind++ << "for(auto& pair :reasonMap){\n";
                *out << ind << "pair.second.eraseCurrentLevel();\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << ind++ << "for(auto& reasonMap:negativeAggrReason){\n";
            *out << ind++ << "for(auto& pair :reasonMap){\n";
                *out << ind << "pair.second.eraseCurrentLevel();\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << ind++ << "if(currentReasonLevel>0)\n";
            *out << ind-- << "currentReasonLevel--;\n";

        for(const auto& pair: aggrIdentifierForAggregateBody){
            const aspc::ArithmeticRelationWithAggregate* aggr = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[pair.second[0].first].getFormulas()[pair.second[0].second];
            int startingLiteral=0;
            for(const aspc::Literal& starter : aggr->getAggregate().getAggregateLiterals()){
                *out << ind++ << "if(tuple.getPredicateName() == &_"<<starter.getPredicateName()<<" && tuple.size()=="<<starter.getAriety()<<"){\n";
                bool checkFormat = checkTupleFormat(starter,"",false);
                std::unordered_set<std::string> boundVars;
                
                for(int i=0;i<starter.getAriety();i++){
                    if(starter.isVariableTermAt(i)&&boundVars.count(starter.getTermAt(i))==0){
                        *out << ind << "int "<<starter.getTermAt(i)<<" = tuple["<<i<<"];\n";
                        boundVars.insert(starter.getTermAt(i));
                    }
                }
                if(!starter.isNegated())
                    *out << ind++ << "if(var > 0){\n";
                else
                    *out << ind++ << "if(var < 0){\n";

                        //letterale vero diventa indefinito
                        *out << ind << "const std::vector<const Tuple*>& tuples = p_"<<aggr->getJoinTupleName()<<aggr->getAggrLitProj(startingLiteral)<<".getValues({";
                        for(int i=0;i<starter.getAriety();i++){
                            if(i>0)
                                *out << ",";
                            std::string mapStringConstant =  !isVariable(starter.getTermAt(i)) &&!isInteger(starter.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(starter.getTermAt(i)) + "\")" : starter.getTermAt(i);
                            *out << mapStringConstant;
                        }
                        *out << "});\n";

                        *out << ind++ << "while(!tuples.empty()){\n";
                            
                            *out << ind << "Tuple t(*tuples.back());\n";
                            //--------------------------EREASING TRUE--------------------------
                            *out << ind << "w"<<aggr->getJoinTupleName()<<".erase(*tuples.back());\n";
                            //--------------------------END EREASING TRUE--------------------------
                            // *out << ind << "std::cout<<\"Erasing from true \"<<w"<<aggr->getJoinTupleName()<<".getTuples().size()<<\" \"<<p_"<<aggr->getJoinTupleName()<<".getValues({}).size()<<std::endl;\n";

                            *out << ind++ << "if(u"<<aggr->getJoinTupleName()<<".find(Tuple(t)) == NULL){\n";
                                //--------------------------INSERT UNDEF--------------------------
                                *out << ind << "const auto& insertResult = u" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
                                *out << ind++ << "if (insertResult.second) {\n";
                                    *out << ind++ << "for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                    *out << --ind << "}\n";
                                    // *out << ind << "std::cout<<\"Insert in undef \"<<u"<<aggr->getJoinTupleName()<<".getTuples().size()<<std::endl;\n";
                                *out << --ind << "}\n";
                                    
                                //--------------------------END INSERT UNDEF--------------------------
                            

                                for(const auto& aggrIdentifier: pair.second){
                                    const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
                                    int ruleId = aggrIdentifier.first;
                                    int aggrIndex = aggrIdentifier.second;
                                    std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);
                                    *out << ind++ << "{\n";
                                        boundVars.clear();
                                        for(int i=0;i<starter.getAriety();i++){
                                            if(starter.isVariableTermAt(i))
                                                boundVars.insert(starter.getTermAt(i)); 
                                        }
                                        for(unsigned v : sharedVariablesIndexesMap[key]){
                                            if(boundVars.count(aggregate->getAggregate().getTermAt(v))<=0){
                                                boundVars.insert(aggregate->getAggregate().getTermAt(v));
                                                *out << ind << "int "<<aggregate->getAggregate().getTermAt(v)<<" = t["<<v<<"];\n";
                                            }
                                        }

                                        //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------

                                        *out << ind << "std::vector<int> aggrKey({";
                                        bool first=true;
                                        std::string aggrVarProj;
                                        std::string aggrVarTuple;
                                        for(unsigned v: aggregateVariablesIndex[key]){
                                            if(!first){
                                                *out << ",";
                                                aggrVarTuple+=",";
                                            }
                                            *out << "t["<<v<<"]";
                                            aggrVarTuple+="t["+std::to_string(v)+"]";
                                            aggrVarProj+=std::to_string(v)+"_";
                                            first=false;
                                        }
                                        *out << "});\n";
                                        std::string sharedVarProj;
                                        for(unsigned v: sharedVariablesIndexesMap[key]){
                                            sharedVarProj+=std::to_string(v)+"_";
                                        }
                                        *out << ind << "auto& trueSet = trueAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                        *out << ind << "auto& undefSet = undefAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                        
                                        if(sharedVariablesMap[key]!=""){
                                            *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                        }else{
                                            *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                        }
                                            *out << ind++ << "if(trueSet.find(aggrKey)!=trueSet.end()){\n";
                                                *out << ind << "trueSet.erase(aggrKey);\n";
                                                if(aggregate->getAggregate().isSum()){
                                                    *out << ind << "actualSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                                }
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        *out << ind++ << "if(undefSet.find(aggrKey)==undefSet.end()){\n";
                                            *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                *out << ind << "undefSet.insert(aggrKey);\n";
                                                if(aggregate->getAggregate().isSum()){
                                                    *out << ind << "possibleSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]+=aggrKey[0];\n";
                                                }
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                    *out << --ind << "}\n";
                                }
                            *out << --ind << "}\n";

                        *out << --ind << "}\n";
                    
                        *out << ind << "const std::vector<const Tuple*>& tuplesN = np_"<<aggr->getJoinTupleName()<<aggr->getAggrLitProj(startingLiteral)<<".getValues({";
                        for(int i=0;i<starter.getAriety();i++){
                            if(i>0)
                                *out << ",";
                            std::string mapStringConstant =  !isVariable(starter.getTermAt(i)) &&!isInteger(starter.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(starter.getTermAt(i)) + "\")" : starter.getTermAt(i);
                            *out << mapStringConstant;
                        }
                        *out << "});\n";

                        *out << ind++ << "while(!tuplesN.empty()){\n";
                            
                            *out << ind << "Tuple t(*tuplesN.back());\n";
                            //--------------------------EREASING TRUE--------------------------
                            *out << ind << "nw"<<aggr->getJoinTupleName()<<".erase(*tuplesN.back());\n";
                            //--------------------------END EREASING TRUE--------------------------
                            *out << ind++ << "if(nu"<<aggr->getJoinTupleName()<<".find(Tuple(t)) == NULL){\n";
                                *out << ind << "const auto& insertResult = nu" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
                                *out << ind++ << "if (insertResult.second) {\n";
                                    *out << ind++ << "for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                for(const auto& aggrIdentifier: pair.second){
                                    const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
                                    int ruleId = aggrIdentifier.first;
                                    int aggrIndex = aggrIdentifier.second;
                                    std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);
                                    *out << ind++ << "{\n";
                                        boundVars.clear();
                                        for(int i=0;i<starter.getAriety();i++){
                                            if(starter.isVariableTermAt(i))
                                                boundVars.insert(starter.getTermAt(i)); 
                                        }
                                        for(unsigned v : sharedVariablesIndexesMap[key]){
                                            if(boundVars.count(aggregate->getAggregate().getTermAt(v))<=0){
                                                boundVars.insert(aggregate->getAggregate().getTermAt(v));
                                                *out << ind << "int "<<aggregate->getAggregate().getTermAt(v)<<" = t["<<v<<"];\n";
                                            }
                                        }

                                        //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------

                                        *out << ind << "std::vector<int> aggrKey({";
                                        bool first=true;
                                        std::string aggrVarProj;
                                        std::string aggrVarTuple;
                                        for(unsigned v: aggregateVariablesIndex[key]){
                                            if(!first){
                                                *out << ",";
                                                aggrVarTuple+=",";
                                            }
                                            *out << "t["<<v<<"]";
                                            aggrVarTuple+="t["+std::to_string(v)+"]";
                                            aggrVarProj+=std::to_string(v)+"_";
                                            first=false;
                                        }
                                        *out << "});\n";
                                        std::string sharedVarProj;
                                        for(unsigned v: sharedVariablesIndexesMap[key]){
                                            sharedVarProj+=std::to_string(v)+"_";
                                        }
                                        if(sharedVariablesMap[key]!=""){
                                            *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                        }else{
                                            *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                        }
                                        
                                            *out << ind << "auto& undefSet = undefNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            *out << ind << "auto& trueSet = trueNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            
                                            if(aggregate->getAggregate().isSum()){
                                                *out << ind++ << "if(undefSet.find(aggrKey)==undefSet.end()){\n";
                                                    *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                        *out << ind << "undefSet.insert(aggrKey);\n";
                                                        if(aggregate->getAggregate().isSum()){
                                                            //sub negative key to possible sum
                                                            *out << ind << "possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                                        }
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            }else{
                                                *out << ind++ << "if(trueSet.find(aggrKey) != trueSet.end()){\n";
                                                    *out << ind << "trueSet.erase(aggrKey);\n";
                                                *out << --ind << "}\n";
                                                *out << ind++ << "if(undefSet.find(aggrKey) == undefSet.end()){\n";
                                                    *out << ind++ << "if(trueSet.find(aggrKey) == trueSet.end()){\n";
                                                        *out << ind << "undefSet.insert(aggrKey);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            }

                                            
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                }
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                    
                        boundVars.clear();
                        for(int i=0;i<starter.getAriety();i++){
                            if(starter.isVariableTermAt(i)&&boundVars.count(starter.getTermAt(i))==0){
                                boundVars.insert(starter.getTermAt(i));
                            }
                        }
                        int closingPars=0;
                        int buildIndex=0;
                        std::string jointuple;
                        std::vector<std::vector<std::string>> previousLit;
                        previousLit.push_back({starter.getPredicateName(),std::to_string(starter.isNegated()),std::to_string(startingLiteral)});
                        for(const aspc::Literal& li : aggr->getAggregate().getAggregateLiterals()){
                            for(int i=0;i<li.getAriety();i++){
                                std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
                                jointuple+=mapStringConstant+",";
                            }
                            if(buildIndex!=startingLiteral){
                                if(li.isBoundedLiteral(boundVars)){
                                    std::string literalTerms;
                                    for(int i=0;i<li.getAriety();i++){
                                        if(i>0)
                                            literalTerms+=",";
                                        std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
                                        literalTerms+=mapStringConstant;
                                    }
                                    
                                    if(li.isPositiveLiteral()){
                                        *out << ind << "const Tuple* tuple"<<buildIndex<<" = w"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
                                        *out << ind << "bool undef"<<buildIndex<<" = false;\n";
                                        *out << ind++ << "if(tuple"<<buildIndex<<"==NULL){\n";
                                            *out << ind << "tuple"<<buildIndex<<" = u"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
                                            *out << ind << "undef"<<buildIndex<<" = true;\n";
                                        *out << --ind << "}\n";
                                    }else{
                                        *out << ind << "const Tuple negativeTuple"<<buildIndex<<"({"<<literalTerms<<"},&_"<<li.getPredicateName()<<",true);\n";
                                        *out << ind << "const Tuple* tuple"<<buildIndex<<" = u"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
                                        *out << ind << "bool undef"<<buildIndex<<" = false;\n";
                                        *out << ind++ << "if(tuple"<<buildIndex<<"!=NULL){\n";
                                            *out << ind << "undef"<<buildIndex<<" = true;\n";
                                        *out << --ind << "}else if(w"<<li.getPredicateName()<<".find(negativeTuple"<<buildIndex<<")==NULL){\n";
                                            *out << ++ind << "tuple"<<buildIndex<<"=&negativeTuple"<<buildIndex<<";\n";
                                        *out << --ind << "}\n";
                                    }
                                    *out << ind++ << "if(tuple"<<buildIndex<<"!=NULL){\n";
                                        for(auto & pair:previousLit){
                                            if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
                                                std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
                                                *out << ind++ << "if(";
                                                for(int i=0;i<li.getAriety();i++){
                                                    if (i>0){
                                                        *out << " || ";
                                                    }
                                                    *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
                                                }
                                                *out << "){\n";
                                                
                                                closingPars++;
                                            }
                                        }
                                    closingPars++;
                                    previousLit.push_back({li.getPredicateName(),std::to_string(li.isNegated()),std::to_string(buildIndex)});
                                }else{
                                    std::string literalTerms;
                                    std::string boundTermsIndex;
                                    bool first=true;
                                    for(int i=0;i<li.getAriety();i++){
                                        if(!li.isVariableTermAt(i) || boundVars.count(li.getTermAt(i))>0){
                                            if(!first)
                                                literalTerms+=",";
                                            std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
                                            literalTerms+=mapStringConstant;
                                            first=false;
                                            boundTermsIndex+= std::to_string(i)+"_";
                                        }
                                    }
                                    
                                    *out << ind << "const std::vector<const Tuple*>& tuples"<<buildIndex<<" = p"<<li.getPredicateName()<<"_"<<boundTermsIndex<<".getValues({"<<literalTerms<<"});\n";
                                    *out << ind << "const std::vector<const Tuple*>& tuplesU"<<buildIndex<<" = u"<<li.getPredicateName()<<"_"<<boundTermsIndex<<".getValues({"<<literalTerms<<"});\n";
                                    *out << ind++ << "for(int i_"<<buildIndex<<"=0;i_"<<buildIndex<<"<tuples"<<buildIndex<<".size()+tuplesU"<<buildIndex<<".size();i_"<<buildIndex<<"++){\n";
                                    closingPars++;
                                        *out << ind << "const Tuple* tuple"<<buildIndex<<";\n";
                                        *out << ind << "bool undef"<<buildIndex<<"=false;\n";
                                        *out << ind++ << "if(i_"<<buildIndex<<"<tuples"<<buildIndex<<".size())";
                                            *out << ind-- << "tuple"<<buildIndex<<"=tuples"<<buildIndex<<"[i_"<<buildIndex<<"];\n";
                                        *out << ind++ << "else{\n";
                                            *out << ind << "tuple"<<buildIndex<<"=tuplesU"<<buildIndex<<"[i_"<<buildIndex<<"-tuples"<<buildIndex<<".size()];\n";
                                            *out << ind << "undef"<<buildIndex<<"=true;\n";
                                        *out << --ind << "}\n";
                                    if(checkTupleFormat(li,std::to_string(buildIndex),true))
                                        closingPars++;
                                        for(auto & pair:previousLit){
                                            if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
                                                std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
                                                *out << ind++ << "if(";
                                                for(int i=0;i<li.getAriety();i++){
                                                    if (i>0){
                                                        *out << " || ";
                                                    }
                                                    *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
                                                }
                                                *out << "){\n";
                                                
                                                closingPars++;
                                            }
                                        }
                                    for(int i=0;i<li.getAriety();i++){
                                        if(li.isVariableTermAt(i)&&boundVars.count(li.getTermAt(i))==0){
                                            *out << ind << "int "<<li.getTermAt(i)<<" = tuple"<<buildIndex<<"->at("<<i<<");\n";
                                            boundVars.insert(li.getTermAt(i));
                                        }
                                    }    

                                    previousLit.push_back({li.getPredicateName(),std::to_string(li.isNegated()),std::to_string(buildIndex)});

                                }
                            }
                            buildIndex++;
                        }
                        for(const aspc::ArithmeticRelation& inequality : aggr->getAggregate().getAggregateInequalities()){
                            if(inequality.isBoundedRelation(boundVars)){
                                *out << ind++ << "if("<<inequality.getStringRep()<<"){\n";
                                closingPars++;
                            }else if(inequality.isBoundedValueAssignment(boundVars)){
                                *out << ind << "int "<<inequality.getAssignmentStringRep(boundVars)<<";\n";
                                jointuple+=inequality.getAssignedVariable(boundVars)+",";
                                boundVars.insert(inequality.getAssignedVariable(boundVars));
                            }
                        }       
                            //--------------------------SAVING NEW UNDEF--------------------------
                            *out << ind << "Tuple t({"<<jointuple.substr(0,jointuple.length()-1)<<"},&_"<<aggr->getJoinTupleName()<<");\n";
                                

                            //--------------------------END SAVING NEW UNDEF--------------------------

                            for(const auto& aggrIdentifier: pair.second){
                                const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
                                int ruleId = aggrIdentifier.first;
                                int aggrIndex = aggrIdentifier.second;
                                std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);

                                *out << ind++ << "{\n";
                                    //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                    
                                    *out << ind << "std::vector<int> aggrKey({";
                                    bool first=true;
                                    std::string aggrVarProj;
                                    std::string aggrVarTuple;
                                    for(unsigned v: aggregateVariablesIndex[key]){
                                        if(!first){
                                            *out << ",";
                                            aggrVarTuple+=",";
                                        }
                                        *out << "t["<<v<<"]";
                                        aggrVarTuple+="t["+std::to_string(v)+"]";
                                        aggrVarProj+=std::to_string(v)+"_";
                                        first=false;

                                    }
                                    *out << "});\n";
                                    *out << ind++ << "if(aggrKey[0]>=0){\n";
                                        {
                                            *out << ind++ << "if(u"<<aggr->getJoinTupleName()<<".find(Tuple(t))==NULL){\n";
                                                *out << ind++ << "if(w" << aggr->getJoinTupleName() <<".find(t))\n";
                                                *out << ind-- << "w" << aggr->getJoinTupleName() <<".erase(t);\n";

                                                *out << ind << "const auto& insertResult = u" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
                                                *out << ind++ << "if (insertResult.second) {\n";
                                                    *out << ind++ << "for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
                                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            std::string sharedVarProj;
                                            for(unsigned v: sharedVariablesIndexesMap[key]){
                                                sharedVarProj+=std::to_string(v)+"_";
                                            }
                                            *out << ind << "auto& trueSet = trueAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            *out << ind << "auto& undefSet = undefAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                        
                                            if(sharedVariablesMap[key]!=""){
                                                // *out << ind++ << "if(sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariablesMap[key]<<"})>0 && sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<"[{"<<sharedVariablesMap[key]<<"}]->first->getValues(aggrKey).size()<=0){\n";
                                                *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                            }else{
                                                *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                            }
                                                *out << ind++ << "if(trueSet.find(aggrKey)!=trueSet.end()){\n";
                                                    *out << ind << "trueSet.erase(aggrKey);\n";
                                                    if(aggregate->getAggregate().isSum()){
                                                        *out << ind << "actualSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                                    }
                                                *out << --ind << "}\n";
                                                *out << ind++ << "if(undefSet.find(aggrKey)==undefSet.end()){\n";
                                                    *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                        *out << ind << "undefSet.insert(aggrKey);\n";
                                                        if(aggregate->getAggregate().isSum()){
                                                            *out << ind << "possibleSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]+=aggrKey[0];\n";
                                                        }
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                        }
                                    *out << --ind << "}else{\n";
                                        ind++;
                                        {
                                            *out << ind++ << "if(nu"<<aggr->getJoinTupleName()<<".find(Tuple(t))==NULL){\n";
                                                *out << ind++ << "if(nw" << aggr->getJoinTupleName() <<".find(t))\n";
                                                *out << ind-- << "nw" << aggr->getJoinTupleName() <<".erase(t);\n";

                                                *out << ind << "const auto& insertResult = nu" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
                                                *out << ind++ << "if (insertResult.second) {\n";
                                                    *out << ind++ << "for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
                                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            std::string sharedVarProj;
                                            for(unsigned v: sharedVariablesIndexesMap[key]){
                                                sharedVarProj+=std::to_string(v)+"_";
                                            }
                                            *out << ind << "auto& trueSet = trueNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                            *out << ind << "auto& undefSet = undefNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                        
                                            if(sharedVariablesMap[key]!=""){
                                                // *out << ind++ << "if(sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariablesMap[key]<<"})>0 && sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<"[{"<<sharedVariablesMap[key]<<"}]->first->getValues(aggrKey).size()<=0){\n";
                                                *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
                                            }else{
                                                *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({aggrKey}).size()<=0){\n";
                                            }
                                                *out << ind++ << "if(trueSet.find(aggrKey)!=trueSet.end()){\n";
                                                    *out << ind << "trueSet.erase(aggrKey);\n";
                                                    if(aggregate->getAggregate().isSum()){
                                                        *out << ind << "actualNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]+=aggrKey[0];\n";
                                                    }
                                                *out << --ind << "}\n";
                                                *out << ind++ << "if(undefSet.find(aggrKey)==undefSet.end()){\n";
                                                    *out << ind++ << "if(trueSet.find(aggrKey)==trueSet.end()){\n";
                                                        *out << ind << "undefSet.insert(aggrKey);\n";
                                                        if(aggregate->getAggregate().isSum()){
                                                            *out << ind << "possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]-=aggrKey[0];\n";
                                                            *out << ind << "int possSum = possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}];\n";
                                                            
                                                            *out << ind++ << "if(maxPossibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]<possSum)\n";
                                                                *out << ind-- << "maxPossibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[key]<<"}]=possSum;\n";
                                                        }
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";

                                            //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
                                        }                                  
                                    *out << --ind << "}\n";  
                                *out << --ind << "}\n";
                            }
                        while(closingPars>0){
                            closingPars--;
                            *out << --ind << "}\n";
                        }
                    
                    if(checkFormat)
                            *out << --ind << "}\n";
                *out << --ind << "}\n";
                startingLiteral++;
            }
        }
        for(const aspc::Rule& r : program.getRules()){
            //aggiungo alla mappa delle shared variables le tuple di shared variables indefinite
            for(int i=0;i<r.getBodyLiterals().size();i++){
                bool hasSharedVar = false;
                for(const aspc::ArithmeticRelationWithAggregate& aggr:r.getArithmeticRelationsWithAggregate()){
                    if(sharedVariablesMap[std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex())]!="")
                        hasSharedVar=true;

                }
                if(hasSharedVar){
                    *out << ind++ << "if(tuple.getPredicateName() == &_" << r.getBodyLiterals()[i].getPredicateName()<<"){\n";
                    updateUndefinedSharedVariablesMap(r,i);
                    *out << --ind <<"}\n";
                }
            }
        }
        // *out << ind << "for(auto& t :ua_U_U_U_a_X_X_X_a_Y_Z_X_.getTuples()){t->print(); std::cout<<std::endl;\n}";
        // *out << ind << "std::cout<<std::endl;\n";
        // *out << ind << "positiveAggrReason[0][{}].print();\n";
        // *out << ind << "std::cout<<\"Current level \"<<positiveAggrReason[0][{}].getCurrentLevel()<<std::endl;\n";
        // *out << ind << "std::cout<<\"Negative aggr reason: \"<<negativeAggrReason[0][{}].size()<<std::endl;\n";
        // *out << ind << "for(auto& pair :negativeAggrReason[0]){ for(int v: pair.second) {unsigned uv = v > 0 ? v : -v; atomsTable[uv].print();}std::cout<<std::endl;}\n";
        // *out << ind << "std::cout<<\"Positive aggr reason: \"<<positiveAggrReason[0][{}].size()<<std::endl;\n";
        // *out << ind << "for(int v:positiveAggrReason[0][{}]){unsigned uv = v > 0 ? v : -v; atomsTable[uv].print();}std::cout<<std::endl;\n";
        // *out << ind << "for(const auto& p : actualSum[0]) std::cout<<\"true sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : possibleSum[0]) std::cout<<\"undef sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : actualNegativeSum[0]) std::cout<<\"true negative sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : possibleNegativeSum[0]) std::cout<<\"undef negative sum \"<<p.second<<std::endl;\n";
        // *out << ind << "for(const auto& p : trueAggrVars[0]) std::cout<<\"true count \"<<p.second.size()<<std::endl;\n";
        // *out << ind << "for(const auto& p : undefAggrVars[0]) std::cout<<\"undef count \"<<p.second.size()<<std::endl;\n";
        // *out << ind << "for(const auto& p : trueNegativeAggrVars[0]) std::cout<<\"true negative count \"<<p.second.size()<<std::endl;\n";
        // *out << ind << "for(const auto& p : undefNegativeAggrVars[0]) std::cout<<\"undef negative count \"<<p.second.size()<<std::endl;\n";

        
    }
    *out << --ind << "}\n";
    // ---------------------- end onLiteralTrue(int var) --------------------------------------//

    // ---------------------- addedVarName(int var, const std::string & atom) --------------------------------------//

    *out << ind++ << "inline void Executor::addedVarName(int var, const std::string & atom) {\n";
    // *out << ind << "std::cout<<var<<\" \" << atom<<std::endl;\n";
    *out << ind << "atomsTable.resize(var+1);\n";
    *out << ind << "atomsTable.insert(atomsTable.begin()+var, parseTuple(atom));\n";
    *out << ind << "tupleToVar[atomsTable[var]]= var;\n";
    *out << --ind << "}\n";
    // ---------------------- end addedVarName(int var, const std::string & atom) --------------------------------------//

    // ---------------------- clearPropagatedLiterals() --------------------------------------//
    *out << ind++ << "void Executor::clearPropagations() {\n";
    *out << ind << "propagatedLiteralsAndReasons.clear();\n";
    *out << ind << "propagatedLiterals.clear();\n";
    // *out << ind << "std::cout<<\"clearPropagation\"<<std::endl;\n";
    //*out << ind << "reasonsForPropagatedLiterals.clear();\n";
    //*out << ind << "propagatedLiterals.clear();\n";
    *out << --ind << "}\n";

    // ---------------------- end clearPropagatedLiterals() --------------------------------------//

    // ---------------------- clear() --------------------------------------//
    *out << ind++ << "void Executor::clear() {\n";
    *out << ind << "failedConstraints.clear();\n";
    *out << ind << "predicateToAuxiliaryMaps.clear();\n";

    if (mode == LAZY_MODE) {
        *out << ind << "predicateToFalseAuxiliaryMaps.clear();\n";
    }

    for (const pair<std::string, unsigned>& predicate : predicates) {
        if (idbs.count(predicate.first) || headPredicates.count(predicate.first)) {
            *out << ind << "w" << predicate.first << ".clear();\n";
        }
    }


    for (const std::string & predicate : modelGeneratorPredicatesInNegativeReasons) {
        if (idbs.count(predicate) || headPredicates.count(predicate)) {
            *out << ind << "neg_w" << predicate << ".clear();\n";
        }
    }

    for (const auto & entry : predicateToAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            if (idbs.count(entry.first) || headPredicates.count(entry.first)) {
                *out << ind << "p" << auxSet << ".clear();\n";
            }
        }
    }

    for (const auto & entry : predicateToFalseAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            if (idbs.count(entry.first) || headPredicates.count(entry.first)) {
                *out << ind << auxSet << ".clear();\n";
            }
        }
    }

    *out << --ind << "}\n";

    // ---------------------- end clear() --------------------------------------//

    // ---------------------- init() --------------------------------------//
    *out << ind++ << "void Executor::init() {\n";
    if (program.hasConstraint()) {
        *out << ind << "createFunctionsMap();\n";
    }
    string reference = (mode == EAGER_MODE) ? "&" : "";

    for (const pair<std::string, unsigned>& predicate : predicates) {

        *out << ind << "predicateWSetMap[" << reference << "_" << predicate.first << "]=&w" << predicate.first << ";\n";
        if (mode == EAGER_MODE) {
            *out << ind << "predicateUSetMap[&_" << predicate.first << "]=&u" << predicate.first << ";\n";
        }
        *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = &_" << predicate.first << ";\n";
    }
    for(aspc::Rule& r :program.getRules()){
        if(r.isConstraint()){
            for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                if(aggr.getAggregate().isSum()){
                    // *out << ind << "possibleSum[" << aggregateToStructure[aggr.getJoinTupleName()] << "][{}]=0;\n";
                    // *out << ind << "actualSum[" << aggregateToStructure[aggr.getJoinTupleName()] << "][{}]=0;\n";
                }
                for(const aspc::Literal& l: aggr.getAggregate().getAggregateLiterals()){
                    // *out << ind << "aggregatePredicatesAndVars [" << reference << "_" << l.getPredicateName() << "]= std::vector<int>({";
                    // int countVars=0;
                    // for(int i=0;i<l.getAriety();i++){
                    //     if(aggr.getAggregate().containsVar(l.getTermAt(i))>=0){
                    //         *out << i;
                    //         countVars++;
                    //         if(countVars<aggr.getAggregate().getAggregateVariables().size()-1 && i<l.getAriety()-1)
                    //         *out <<",";
                    //     }

                    // }
                    // *out << "});\n";
                    *out << ind << "predicateWSetMap[" << reference << "_" << l.getPredicateName() << "]=&w" << l.getPredicateName() << ";\n";
                    *out << ind << "predicateFSetMap[" << reference << "_" << l.getPredicateName() << "]=&f" << l.getPredicateName() << ";\n";
                    if (mode == EAGER_MODE) {
                        *out << ind << "predicateUSetMap[&_" << l.getPredicateName() << "]=&u" << l.getPredicateName() << ";\n";
                    }
                    *out << ind << "stringToUniqueStringPointer[\"" << l.getPredicateName() << "\"] = &_" << l.getPredicateName() << ";\n";
                }
            }
        }
    }



    for (const std::string & predicate : modelGeneratorPredicatesInNegativeReasons) {
        *out << ind << "predicateFSetMap[_" << predicate << "] = &neg_w" << predicate << ";\n";
    }

    for (const auto & entry : predicateToAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            *out << ind << "predicateToAuxiliaryMaps[" << reference << "_" << entry.first << "].push_back(&p" << auxSet << ");\n";
        }
    }
    for (const auto & entry : predicateToNegativeAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            *out << ind << "predicateToNegativeAuxiliaryMaps[" << reference << "_" << entry.first << "].push_back(&np" << auxSet << ");\n";
        }
    }

    for (const auto & entry : predicateToUndefAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            *out << ind << "predicateToUndefAuxiliaryMaps[" << reference << "_" << entry.first << "].push_back(&u" << auxSet << ");\n";
        }
    }
    for (const auto & entry : predicateToNegativeUndefAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            *out << ind << "predicateToNegativeUndefAuxiliaryMaps[" << reference << "_" << entry.first << "].push_back(&nu" << auxSet << ");\n";
        }
    }

    for (const auto & entry : predicateToFalseAuxiliaryMaps) {
        for (const auto & auxSet : entry.second) {
            *out << ind << "predicateToFalseAuxiliaryMaps[" << reference << "_" << entry.first << "].push_back(&f" << auxSet << ");\n";
        }
    }

    *out << --ind << "}\n";
    // ---------------------- end init() --------------------------------------//


    // ---------------------- executeProgramOnFacts() --------------------------------------//
    if (mode == LAZY_MODE) {
        *out << ind << "void Executor::executeProgramOnFacts(const std::vector<int> & facts) {}\n";
        *out << ind++ << "void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {\n";
    } else {
        *out << ind << "void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}\n";
        *out << ind++ << "void Executor::executeProgramOnFacts(const std::vector<int> & facts) {\n";
    }
    //data structure init

    if (mode == LAZY_MODE) {
        *out << ind << "init();\n";
        *out << ind << "clear();\n";
    } else {
        // mode == EAGER_MODE

        //facts[0] is the decision level for eager mode (-1 is facts level)
        *out << ind << "int decisionLevel = facts[0];\n";
        //*out << ind << "std::cout<<\"Execute program on facts: decision level \"<<decisionLevel<<std::endl;\n";

#ifdef EAGER_DEBUG
        *out << ind << "std::cout<<\"Execute program on facts: decision level \"<<decisionLevel<<std::endl;\n";
#endif
        //*out << ind++ << "if(decisionLevel > 0) {\n";
        *out << ind << "clearPropagations();\n";
        //*out << --ind << "}\n";
    }


    // *out << ind << "std::cout<<\"facts reading\"<<std::endl;\n";

    //feed facts
    //*out << ind << "std::cout<<\"facts\\n\";\n";
    if (mode == LAZY_MODE) {
        *out << ind++ << "for(unsigned i=0;i<facts.size();i++) {\n";
        *out << ind << "onLiteralTrue(facts[i]);\n";
        *out << --ind << "}\n";
    } else {
        // mode == EAGER_MODE
        *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
        // *out << ind << "std::cout<<\"facts: \"<<facts[i]<<std::endl;\n";
        *out << ind << "onLiteralTrue(facts[i]);\n";

        *out << --ind << "}\n";
    }

    if (mode == LAZY_MODE) {
        //declare iterators
        for (const pair<std::string, unsigned>& predicate : predicates) {
            *out << ind << "unsigned index_" << predicate.first << "=0;\n";
        }

        for (unsigned i = 0; i < sccsSize; i++) {
            const std::unordered_map<std::string, std::vector<unsigned>>&startersExitRules = starterToExitRulesByComponent[i];
            for (const auto& rulesByPredicate : startersExitRules) {
                *out << ind << "index_" << rulesByPredicate.first << "=0;\n";
                *out << ind++ << "while(index_" << rulesByPredicate.first << "!=w" << rulesByPredicate.first << ".getTuples().size()){\n";
                *out << ind << "const Tuple * tuple0 = w" << rulesByPredicate.first << ".getTuples()[index_" << rulesByPredicate.first << "];\n";
                for (unsigned ruleId : rulesByPredicate.second) {
                    const aspc::Rule& r = program.getRule(ruleId);
                    *out << ind++ << "{\n";
                    compileRule(r, r.getStarters()[0], program);
                    *out << --ind << "}\n";

                }
                *out << ind << "index_" << rulesByPredicate.first << "++;\n";
                *out << --ind << "}\n";
            }

            const std::unordered_map<std::string, std::vector <pair<unsigned, unsigned>>>& recursiveRulesByStarter = starterToRecursiveRulesByComponent[i];
            if (recursiveRulesByStarter.size()) {
                *out << ind++ << "while(";
                unsigned index = 0;
                for (unsigned vertexId : sccs[sccs.size() - i - 1]) {
                    const Vertex& v = vertexByID.at(vertexId);
                    if (index > 0)
                        *out << " || ";
                    *out << "index_" << v.name << "!=w" << v.name << ".getTuples().size()";
                    index++;
                }
                *out << "){\n";
            }
            for (const auto& rulesByStarter : recursiveRulesByStarter) {
                *out << ind++ << "while(index_" << rulesByStarter.first << "!=w" << rulesByStarter.first << ".getTuples().size()){\n";
                *out << ind << "const Tuple * tuple0 = w" << rulesByStarter.first << ".getTuples()[index_" << rulesByStarter.first << "];\n";
                for (const auto& ruleAndStarterIndex : rulesByStarter.second) {
                    const aspc::Rule& r = program.getRule(ruleAndStarterIndex.first);
                    *out << ind++ << "{\n";
                    compileRule(r, ruleAndStarterIndex.second, program);
                    *out << --ind << "}\n";

                }
                *out << ind << "index_" << rulesByStarter.first << "++;\n";
                *out << --ind << "}\n";
            }
            if (recursiveRulesByStarter.size())
                *out << --ind << "}\n";

        }
        if (!programHasConstraint) {
            //*out << ind << "std::cout<<\"Propagator model:\"<<std::endl;\n";
            for (const pair<std::string, unsigned>& predicate : predicates) {
                *out << ind << "printTuples(\"" << predicate.first << "\",w" << predicate.first << ".getTuples());\n";

            }
        }
    } else {
        //mode == EAGER_MODE
        // *out << ind << "std::cout<<\"Decision level \"<<decisionLevel<<\" \"<<facts[1]<<std::endl;\n";
        *out << ind++ << "if(decisionLevel==-1) {\n";
        // *out << ind << "std::cout<<\"decisionLevelif\"<<std::endl;\n";
        for (const aspc::Rule& r : program.getRules()) {
            if (r.isConstraint() && !r.containsAggregate()) {
                *out << ind++ << "{\n";
                *out << ind << "const Tuple * tupleU = NULL;\n";
                *out << ind << "bool tupleUNegated = false;\n";

                compileRule(r, r.getBodySize(), program);


                *out << --ind << "}//close local scope\n";
            }else if (r.isConstraint()){
                *out << ind++ << "{\n";
                *out << ind << "const Tuple * tupleU = NULL;\n";
                *out << ind << "bool tupleUNegated = false;\n";
                compileConstraintWithAggregate(r, r.getBodySize(), program);

                *out << --ind << "}//close local scope\n";
            }
        }
        *out << --ind << "}//close decision level == -1\n";
        // *out << ind << "else std::cout<<\"outOfDecisionLevel\"<<std::endl;\n";
        //*out << ind << "std::cout<<\"start for on facts\"<<decisionLevel<<std::endl;\n";

        *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
        *out << ind << "unsigned factVar = facts[i] > 0 ? facts[i] : -facts[i];\n";
        *out << ind << "Tuple starter = atomsTable[factVar];\n";
        *out << ind << "starter.setNegated(facts[i]<0);\n";

        //*out << ind << "starter.print();std::cout<<\" Starter\"<<std::endl;\n";
        //*out << ind << "std::cout<<\"Starting from \";starter.print();std::cout<<std::endl;\n";
        /**out << ind << "std::cout<<\"False size: \"<<fp_1_.getValues({}).size()<<std::endl;\n";
        *out << ind << "std::cout<<\"True size: \"<<pp_1_.getValues({}).size()<<std::endl;\n";
        *out << ind << "std::cout<<\"Undef size: \"<<up_1_.getValues({}).size()<<std::endl;\n";*/
        for (unsigned i = 0; i < sccsSize; i++) {
            const std::unordered_map<std::string, std::vector<unsigned>>&startersExitRules = starterToExitRulesByComponent[i];
            for (const auto& rulesByPredicate : startersExitRules) {
                //*out << ind++ << "if(facts[i]->getPredicateName() == \"" << rulesByPredicate.first << "\") { \n";
                if(rulesByPredicate.first[0]=='#'){

                    /*int start = rulesByPredicate.first.find(':');
                    *out << ind++ << "if(starter.getPredicateName() == &_" << rulesByPredicate.first.substr(start+1) << ") { \n";
                    *out << ind << "const Tuple * tuple0 = &starter;\n";*/

                }else{
                    *out << ind++ << "if(starter.getPredicateName() == &_" << rulesByPredicate.first << ") { \n";
                    *out << ind << "const Tuple * tuple0 = &starter;\n";

                }
                //std::cout<< "Predicate "<<rulesByPredicate.first<<std::endl;
                for (unsigned ruleId : rulesByPredicate.second) {

                    const aspc::Rule& r = program.getRule(ruleId);
                    for (unsigned starter : r.getStarters()) {
                        if (starter != r.getBodySize()) {
                            //std::cout<<starter<<std::endl;
                            if(!r.containsAggregate()){
                                aspc::Literal* starterBodyLiteral = (aspc::Literal*)(r.getFormulas()[starter]);
                                string negationCheck = starterBodyLiteral->isNegated() ? "<" : ">";
                                if (rulesByPredicate.first == starterBodyLiteral->getPredicateName()) {
                                    *out << ind++ << "if(facts[i] " << negationCheck << " 0){\n";
                                    *out << ind++ << "{\n";
                                    *out << ind << "const Tuple * tupleU = NULL;\n";
                                    *out << ind << "bool tupleUNegated = false;\n";
                                    compileRule(r, starter, program);
                                    *out << --ind << "}//close loop nested join\n";
                                    *out << --ind << "}//close loop nested join\n";
                                }
                            }else{
                                if(r.getFormulas()[starter]->isLiteral()){
                                    aspc::Literal* starterBodyLiteral = (aspc::Literal*)(r.getFormulas()[starter]);
                                    string negationCheck = starterBodyLiteral->isNegated() ? "<" : ">";
                                    if (rulesByPredicate.first == starterBodyLiteral->getPredicateName()) {
                                        *out << ind++ << "if(facts[i] " << negationCheck << " 0){\n";
                                        *out << ind++ << "{\n";
                                        *out << ind << "const Tuple * tupleU = NULL;\n";
                                        *out << ind << "bool tupleUNegated = false;\n";
                                        compileConstraintWithAggregate(r, starter, program);
                                        *out << --ind << "}//close loop nested join\n";
                                        *out << --ind << "}//close loop nested join\n";
                                    }
                                }else if (r.getFormulas()[starter]->containsAggregate()){
                                    aspc::ArithmeticRelationWithAggregate* aggr = (aspc::ArithmeticRelationWithAggregate*)(r.getFormulas()[starter]);
                                    string negationCheck = aggr->isNegated() ? "<" : ">";

                                    //per constraint con multi aggregato controllare che il formulaIndex corrisponda
                                    if (rulesByPredicate.first == "#"+std::to_string(r.getRuleId())+":"+std::to_string(aggr->getFormulaIndex())) {

                                        //*out << ind++ << "if(facts[i] "<<negationCheck<<" 0){\n";
                                        *out << ind++ << "{\n";

                                        *out << ind << "bool tupleUNegated = false;\n";
                                        *out << ind << "const Tuple * tupleU = NULL;\n";

                                        compileConstraintWithAggregate(r, starter, program);
                                        *out << --ind << "}//local scope\n";
                                        //*out << --ind << "}//close if\n";
                                    }

                                }
                            }
                        }
                    }

                }
                if(rulesByPredicate.first[0]!='#')
                    *out << --ind << "}//close predicate joins\n";
            }
        }
        *out << --ind << "}\n";

    }
    // *out << ind << "std::cout<<\"Out execute program on facts\"<<std::endl;\n";

    *out << --ind << "}\n";
    *out << ind << "}\n";


    //*out << ind << "w" << predicateIdPair.first << ".printTuples(\"" << predicateIdPair.first << "\");\n";
}

void CompilationManager::declareDataStructures(const aspc::Rule& r, unsigned start,const std::set< std::pair<std::string, unsigned> >& aggregatePredicates) {

    std::unordered_set<std::string> boundVariables;
    if (start != r.getBodySize()) {
        r.getFormulas().at(start)->addVariablesToSet(boundVariables);

    }

    const std::vector<unsigned> & joinOrder = r.getOrderedBodyIndexesByStarter(start);
    unsigned i = 1;
    if (start == r.getBodySize()) {
        i = 0;
    }
    for (; i < r.getFormulas().size(); i++) {
        const aspc::Formula* f = r.getFormulas()[joinOrder[i]];
        if (f->isLiteral()) {
            const aspc::Literal * li = (aspc::Literal *) f;
            if (li->isPositiveLiteral() && !li->isBoundedLiteral(boundVariables)) {

                std::vector< unsigned > keyIndexes;
                std::string mapVariableName = li->getPredicateName() + "_";
                for (unsigned tiIndex = 0; tiIndex < li->getTerms().size(); tiIndex++) {
                    if ((li->isVariableTermAt(tiIndex) && boundVariables.count(li->getTermAt(tiIndex))) || !li->isVariableTermAt(tiIndex)) {
                        mapVariableName += std::to_string(tiIndex) + "_";
                        keyIndexes.push_back(tiIndex);
                    }
                }

                if (!declaredMaps.count(mapVariableName)) {
                    *out << ind << "AuxMap p" << mapVariableName << "({";
                    for (unsigned k = 0; k < keyIndexes.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << keyIndexes[k];
                    }
                    *out << "});\n";

                    //TODO remove duplication
                    *out << ind << "AuxMap u" << mapVariableName << "({";
                    for (unsigned k = 0; k < keyIndexes.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << keyIndexes[k];
                    }
                    *out << "});\n";
                    if(aggregatePredicates.count(std::pair<std::string,unsigned>(li->getPredicateName(),li->getAriety()))!=0){

                        *out << ind << "AuxMap f" << mapVariableName << "({";
                        for (unsigned k = 0; k < keyIndexes.size(); k++) {
                            if (k > 0) {
                                *out << ",";
                            }
                            *out << keyIndexes[k];
                        }
                        *out << "});\n";
                        predicateToFalseAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);

                    }

                    predicateToAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);
                    if (mode == EAGER_MODE) {
                        predicateToUndefAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);
                    }
                    declaredMaps.insert(mapVariableName);
                }
            }
        }
        f->addVariablesToSet(boundVariables);
    }
}

bool literalPredicateAppearsBeforeSameSign(const std::vector<const aspc::Formula*>& body, vector<unsigned> joinOrder, unsigned i) {
    const aspc::Literal* l = (aspc::Literal*) body[joinOrder[i]];
    assert(l->isLiteral());

    for (unsigned p = 0; p < i; p++) {
        const aspc::Formula * f2 = body[joinOrder[p]];
        if (f2->isLiteral()) {
            const aspc::Literal* l2 = (aspc::Literal*) f2;
            if (l2->getPredicateName() == l->getPredicateName() && l->isNegated() == l2->isNegated()) {
                return true;
            }
            //find variables inequality?
        }
    }
    return false;
}

void CompilationManager::buildReason(std::string aggrIdentifier,const aspc::ArithmeticRelationWithAggregate* aggregateRelation,bool declareReason){


    int k=0;
    std::string tuple="";
    for(unsigned index : aggregateVariablesIndex[aggrIdentifier]){
        tuple+="trueTuples->at(reasonIndex)->at("+std::to_string(index)+")";
        if(k<aggregateVariablesIndex[aggrIdentifier].size()-1)
           tuple+=",";
        k++;
    }

    //choose join tuples map
    if(sharedVariablesMap[aggrIdentifier] != ""){
        if(!aggregateRelation->isNegated()){
            *out << ind << "const std::vector<const Tuple*>* trueTuples = &p_"<<aggregateRelation->getJoinTupleName();
            for(unsigned index : sharedVariablesIndexesMap[aggrIdentifier])
                *out << index << "_";
            *out <<".getValues({"<<sharedVariablesMap[aggrIdentifier]<<"});\n";
        }
    }else{

        if(!aggregateRelation->isNegated()){
            *out << ind << "const std::vector<const Tuple*>* trueTuples = &p_"<<aggregateRelation->getJoinTupleName();
            *out <<".getValues({});\n";
        }
    }
    //*out << ind << "std::cout<<\"Truetuples size: \"<<trueTuples->size()<<std::endl;\n";
    if(declareReason)
        *out << ind << "std::vector<int> reason;\n";

    if(!aggregateRelation->isNegated()){
        //iterate true values for positive literal
        *out << ind++ << "for(int reasonIndex=0;reasonIndex<trueTuples->size();reasonIndex++){\n";
            int varIndex=0;
            int literalIndex=0;
            for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
                *out << ind++ << "{\n";
                    *out << ind << "Tuple tuple(std::vector<int>({";
                    for(unsigned i=0;i<l.getAriety();i++){
                        *out << "trueTuples->at(reasonIndex)->at("<<varIndex<<")";
                        if(i<l.getAriety()-1)
                            *out << ",";
                        varIndex++;

                    }
                    *out << "}),&_"<<l.getPredicateName()<<");\n";
                    if(l.isNegated())
                        *out << ind << "int sign = -1;\n";
                    else
                        *out << ind << "int sign = 1;\n";
                    // *out << ind << "tuple"<<l.getPredicateName()<<"_"<<literalIndex<<".print();\n";
                    *out << ind << "const auto & it = tupleToVar.find(tuple);\n";
                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                        //print tuple in reason to debug
                        // *out << ind << "tuple.print();\n";
                        // *out << ind << "std::cout<<it->second<<std::endl;\n";
                        *out << ind << "local_reason.push_back(it->second * sign);\n";
                    *out << --ind <<"}//closing if\n";
                    literalIndex++;
                *out << --ind <<"}//closing local scope\n";
            }

        *out << --ind << "}\n";
    }else{
        //generate false joinTuple
        std::unordered_set<std::string> global_boundVars;
        for(unsigned v : sharedVariablesIndexesMap[aggrIdentifier]){
            global_boundVars.insert(aggregateRelation->getAggregate().getTermAt(v));
        }
        for(int starter=0;starter<aggregateRelation->getAggregate().getAggregateLiterals().size();starter++){
            int parenthesis=0;
            const aspc::Literal* li = &(aggregateRelation->getAggregate().getAggregateLiterals()[starter]);
            std::string constant_and_shared_var_proj="";
            std::string constant = "";
            std::unordered_set<std::string> boundVars(global_boundVars);
            
            for(int i=0;i<li->getAriety();i++){
                if(!li->isVariableTermAt(i) || sharedVariablesMap[aggrIdentifier].find(li->getTermAt(i))!=std::string::npos){
                    constant_and_shared_var_proj+=std::to_string(i)+"_";
                    constant+=li->getTermAt(i)+",";
                }
            }
            if(constant != ""){
                constant = constant.substr(0,constant.length()-1);
            }
            if(!li->isNegated())
                *out << ind << "const std::vector<const Tuple*>* falseTuples"<<starter<<" = &f"<<li->getPredicateName()<<"_"<<constant_and_shared_var_proj<<".getValues({";
            else
                *out << ind << "const std::vector<const Tuple*>* falseTuples"<<starter<<" = &p"<<li->getPredicateName()<<"_"<<constant_and_shared_var_proj<<".getValues({";
            
            *out << constant <<"});\n";

            *out << ind++ << "for(int i=0;i<falseTuples"<<starter<<"->size();i++){\n";
            std::string joiningTupleFound = aggregateRelation->getAggregate().getAggregateLiterals().size()<=1 ? "true":"false";
            *out << ind << "bool joiningTupleFound="<<joiningTupleFound<<";\n";
            for(int i=0;i<li->getAriety();i++){
                if(li->isVariableTermAt(i) && !boundVars.count(li->getTermAt(i))){
                    *out << ind << "int "<<li->getTermAt(i)<<" = falseTuples"<<starter<<"->at(i)->at("<<i<<");\n";
                    boundVars.insert(li->getTermAt(i));
                }
            }
            *out << ind << "const Tuple* tuple"<<starter<<"=falseTuples"<<starter<<"->at(i);\n";
            if(checkTupleFormat(*li,std::to_string(starter),true))
                parenthesis++;
            for(int joiningLiteral=0;joiningLiteral < aggregateRelation->getAggregate().getAggregateLiterals().size();joiningLiteral++){

                if(joiningLiteral!=starter){

                    if(!aggregateRelation->getAggregate().getAggregateLiterals()[joiningLiteral].isNegated()){

                        const aspc::Literal* liBuild = &(aggregateRelation->getAggregate().getAggregateLiterals()[joiningLiteral]);
                        std::string mapVariableName=liBuild->getPredicateName()+"_";
                        for(int i=0;i<liBuild->getAriety();i++){
                            if(boundVars.count(liBuild->getTermAt(i))||!liBuild->isVariableTermAt(i)){
                                mapVariableName+=std::to_string(i)+"_";
                            }
                        }
                        // if(!liBuild->isNegated())
                            *out << ind << "const std::vector<const Tuple*>* trueTuples"<<joiningLiteral<<" = &p"<<mapVariableName<<".getValues({";
                        // else
                        //     *out << ind << "const std::vector<const Tuple*>* trueTuples"<<joiningLiteral<<" = &f"<<mapVariableName<<".getValues({";

                        printLiteralTuple(liBuild,boundVars);
                        *out << "});\n";
                        *out << ind << "const std::vector<const Tuple*>* undefTuples"<<joiningLiteral<<" = &u"<<mapVariableName<<".getValues({";
                        printLiteralTuple(liBuild,boundVars);
                        *out << "});\n";
                        // if(!liBuild->isNegated())
                            *out << ind << "const std::vector<const Tuple*>* falseTuples"<<joiningLiteral<<" = &f"<<mapVariableName<<".getValues({";
                        // else
                        //     *out << ind << "const std::vector<const Tuple*>* falseTuples"<<joiningLiteral<<" = &p"<<mapVariableName<<".getValues({";

                        printLiteralTuple(liBuild,boundVars);
                        *out << "});\n";


                        *out << ind++ << "for(int i_"<<joiningLiteral<<"=0;!joiningTupleFound && i_"<<joiningLiteral<<" < trueTuples"<<joiningLiteral<<"->size()+undefTuples"<<joiningLiteral<<"->size()+falseTuples"<<joiningLiteral<<"->size();i_"<<joiningLiteral<<"++){\n";
                        parenthesis++;

                            *out << ind << "const Tuple * tuple"<<joiningLiteral<<"=NULL;\n";
                            *out << ind++ << "if(i_"<<joiningLiteral<<"<trueTuples"<<joiningLiteral<<"->size())\n";
                                *out << ind << "tuple"<<joiningLiteral<<"=trueTuples"<<joiningLiteral<<"->at(i_"<<joiningLiteral<<");\n";
                            *out << --ind << "else if(i_"<<joiningLiteral<<"<trueTuples"<<joiningLiteral<<"->size()+undefTuples"<<joiningLiteral<<"->size())\n";
                                *out << ++ind << "tuple"<<joiningLiteral<<"=undefTuples"<<joiningLiteral<<"->at(i_"<<joiningLiteral<<"-trueTuples"<<joiningLiteral<<"->size());\n";
                            *out << --ind << "else\n";
                                *out << ++ind << "tuple"<<joiningLiteral<<"=falseTuples"<<joiningLiteral<<"->at(i_"<<joiningLiteral<<"-trueTuples"<<joiningLiteral<<"->size()-undefTuples"<<joiningLiteral<<"->size());\n";
                            --ind;
                            if(checkTupleFormat(*liBuild,std::to_string(joiningLiteral),true))
                                parenthesis++;

                            for(int i=0;i<liBuild->getAriety();i++){
                                if(liBuild->isVariableTermAt(i) && !boundVars.count(liBuild->getTermAt(i))){
                                    *out << ind << "int "<<liBuild->getTermAt(i)<<" = tuple"<<joiningLiteral<<"->at("<<i<<");\n";
                                    boundVars.insert(liBuild->getTermAt(i));
                                }
                            }

                    }
                }
                int lastLiteral = aggregateRelation->getAggregate().getAggregateLiterals().size()-1;
                if(joiningLiteral>=lastLiteral){
                    for(const aspc::ArithmeticRelation& ar : aggregateRelation->getAggregate().getAggregateInequalities()){
                        if(ar.isBoundedRelation(boundVars))
                            *out << ind++ << "if(" << ar.getStringRep() << ")\n";
                        else if(ar.getComparisonType() == aspc::EQ){
                            std::string not_bound_var = "";
                            std::string remaining="";
                            if(ar.getLeft().isSingleTerm() && boundVars.count(ar.getLeft().getStringRep())<=0){
                                not_bound_var=ar.getLeft().getStringRep();
                                remaining=ar.getRight().getStringRep();
                            }
                            else if(ar.getRight().isSingleTerm() && boundVars.count(ar.getRight().getStringRep())<=0){
                                not_bound_var=ar.getRight().getStringRep();
                                remaining=ar.getLeft().getStringRep();

                            }
                            if(not_bound_var!="")
                                boundVars.insert(not_bound_var);

                            if(ar.isBoundedRelation(boundVars)){
                                *out << ind++ << "int " << not_bound_var << " = " <<remaining<<";\n";
                            }
                        }

                    }
                    *out << ind << "joiningTupleFound=true;\n";
                    for(const aspc::ArithmeticRelation& ar : aggregateRelation->getAggregate().getAggregateInequalities())
                        ind--;
                }
            }
            while(parenthesis>0){
                parenthesis--;
                *out << --ind << "}\n";
            }
            *out << ind++ << "if(joiningTupleFound){\n";
            // *out << ind << "std::cout << \"Building reason\"<<std::endl;\n";
            // *out << ind << "falseTuples"<<starter<<"->at(i)->print();\n";
                *out << ind << "const auto & it = tupleToVar.find(*falseTuples"<<starter<<"->at(i));\n";
                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                    if(li->isNegated()){
                        *out << ind << "const bool negatedLiteralForReason=true;\n";
                    }else{
                        *out << ind << "const bool negatedLiteralForReason=false;\n";
                    }
                    *out << ind << "local_reason.push_back(it->second * (negatedLiteralForReason ? 1:-1));\n";
                *out << --ind <<"}//closing if\n";
            *out << --ind << "}\n";
            *out << --ind << "}\n";
        }
    }

}
void CompilationManager::propIfMultipleJoin(const aspc::ArithmeticRelationWithAggregate* aggregateRelation,std::string& aggregateIdentifier,bool withReason,const std::vector<const aspc::Formula *>& body,const std::vector<unsigned int>& joinOrder,const aspc::Rule& r){
    //TODO: Fix plus one in if can prop
    //TODO: convert undefKey from set to map when there are shared variables
    // std::cout<<"propIfMultipleJoin"<<std::endl;
    // *out << ind << "std::cout<<\"start prof if multiple join\"<<std::endl;\n";
    std::string reason = withReason ? "localReason":"";
    std::string ruleId = aggregateIdentifier.substr(0,aggregateIdentifier.find(":"));
    std::string aggrIndex = aggregateIdentifier.substr(aggregateIdentifier.find(":")+1,aggregateIdentifier.length());
    std::string op = sharedVariablesMap[aggregateIdentifier] != "" ?"->":".";
    int literalIndex=0;
    std::string aggrVarProj;
    // std::string aggrVarMap = aggregateRelation->getJoinTupleName();
    std::string aggrVarMap;
    for(unsigned index : aggregateVariablesIndex[aggregateIdentifier]){
        aggrVarProj+="joinTupleU->at("+std::to_string(index)+"),";
        aggrVarMap+=std::to_string(index)+"_";
    }
    aggrVarProj=aggrVarProj.substr(0,aggrVarProj.length()-1);
    std::string sharedVarProj;
    if(sharedVariablesMap[aggregateIdentifier]!=""){
        for(unsigned index :sharedVariablesIndexesMap[aggregateIdentifier])
            sharedVarProj+="joinTupleU->at("+std::to_string(index)+"),";
        sharedVarProj=sharedVarProj.substr(0,sharedVarProj.length()-1);
    }
    int actualAriety=0;
    for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
        *out << ind++ << "for(const Tuple* tupleU : u"<<l.getPredicateName()<<"_.getValues({})){\n";
            if(l.getPredicateName()=="b")
            // *out << ind << "tupleU->print();std::cout<<\" Checking\"<<std::endl;\n";
            *out << ind << "std::unordered_set<std::vector<int>> undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<";\n";
            if(aggregateRelation->getAggregate().isSum())
                *out << ind << "int sumKey_"<<l.getPredicateName()<<"_"<<literalIndex<<"=0;\n";
            
            if(withReason)
                *out << ind << "std::vector<int> localReason;\n";

            std::string sharedVarsIndeces;
            for(unsigned i : sharedVariablesIndexesMap[aggregateIdentifier])
                sharedVarsIndeces+=std::to_string(i)+"_";

            *out << ind << "std::vector<int> key({";
            std::string tupleUProj;
            for(int i=0;i<l.getAriety();i++){
                if(i>0){
                    *out << ",";
                }
                if(i>0){
                    tupleUProj+=",";
                }
                *out << "tupleU->at("<<i<<")";
                tupleUProj += "tupleU->at("+std::to_string(i)+")";
            }
            std::string hasSharedVar = sharedVariablesMap[aggregateIdentifier]!=""?",":"";
            *out <<hasSharedVar<<sharedVariablesMap[aggregateIdentifier]<<"});\n";

            *out << ind++ << "for(const Tuple* joinTupleU : u_"<<aggregateRelation->getJoinTupleName()<<aggregateRelation->getAggrLitProj(literalIndex)<<sharedVarsIndeces<<".getValues(key)){\n";
                //joinTupleU matches literal undef and currentSharedVariable
                // if(l.getPredicateName()=="b")
                //     *out << ind << "joinTupleU->print();\n";
                *out << ind++ << "if(trueAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[aggregateIdentifier]<<"}].find({"<<aggrVarProj<<"})==trueAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[aggregateIdentifier]<<"}].end()){\n";
                if(aggregateRelation->isNegated()){
                    std::string comma= sharedVariablesMap[aggregateIdentifier]!="" ? ",":"";
                    *out << ind << "//"<<aggregateRelation->getJoinTupleName()<<"\n";
                    *out <<ind++ << "if(u_"<<aggregateRelation->getJoinTupleName()<<sharedVarsIndeces<<aggrVarMap<<".getValues({"<<sharedVarProj<<comma<<aggrVarProj<<"}).size() ==";
                        *out << "u_"<<aggregateRelation->getJoinTupleName()<<aggregateRelation->getAggrLitProj(literalIndex)<<sharedVarsIndeces<<aggrVarMap<<".getValues({"<<tupleUProj<<","<<sharedVarProj<<comma<<aggrVarProj<<"}).size() ){\n";

                        if(aggregateRelation->getAggregate().isSum()){
                            *out << ind++ << "if(undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".find({"<<aggrVarProj<<"})==undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".end())\n";
                                *out << ind-- << "sumKey_"<<l.getPredicateName()<<"_"<<literalIndex<<"+=joinTupleU->at("<<aggregateVariablesIndex[aggregateIdentifier][0]<<");\n";
                        }
                        *out << ind << "undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".insert({"<<aggrVarProj<<"});\n";

            
                    *out << --ind << "}\n";
                }else{
                    int buildLitIndex=0;
                    int buildAriety=0;
                    std::string onlyOneTrue;
                    for(const aspc::Literal& lBuild : aggregateRelation->getAggregate().getAggregateLiterals()){
                        if(literalIndex!=buildLitIndex){
                            *out << ind << "const Tuple* tuple"<<buildLitIndex<<"=w"<<lBuild.getPredicateName()<<".find(Tuple({";
                            for(int i=0;i<lBuild.getAriety();i++){
                                if(i>0)
                                    *out << ",";
                                *out << "joinTupleU->at("<<i+buildAriety<<")";
                            }
                            *out << "},&_"<<lBuild.getPredicateName()<<"));\n";
                            *out << ind << "const Tuple* tupleU"<<buildLitIndex<<"=u"<<lBuild.getPredicateName()<<".find(Tuple({";
                            for(int i=0;i<lBuild.getAriety();i++){
                                if(i>0)
                                    *out << ",";
                                *out << "joinTupleU->at("<<i+buildAriety<<")";
                            }
                            *out << "},&_"<<lBuild.getPredicateName()<<"));\n";   

                            
                            if(!lBuild.isPositiveLiteral()){
                                *out << ind << "const Tuple negativeTuple"<<buildLitIndex<<"({";
                                for(int i=0;i<lBuild.getAriety();i++){
                                    if(i>0)
                                        *out << ",";
                                    *out << "joinTupleU->at("<<i+buildAriety<<")";
                                }
                                *out << "},&_"<<lBuild.getPredicateName()<<",true);\n"; 

                                if(lBuild.getPredicateName()==l.getPredicateName() && lBuild.getAriety()==l.getAriety() && lBuild.isNegated()==l.isNegated()){
                                    onlyOneTrue+=" ((tuple"+std::to_string(buildLitIndex)+"==NULL && tupleU"+std::to_string(buildLitIndex)+"==NULL) || tupleU"+std::to_string(buildLitIndex)+"==tupleU) &&";
                                }else{
                                    onlyOneTrue+=" tuple"+std::to_string(buildLitIndex)+"==NULL && tupleU"+std::to_string(buildLitIndex)+"==NULL &&";
                                }
                            }else{
                                if(lBuild.getPredicateName()==l.getPredicateName() && lBuild.getAriety()==l.getAriety() && lBuild.isNegated()==l.isNegated()){
                                    onlyOneTrue+=" (tuple"+std::to_string(buildLitIndex)+"!=NULL || tupleU"+std::to_string(buildLitIndex)+"==tupleU) &&";
                                }else{
                                    onlyOneTrue+=" tuple"+std::to_string(buildLitIndex)+"!=NULL &&";
                                
                                }
                            }
                        }
                        buildAriety+=lBuild.getAriety();
                        buildLitIndex++;
                    }
                    if(onlyOneTrue!="")
                        *out << ind++ << "if("<<onlyOneTrue.substr(0,onlyOneTrue.length()-2)<<"){\n";
                        // if(l.getPredicateName()=="b")
                        //     *out << ind << "joinTupleU->print();\n";
                
                        if(withReason){
                            buildLitIndex=0;
                            buildAriety=0;
                            for(const aspc::Literal& lBuild : aggregateRelation->getAggregate().getAggregateLiterals()){
                                if(buildLitIndex!=literalIndex){
                                    if(lBuild.isNegated()){
                                        *out << ind++ << "if(tupleU"<<buildLitIndex<<"==NULL){\n";
                                            *out << ind << "const auto & it = tupleToVar.find(negativeTuple"<<buildLitIndex<<");\n";
                                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                *out << ind << "localReason.push_back(it->second * -1);\n";
                                            *out << --ind <<"}//closing if\n";
                                        *out << --ind <<"}//closing if\n";
                                    }else{
                                        *out << ind++ << "if(tupleU"<<buildLitIndex<<"==NULL){\n";
                                            *out << ind << "const auto & it = tupleToVar.find(*tuple"<<buildLitIndex<<");\n";
                                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                *out << ind << "localReason.push_back(it->second);\n";
                                            *out << --ind <<"}//closing if\n";
                                        *out << --ind <<"}//closing if\n";
                                    }
                                }
                                
                                buildAriety+=lBuild.getAriety();
                                buildLitIndex++;
                            }
                        }
                        if(aggregateRelation->getAggregate().isSum()){
                            *out << ind++ << "if(undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".find({"<<aggrVarProj<<"})==undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".end())\n";
                                *out << ind-- << "sumKey_"<<l.getPredicateName()<<"_"<<literalIndex<<"+=joinTupleU->at("<<aggregateVariablesIndex[aggregateIdentifier][0]<<");\n";
                        }
                        *out << ind << "undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".insert({"<<aggrVarProj<<"});\n";

                    if(onlyOneTrue!="")
                        *out << --ind << "}\n";

                }
                *out << --ind << "}\n";
            *out << --ind << "}\n";
            std::string plusOne = aggregateRelation->isPlusOne() ? "+1":"";
            if(aggregateRelation->getAggregate().isSum()){
                if(aggregateRelation->isNegated()){
                    *out << ind++ << "if(!(undefPlusTrue - sumKey_"<<l.getPredicateName()<<"_"<<literalIndex<<aggregateRelation->getCompareTypeAsString()<<aggregateRelation->getGuard().getStringRep()<<plusOne<<")){\n";
                }else
                    *out << ind++ << "if(actualSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[aggregateIdentifier]<<"}] + sumKey_"<<l.getPredicateName()<<"_"<<literalIndex<<aggregateRelation->getCompareTypeAsString()<<aggregateRelation->getGuard().getStringRep()<<plusOne<<"){\n";
            }else{
                if(aggregateRelation->isNegated()){
                    *out << ind++ << "if(!(undefPlusTrue-undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".size()"<<aggregateRelation->getCompareTypeAsString()<<aggregateRelation->getGuard().getStringRep()<<plusOne<<")){\n";
                }else{
                    *out << ind++ << "if(trueAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[aggregateIdentifier]<<"}].size()+undefKey_"<<l.getPredicateName()<<"_"<<literalIndex<<".size()"<<aggregateRelation->getCompareTypeAsString()<<aggregateRelation->getGuard().getStringRep()<<plusOne<<"){\n";
                }
            }

                *out << ind << "const auto & it_prop = tupleToVar.find(*tupleU);\n";
                std::string aggrTupleUNegated=l.isNegated() ? "-1":"1";
                if(aggregateRelation->isNegated()){
                    aggrTupleUNegated=l.isNegated() ? "1":"-1";
                }
                *out << ind++ << "if(it_prop != tupleToVar.end()) {\n";
                    *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                    // *out << ind << "tupleU->print();\n";
                    // if(aggregateRelation->isNegated())
                    //     *out << ind << "std::cout<<\"Prop multiple join not "<<literalIndex<<"\"<<std::endl;\n";
                    // else
                    //     *out << ind << "std::cout<<\"Prop multiple join "<<literalIndex<<" \"<<std::endl;\n";
                    if(withReason){
                        for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                            std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
                            if(aggr.isNegated())
                                // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                *out << ind << "localReason.insert(localReason.end(),negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                            
                            else
                                // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                *out << ind << "localReason.insert(localReason.end(),positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                            // buildReason(identifier,&aggr,false);
                        }
//                        *out << ind << "std::cout<<\"Local reason size with aggr: \"<<localReason.size();\n";
                        *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                            // *out << ind << "std::cout<<\"Adding starter\"<<std::endl;\n";
                            *out << ind << "localReason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
                        *out << --ind <<"}\n";
                        for(int j=1;j<joinOrder.size();j++){
                            if(body[joinOrder[j]]->isLiteral()){
                                const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                                *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                                    *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                        if(l->isNegated())
                                            *out << ind << "localReason.push_back(it->second * -1);\n";
                                        else
                                            *out << ind << "localReason.push_back(it->second);\n";
                                        // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                                    *out << --ind <<"}\n";
                                *out << --ind <<"}\n";
                            }
                        }
                            // *out << ind << "for(int v : localReason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                            // *out << ind << "std::cout<<std::endl;\n";
                    }
                    // *out << ind << "std::cout<<\"LitIndex: "<<literalIndex<<" prop multi join\"<<std::endl;\n";
                    // *out << ind << "propagatedLiteralsAndReasons.insert({it_prop->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                    *out << ind << "propagatedLiterals.push_back(it_prop->second*sign);\n";
                    //TODO adding reason mapping save

                *out << --ind <<"}\n";
              
            *out << --ind <<"}\n";
        *out << --ind << "}\n\n";
        literalIndex++;
        actualAriety+=l.getAriety();

    }
    // *out << ind << "std::cout<<\"end prof if multiple join\"<<std::endl;\n";

}
void CompilationManager::propAggr(const aspc::ArithmeticRelationWithAggregate* aggregateRelation,std::string& aggregateIdentifier,bool withReason,std::string op){

    std::string ruleId = aggregateIdentifier.substr(0,aggregateIdentifier.find(":"));
    std::string index = aggregateIdentifier.substr(aggregateIdentifier.find(":")+1,aggregateIdentifier.length());
    std::string joinTupleName = aggregateRelation->getJoinTupleName();

    std::string sharedVariableTuple=sharedVariablesMap[aggregateIdentifier];
    std::string op_ = aggregateRelation->isNegated() ? "->": ".";

    std::string aggrVarProjection="";
    std::string aggrVarTuple="";
    int aggrVarCount=0;
    
    for(unsigned v : aggregateVariablesIndex[aggregateIdentifier]){
        aggrVarProjection+=std::to_string(v)+"_";
        if(aggrVarCount>0)
            aggrVarTuple+=",";
        aggrVarTuple+="undefKey"+op_+"at("+std::to_string(aggrVarCount)+")";
        aggrVarCount++;
    }

    std::string sharedVarProjection="";
    for(unsigned v : sharedVariablesIndexesMap[aggregateIdentifier])
        sharedVarProjection+=std::to_string(v)+"_";
    std::string comma=sharedVariableTuple!="" ? ",":"";
    int pars=0;
    // *out << ind << "std::cout<<\" Start prop\"<<std::endl;\n";
    if(aggregateRelation->isNegated()){
        std::string reason = withReason ? "local_reason":"";
        // *out << ind << "std::cout<<undefPlusTrue<<std::endl;\n";
        std::string reverse_it = aggregateRelation->getAggregate().isSum() ? "r":"";
        *out << ind++ << "for(auto undefKey = undefAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"begin();undefKey!=undefAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"end();undefKey++){\n";
        pars++;
            // pars++;
        if(aggregateRelation->getAggregate().isSum()){
            std::string plusOne = aggregateRelation->isPlusOne() ? "+1":"";
            *out << ind++ << "if(undefPlusTrue-undefKey->at(0)"<<aggregateRelation->getCompareTypeAsString()<<aggregateRelation->getGuard().getStringRep()<<plusOne<<"+maxPossibleNegativeSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}])\n";
            *out << ind-- << "break;\n";
            *out << ind++ << "else{\n";
            pars++;

        }

        if(sharedVariablesMap[aggregateIdentifier]!=""){
            // *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &sharedVarTuple"<<ruleId<<"_"<<index<<".second"<<op_<<"second->getValues(*undefKey);\n";
            *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &u_"<<joinTupleName<<sharedVarProjection<<aggrVarProjection<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"});\n";
        }else{
            *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &u_"<<joinTupleName<<aggrVarProjection<<".getValues(*undefKey);\n";
        }
        // *out << ind++ << "if(u_"<<aggregateRelation->getJoinTupleName()<<sharedVarProjection<<aggrVarProjection<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"}).size() == 1){\n";
        *out << ind++ << "if(undefinedTuples->size()==1){\n"<<std::endl;
        pars++;
        int totalAriety=0;
        int litIndex=0;
        for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
            *out << ind << "const Tuple* tuple"<<litIndex<<" = u"<<l.getPredicateName()<<".find(Tuple({";
            for(int i=0;i<l.getAriety();i++){
                if(i>0)
                    *out << ",";
                *out << "undefinedTuples->at(0)->at("<<i+totalAriety<<")";
            }
            *out << "},&_"<<l.getPredicateName()<<"));\n";
            *out << ind++ << "if(tuple"<<litIndex<<"!=NULL){\n";
                *out << ind << "const auto & it"<<litIndex<<" = tupleToVar.find(*tuple"<<litIndex<<");\n";
                
                std::string aggrTupleUNegated=l.isNegated() ? "1":"-1";

                *out << ind++ << "if(it"<<litIndex<<" != tupleToVar.end()) {\n";
                    *out << ind << "propagated=true;\n";
                    // if(withReason){
                    //     *out<<ind<<"std::cout<<\"propagation reason\";\n";
                    //      *out << ind << "for(int v : "<<reason<<") {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                    //     // *out << ind << "for(int v : "<<reason<<") std::cout<<v<<\" \"<<std::endl;\n";
                    //     *out << ind << "std::cout<<std::endl;\n";
                    // }
                    // *out << ind << "std::cout<<\"Propagation Negated\";tuple"<<litIndex<<"->print();std::cout<<std::endl;\n";
                    *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                    // *out << ind << "propagatedLiteralsAndReasons.insert({it"<<litIndex<<"->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                    *out << ind << "propagatedLiterals.push_back(it"<<litIndex<<"->second*sign);\n";
                    if(withReason){
                        *out << ind << "reasonMapping.addPropagation(it"<<litIndex<<"->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariableTuple<<"});\n";
                        // *out << ind << "if(it"<<litIndex<<"->second*sign == 3) explainAggrLiteral(3);\n";
                    }
                *out << --ind <<"}\n";
            *out << --ind << "}\n";
            totalAriety+=l.getAriety();
            litIndex++;
        }

        while(pars>0){
            *out << --ind << "}\n";
            pars--;
        }
        *out << ind++ << "for(auto undefKey = undefNegativeAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"begin();undefKey!=undefNegativeAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"end();undefKey++){\n";
        pars++;
        
        aggrVarCount=0;
        aggrVarTuple="";
        for(int v : aggregateVariablesIndex[aggregateIdentifier]){
            if(aggrVarCount>0){
                aggrVarTuple+=",";
            }
            aggrVarTuple+="undefKey->at("+std::to_string(aggrVarCount)+")";
            aggrVarCount++;
        }
            // *out << ind++ << "if(p_"<<aggregateRelation->getJoinTupleName()<<sharedVarProjection<<aggrVarProjection<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"}).size() == 0){\n";
            // pars++;
        if(aggregateRelation->getAggregate().isSum()){
            std::string plusOne = aggregateRelation->isPlusOne() ? "+1":"";
            *out << ind++ << "if(undefPlusTrue+undefKey->at(0)"<<aggregateRelation->getCompareTypeAsString()<<aggregateRelation->getGuard().getStringRep()<<plusOne<<"+maxPossibleNegativeSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}])\n";
            *out << ind-- << "break;\n";
            *out << ind++ << "else{\n";
            pars++;

        }

        if(sharedVariablesMap[aggregateIdentifier]!=""){
            // *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &sharedVarTuple"<<ruleId<<"_"<<index<<".second"<<op_<<"second->getValues(*undefKey);\n";
            *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &nu_"<<joinTupleName<<sharedVarProjection<<aggrVarProjection<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"});\n";
        }else{
            *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &nu_"<<joinTupleName<<aggrVarProjection<<".getValues({"<<aggrVarTuple<<"});\n";
        }
        // *out << ind++ << "if(u_"<<aggregateRelation->getJoinTupleName()<<sharedVarProjection<<aggrVarProjection<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"}).size() == 1){\n";
        if(aggregateRelation->getAggregate().isSum()){
            *out << ind++ << "for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){\n"<<std::endl;
            pars++;
            int starterAriety=0;
            int startLit=0;
            *out << ind << "bool negativeJoinPropagated=false;\n";
            for(const aspc::Literal& starter : aggregateRelation->getAggregate().getAggregateLiterals()){
                *out << ind << "const Tuple* tupleU"<<startLit<<" = u"<<starter.getPredicateName()<<".find(Tuple({";
                for(int i=0;i<starter.getAriety();i++){
                    if(i>0)
                        *out << ",";
                    *out << "undefinedTuples->at(iUndef)->at("<<i+starterAriety<<")";
                }
                *out << "},&_"<<starter.getPredicateName()<<"));\n";
                *out << ind++ << "if(tupleU"<<startLit<<"!=NULL && !negativeJoinPropagated){\n";
                int buildAriety=0;
                int buildLit=0;
                *out << ind <<"std::vector<int> reas;\n";
                for(const aspc::Literal& build : aggregateRelation->getAggregate().getAggregateLiterals()){
                    if(startLit!=buildLit){
                        *out << ind << "Tuple tuple"<<buildLit<<" ({";
                        for(int i=0;i<build.getAriety();i++){
                            if(i>0)
                                *out << ",";
                            *out << "undefinedTuples->at(iUndef)->at("<<i+buildAriety<<")";
                        }
                        *out << "},&_"<<build.getPredicateName()<<");\n";
                        std::string same_of_start="";
                        if(starter.getPredicateName() == build.getPredicateName() && starter.isNegated()==build.isNegated())
                            same_of_start= " || *tupleU"+std::to_string(startLit)+"==tuple"+std::to_string(buildLit);

                        if(build.isNegated()){
                            *out << ind++ << "if((w"<<build.getPredicateName()<<".find(tuple"<<buildLit<<")==NULL && u"<<build.getPredicateName()<<".find(tuple"<<buildLit<<")==NULL) "<<same_of_start<<"){\n";
                        }else{
                            *out << ind++ << "if((w"<<build.getPredicateName()<<".find(tuple"<<buildLit<<")!=NULL) "<<same_of_start<<"){\n";
                        }
                            if(starter.getPredicateName() == build.getPredicateName() && starter.isNegated()==build.isNegated()){
                                *out << ind++ << "if(*tupleU"<<startLit<<"!=tuple"<<buildLit<<"){\n";
                            }
                            *out << ind << "const auto & it"<<buildLit<<" = tupleToVar.find(tuple"<<buildLit<<");\n";
                            *out << ind++ << "if(it"<<buildLit<<" != tupleToVar.end()) {\n";
                                if(build.isNegated()){
                                    *out << ind << "reas.push_back(it"<<buildLit<<"->second*-1);\n";
                                }else{
                                    *out << ind << "reas.push_back(it"<<buildLit<<"->second);\n";
                                }
                            *out << --ind << "}\n";
                            if(starter.getPredicateName() == build.getPredicateName() && starter.isNegated()==build.isNegated()){
                                *out << --ind << "}\n";
                            }

                    }
                    buildLit++;
                    buildAriety+=build.getAriety();
                }
            
                    *out << ind << "const auto & it"<<startLit<<" = tupleToVar.find(*tupleU"<<startLit<<");\n";
                    
                    std::string aggrTupleUNegated=starter.isNegated() ? "-1":"1";

                    *out << ind++ << "if(it"<<startLit<<" != tupleToVar.end()) {\n";
                        *out << ind << "negativeJoinPropagated=true;\n";
                        if(withReason){
                            // *out << ind << "for(int v: reas){ "<<reason<<".push_back(v); }\n";
                            // *out<<ind<<"std::cout<<\"propagation reason\";\n";
                            //  *out << ind << "for(int v : "<<reason<<") {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                            // // *out << ind << "for(int v : local_reason) std::cout<<v<<\" \"<<std::endl;\n";
                            // *out << ind << "std::cout<<std::endl;\n";
                        }
                        // *out << ind << "std::cout<<\"Propagation Negated Negative join\";tupleU"<<startLit<<"->print();std::cout<<std::endl;\n";
                        *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                        // *out << ind << "propagatedLiteralsAndReasons.insert({it"<<startLit<<"->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                        *out << ind << "propagatedLiterals.push_back(it"<<startLit<<"->second*sign);\n";
                        if(withReason){
                            *out << ind << "for(int v: reas){ bodyReason.push_back(v); }\n";
                            //TODO adding externalLiteral
                            *out << ind << "reasonMapping.addPropagation(it"<<startLit<<"->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariableTuple<<"});\n";
                            // *out << ind << "if(it"<<startLit<<"->second*sign == 3) explainAggrLiteral(3);\n";
                            *out << ind << "while(!reas.empty()){ bodyReason.pop_back(); reas.pop_back();}\n";

                        }
                        if(withReason){
                            // *out << ind << "while(!reas.empty()){ "<<reason<<".pop_back(); reas.pop_back();}\n";
                        }
                    *out << --ind <<"}\n";
                while (buildLit>0){
                    buildLit--;
                    *out << --ind << "}\n";
                }
                
                starterAriety+=starter.getAriety();
                startLit++;
            }
        }else{
            *out << ind++ << "if(undefinedTuples->size()==1){\n"<<std::endl;
            pars++;
            int starterAriety=0;
            int startLit=0;
            for(const aspc::Literal& starter : aggregateRelation->getAggregate().getAggregateLiterals()){
                *out << ind++ << "{\n";
                    *out << ind << "const Tuple* tupleU = u"<<starter.getPredicateName()<<".find(Tuple({";
                    for(int i=0;i<starter.getAriety();i++){
                        if(i>0)
                            *out << ",";
                        *out << "undefinedTuples->at(0)->at("<<i+starterAriety<<")";
                    }
                    *out << "},&_"<<starter.getPredicateName()<<"));\n";
                    *out << ind++ << "if(tupleU!=NULL){\n";
                
                        *out << ind << "const auto & it = tupleToVar.find(*tupleU);\n";
                            
                        std::string aggrTupleUNegated=starter.isNegated() ? "1":"-1";

                        *out << ind++ << "if(it != tupleToVar.end()) {\n";
                            // *out << ind << "std::cout<<\"Propagation Negated Negative join\";tupleU->print();std::cout<<std::endl;\n";
                            *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                            // *out << ind << "propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                            *out << ind << "propagatedLiterals.push_back(it->second*sign);\n";
                            if(withReason){
                                //TODO adding body literals
                                *out << ind << "reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariableTuple<<"});\n";
                                // *out << ind << "if(it->second*sign == 3) explainAggrLiteral(3);\n";
                            }
                        *out << --ind <<"}\n";
                    *out << --ind <<"}\n";
                *out << --ind <<"}\n";
                starterAriety+=starter.getAriety();
                startLit++;
            }
        }
        
        
    }else{
        std::string reason = withReason ? "propagationReason":"";
        std::string reverse_it = aggregateRelation->getAggregate().isSum() ? "r":"";
        // *out << ind << "for(const auto& k : trueAggrVars[0][{U,U,U}]) std::cout<<k[0]<<\" \"<<k[1]<<std::endl;\n";
        *out << ind++ << "for(auto undefKey = undefAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"begin();undefKey!=undefAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"end();undefKey++){\n";
        pars++;

        if(aggregateRelation->getAggregate().isSum()){
            std::string plusOne = aggregateRelation->isPlusOne() ? "+1":"";
            *out << ind++ << "if(actualSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]+actualNegativeSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]+undefKey->at(0) < "<<aggregateRelation->getGuard().getStringRep()<<plusOne<<"+maxPossibleNegativeSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}])\n";
                *out << ind-- << "break;\n";
            *out << ind++ << "else{\n";
            pars++;

        }
        std::string sharedVarIndex;
        for(unsigned v:sharedVariablesIndexesMap[aggregateIdentifier]){
            sharedVarIndex+=std::to_string(v)+"_";
        }
        std::string aggrVarTuple;
        std::string aggrVarIndex;
        int aggrVarCount=0;
        for(int v : aggregateVariablesIndex[aggregateIdentifier]){
            aggrVarIndex+=std::to_string(v)+"_";
            if(aggrVarCount>0){
                aggrVarTuple+=",";
            }
            aggrVarTuple+="undefKey->at("+std::to_string(aggrVarCount)+")";
            aggrVarCount++;
        }
        std::string comma = sharedVariableTuple!="" ? ",":"";
        *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &u_"<<aggregateRelation->getJoinTupleName()<<sharedVarIndex<<aggrVarIndex<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"});\n";
        *out << ind++ << "for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){\n";
        pars++;
            // *out << ind << "undefinedTuples->at(iUndef)->print();std::cout<<std::endl;\n";
        int startingIndex=0;
        int litIndex=0;
        *out << ind << "bool found=false;\n";
        for(const aspc::Literal& startingLit : aggregateRelation->getAggregate().getAggregateLiterals()){
            *out << ind++ <<"if(!found){\n";
                *out << ind << "const Tuple* aggrTupleU"<<litIndex<<" = u"<<startingLit.getPredicateName()<<".find(Tuple({";
                for(int i=0;i<startingLit.getAriety();i++){
                    if(i>0)
                        *out <<", ";
                    *out << "undefinedTuples->at(iUndef)->at("<<startingIndex+i<<")";
                }
                *out << "},&_"<<startingLit.getPredicateName()<<"));\n";
        
                int buildLitIndex=0;
                int buildingIndex=0;
                std::string oneUndefIf="aggrTupleU"+std::to_string(litIndex)+"!=NULL ";
                std::vector<std::pair<bool,std::string>> reasonLiterals;
                for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
                    if(buildLitIndex!=litIndex){
                        char trueMap='w';
                        *out << ind << "const Tuple* tuple"<<buildLitIndex<<" = "<<trueMap<<l.getPredicateName()<<".find(Tuple({";
                        for(int i=0;i<l.getAriety();i++){
                            if(i>0)
                                *out <<", ";
                            *out << "undefinedTuples->at(iUndef)->at("<<buildingIndex+i<<")";
                        }
                        *out << "},&_"<<l.getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU"<<buildLitIndex<<" = u"<<l.getPredicateName()<<".find(Tuple({";
                        for(int i=0;i<l.getAriety();i++){
                            if(i>0)
                                *out <<", ";
                            *out << "undefinedTuples->at(iUndef)->at("<<buildingIndex+i<<")";
                        }
                        *out << "},&_"<<l.getPredicateName()<<"));\n";
                        if(l.isNegated()){
                            *out << ind << "const Tuple negativeTuple"<<buildLitIndex<<" ({";
                            for(int i=0;i<l.getAriety();i++){
                                if(i>0)
                                    *out <<", ";
                                *out << "undefinedTuples->at(iUndef)->at("<<buildingIndex+i<<")";
                            }
                            *out << "},&_"<<l.getPredicateName()<<",true);\n";

                            if(l.getPredicateName()==startingLit.getPredicateName() && l.getAriety()==startingLit.getAriety() && l.isNegated()==startingLit.isNegated())
                                oneUndefIf += "&& ((tuple"+std::to_string(buildLitIndex)+"==NULL && tupleU"+std::to_string(buildLitIndex)+"==NULL) || (tupleU"+std::to_string(buildLitIndex)+"==aggrTupleU"+std::to_string(litIndex)+"))";
                            else
                                oneUndefIf += "&& (tuple"+std::to_string(buildLitIndex)+"==NULL && tupleU"+std::to_string(buildLitIndex)+"==NULL)";
                            reasonLiterals.push_back({l.isNegated(),"negativeTuple"+std::to_string(buildLitIndex)});

                        
                        }else{
                            if(l.getPredicateName()==startingLit.getPredicateName() && l.getAriety()==startingLit.getAriety() && l.isNegated()==startingLit.isNegated())
                                oneUndefIf += "&& (tuple"+std::to_string(buildLitIndex)+"!=NULL || tupleU"+std::to_string(buildLitIndex)+"==aggrTupleU"+std::to_string(litIndex)+")";
                            else
                                oneUndefIf += "&& tuple"+std::to_string(buildLitIndex)+"!=NULL ";
                            reasonLiterals.push_back({l.isNegated(),"tuple"+std::to_string(buildLitIndex)});

                        }

                    }
                    buildLitIndex++;
                    buildingIndex+=l.getAriety();
                }
                *out <<ind++ <<"if("<<oneUndefIf<<"){\n";
                    if(withReason){
                        *out << ind << "std::vector<int> propagationReason(bodyReason);\n";
                        for(const std::pair<bool,std::string>& pair : reasonLiterals){
                            if(!pair.first)
                                *out << ind++ << "if("<<pair.second<<"!=NULL){\n";
                            else{
                                std::string tupleName="negativeTuple";
                                std::string tupleIndex = pair.second.substr(tupleName.length(),pair.second.length()-tupleName.length());
                                *out << ind++ << "if(tupleU"<<tupleIndex<<" == NULL){\n";// && tupleU"<<tupleIndex<<"->getPredicateName() == aggrTupleU"<<litIndex<<"->getPredicateName() && tupleU"<<tupleIndex<<"!=aggrTupleU"<<litIndex<<"){\n";
                            }
                                std::string star = pair.first ? "":"*";
                                *out << ind << "const auto & it_"<<pair.second<<" = tupleToVar.find("<<star<<pair.second<<");\n";
                                *out << ind++ << "if(it_"<<pair.second<<"!=tupleToVar.end()){\n";
                                    std::string negatedLiteralReason= pair.first ? "-1":"1";
                                    *out << ind << reason << ".push_back(it_"<<pair.second<<"->second * "<<negatedLiteralReason<<");\n";
                                *out << --ind <<"}//closing if\n";
                            // if(!pair.first)
                            *out << --ind <<"}//closing if\n";
                        }
                    }
                    *out << ind << "const auto & it = tupleToVar.find(*aggrTupleU"<<litIndex<<");\n";
                    std::string aggrTupleUNegated=startingLit.isNegated() ? "-1":"1";

                    *out << ind++ << "if(it != tupleToVar.end()) {\n";
                        *out << ind << "propagated=true;\n";
                        *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                        // if(withReason){
                        //     *out << ind << "for(int v : "<<reason<<") {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                        // }
                        // *out << ind << "std::cout<<\"Propagation positive "<<ruleId<<" \";aggrTupleU"<<litIndex<<"->print();std::cout<<std::endl;\n";
                        *out << ind << "found=true;\n";
                        // *out << ind << "propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                        *out << ind << "propagatedLiterals.push_back(it->second*sign);\n";
                        if(withReason){
                            //TODO adding body literals
                            *out << ind << "reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,propagationReason,{"<<sharedVariableTuple<<"});\n";
                            // *out << ind << "if(it->second*sign == 3) explainAggrLiteral(3);\n";
                        }
                    *out << --ind <<"}\n";
                // *out << --ind <<"}else{\n";
                *out << --ind << "}\n";
                litIndex++;
                startingIndex+=startingLit.getAriety();
            *out << --ind << "}\n"; 
        }
        while(pars>0){
            *out << --ind << "}\n";
            pars--;
        }
        
        *out << ind++ << "for(auto undefKey = undefNegativeAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"begin();undefKey!=undefNegativeAggrVars["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]."<<reverse_it<<"end();undefKey++){\n";
        pars++;
        aggrVarCount=0;
        aggrVarTuple="";
        for(int v : aggregateVariablesIndex[aggregateIdentifier]){
            if(aggrVarCount>0){
                aggrVarTuple+=",";
            }
            aggrVarTuple+="undefKey->at("+std::to_string(aggrVarCount)+")";
            aggrVarCount++;
        }
        if(aggregateRelation->getAggregate().isSum()){
            std::string plusOne = aggregateRelation->isPlusOne() ? "+1":"";
            *out << ind++ << "if(actualSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]+actualNegativeSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}]-undefKey->at(0) < "<<aggregateRelation->getGuard().getStringRep()<<plusOne<<"+maxPossibleNegativeSum["<<aggregateToStructure[aggregateRelation->getJoinTupleName()+sharedVariablesMap[aggregateIdentifier]+aggregateRelation->getAggrVarAsString()]<<"][{"<<sharedVariableTuple<<"}])\n";
            *out << ind-- << "break;\n";
            *out << ind++ << "else{\n";

            pars++;

        }
        *out << ind << "const std::vector<const Tuple*>* undefinedTuples = &nu_"<<aggregateRelation->getJoinTupleName()<<sharedVarIndex<<aggrVarIndex<<".getValues({"<<sharedVariableTuple<<comma<<aggrVarTuple<<"});\n";
        if(aggregateRelation->getAggregate().isSum()){
            *out << ind++ << "if(undefinedTuples->size()==1){\n";
            pars++;
            
            int start_lit=0;
            int start_ariety=0;
            for(const aspc::Literal& startingLit : aggregateRelation->getAggregate().getAggregateLiterals()){
                *out << ind++ << "{\n";
                    *out << ind << "Tuple tuple"<<start_lit<<" ({";
                    for(int i=0;i<startingLit.getAriety();i++){
                        if(i>0)
                            *out <<", ";
                        *out << "undefinedTuples->at(0)->at("<<start_ariety+i<<")";
                    }
                    *out << "},&_"<<startingLit.getPredicateName()<<");\n";
                    *out <<ind++ <<"if(u"<<startingLit.getPredicateName()<<".find(tuple"<<start_lit<<")!=NULL){\n";
                        if(withReason){
                            // *out << ind << "std::vector<int> propagationReason(local_reason);\n";
                            //TODO adding reason
                        }
                        *out << ind << "const auto & it = tupleToVar.find(tuple"<<start_lit<<");\n";
                        std::string aggrTupleUNegated=startingLit.isNegated() ? "1":"-1";

                        *out << ind++ << "if(it != tupleToVar.end()) {\n";
                            *out << ind << "propagated=true;\n";
                            *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                            if(withReason){
                                // *out<<ind<<"if("<<reason<<".size() != wtd.getTuples().size()+wfactor.getTuples().size()+3) std::cout<<\"propagation reason mismatch: \"<<std::endl;\n";
                                // *out << ind << "for(int v : "<<reason<<") {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                            }
                            // *out << ind << "std::cout<<\"Propagation positive negative join"<<ruleId<<" \";tuple"<<start_lit<<".print();std::cout<<std::endl;\n";
                            // *out << ind << "propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                            *out << ind << "propagatedLiterals.push_back(it->second*sign);\n";
                            if(withReason){
                                //TODO adding body literals
                                *out << ind << "reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariableTuple<<"});\n";
                                // *out << ind << "if(it->second*sign == 3) explainAggrLiteral(3);\n";
                            }
                        *out << --ind <<"}\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n"; 
                start_lit++;
                start_ariety+=startingLit.getAriety();
            }
        }else{
            *out << ind++ << "for(int iUndef=0;iUndef<undefinedTuples->size();iUndef++){\n"<<std::endl;
            pars++;
            int starterAriety=0;
            int startLit=0;
            *out << ind << "bool negativeJoinPropagated=false;\n";
            for(const aspc::Literal& starter : aggregateRelation->getAggregate().getAggregateLiterals()){
                *out << ind << "const Tuple* tupleU"<<startLit<<" = u"<<starter.getPredicateName()<<".find(Tuple({";
                for(int i=0;i<starter.getAriety();i++){
                    if(i>0)
                        *out << ",";
                    *out << "undefinedTuples->at(iUndef)->at("<<i+starterAriety<<")";
                }
                *out << "},&_"<<starter.getPredicateName()<<"));\n";
                *out << ind++ << "if(tupleU"<<startLit<<"!=NULL && !negativeJoinPropagated){\n";
                int buildAriety=0;
                int buildLit=0;
                if(withReason){
                    *out << ind << "std::vector<int> "<<reason<<"(bodyReason);\n";
                    //TODO adding reason
                }
                for(const aspc::Literal& build : aggregateRelation->getAggregate().getAggregateLiterals()){
                    if(startLit!=buildLit){
                        *out << ind << "Tuple tuple"<<buildLit<<" ({";
                        for(int i=0;i<build.getAriety();i++){
                            if(i>0)
                                *out << ",";
                            *out << "undefinedTuples->at(iUndef)->at("<<i+buildAriety<<")";
                        }
                        *out << "},&_"<<build.getPredicateName()<<");\n";

                        std::string same_of_start="";
                        if(starter.getPredicateName() == build.getPredicateName() && starter.isNegated()==build.isNegated())
                            same_of_start= " || *tupleU"+std::to_string(startLit)+"==tuple"+std::to_string(buildLit);

                        if(build.isNegated()){
                            *out << ind++ << "if((w"<<build.getPredicateName()<<".find(tuple"<<buildLit<<")==NULL && u"<<build.getPredicateName()<<".find(tuple"<<buildLit<<")==NULL) "<<same_of_start<<"){\n";
                        }else{
                            *out << ind++ << "if((w"<<build.getPredicateName()<<".find(tuple"<<buildLit<<")!=NULL) "<<same_of_start<<"){\n";
                        }

                        if(withReason){
                            if(starter.getPredicateName() == build.getPredicateName() && starter.isNegated()==build.isNegated()){
                                *out << ind++ << "if(*tupleU"<<startLit<<"!=tuple"<<buildLit<<"){\n";
                            }
                            *out << ind << "const auto & it"<<buildLit<<" = tupleToVar.find(tuple"<<buildLit<<");\n";
                            *out << ind++ << "if(it"<<buildLit<<" != tupleToVar.end()) {\n";
                                if(build.isNegated()){
                                    *out << ind << reason << ".push_back(it"<<buildLit<<"->second*-1);\n";
                                }else{
                                    *out << ind << reason << ".push_back(it"<<buildLit<<"->second);\n";
                                }
                            *out << --ind << "}\n";
                            if(starter.getPredicateName() == build.getPredicateName() && starter.isNegated()==build.isNegated()){
                                *out << --ind << "}\n";
                            }
                        }
                        
                    

                    }
                    buildLit++;
                    buildAriety+=build.getAriety();
                }
            
                    *out << ind << "const auto & it"<<startLit<<" = tupleToVar.find(*tupleU"<<startLit<<");\n";
                    
                    std::string aggrTupleUNegated=starter.isNegated() ? "-1":"1";

                    *out << ind++ << "if(it"<<startLit<<" != tupleToVar.end()) {\n";
                        *out << ind << "negativeJoinPropagated=true;\n";
                        // *out << ind << "std::cout<<\"Propagation Negated Negative join\";tupleU"<<startLit<<"->print();std::cout<<std::endl;\n";
                        *out << ind << "int sign = "<<aggrTupleUNegated<<";\n";
                        // *out << ind << "propagatedLiteralsAndReasons.insert({it"<<startLit<<"->second*sign, std::vector<int>("<<reason<<")}).first->second;\n";
                        *out << ind << "propagatedLiterals.push_back(it"<<startLit<<"->second*sign);\n";
                        if(withReason){
                            //TODO adding body literals
                            *out << ind << "reasonMapping.addPropagation(it"<<startLit<<"->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,"<<reason<<",{"<<sharedVariableTuple<<"});\n";
                            // *out << ind << "if(it"<<startLit<<"->second*sign == 3) explainAggrLiteral(3);\n";
                        }
                    *out << --ind <<"}\n";
                while (buildLit>0){
                    buildLit--;
                    *out << --ind << "}\n";
                }
                
                starterAriety+=starter.getAriety();
                startLit++;
            }
        }
        
    }
    while(pars>0){
        *out << --ind << "}\n";
        pars--;
    }
}
void CompilationManager::printCanPropagateIf(std::string aggrIdentifier,const aspc::ArithmeticRelationWithAggregate* aggr,std::string op,bool bound){
    std::string ruleId = aggrIdentifier.substr(0,aggrIdentifier.find(":"));
    std::string index = aggrIdentifier.substr(aggrIdentifier.find(":")+1,aggrIdentifier.length());

    op = sharedVariablesMap[aggrIdentifier]!="" ? "->":".";
    std::string sharedVarProjection;
    for(unsigned v : sharedVariablesIndexesMap[aggrIdentifier]){
        sharedVarProjection+=std::to_string(v)+"_";
    }
    if(!aggr->getAggregate().isSum() && bound){
        if(aggr->isNegated()){
            std::string plusOne = aggr->isPlusOne() ? "+1": "";
            *out << ind++ << "if(undefPlusTrue == "<<aggr->getGuard().getStringRep()<<plusOne<<"){\n";
        }else{
            std::string plusOne = aggr->isPlusOne() ? "": "-1";
            *out << ind++ << "if((int)(trueAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[aggrIdentifier]<<"}].size()+trueNegativeAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[aggrIdentifier]<<"}].size()) == "<<aggr->getGuard().getStringRep()<<plusOne<<"){\n";
        }
    }else {
        *out << ind++ <<"{\n";
    }
}

void CompilationManager::printAggregateTrueIf(std::string aggrIdentifier,const aspc::ArithmeticRelationWithAggregate* aggr,std::string joinTupleName,std::string op,bool isBound){
    std::string sharedVars = sharedVariablesMap[aggrIdentifier];

    std::string ruleId = aggrIdentifier.substr(0,aggrIdentifier.find(":"));
    std::string index = aggrIdentifier.substr(aggrIdentifier.find(":")+1,aggrIdentifier.length());
    std::string plusOne = aggr->isPlusOne() ? "+1" : "";

    // *out << ind << "std::cout<<actualSum["<<aggr->getJoinTupleName()<<sharedVariablesMap[aggrIdentifier]<<"\"][{"<<sharedVars<<"}]<<\""<<aggr->getJoinTupleName()<<sharedVariablesMap[aggrIdentifier]<<"<<std::endl;\n";
    if(!aggr->isNegated()){
        if(isBound)
            if(!aggr->getAggregate().isSum())
                *out << ind++ << "if((int)(trueAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size()+trueNegativeAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size())"<<aggr->getCompareTypeAsString()<<aggr->getGuard().getStringRep()<<plusOne<<"){\n";
            else
                *out << ind++ << "if(actualSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]+actualNegativeSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]"<<aggr->getCompareTypeAsString()<<aggr->getGuard().getStringRep()<<plusOne<<"+maxPossibleNegativeSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]){\n";
        else {
            if(!aggr->getAggregate().isSum())
                *out << ind << "int count"<<ruleId<<"_"<<aggr->getFormulaIndex()<<" = trueAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size()+trueNegativeAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size();\n";
            else
                *out << ind << "int count"<<ruleId<<"_"<<aggr->getFormulaIndex()<<" = actualSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]+actualNegativeSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}];\n";
            *out << ind++ << "{\n";
        }

    }else{
        if(aggr->getAggregate().isSum()){
            *out << ind << "int undefPlusTrue = actualSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]+possibleSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]+actualNegativeSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}]+possibleNegativeSum["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}];\n";
        }else{
            *out << ind << "int undefPlusTrue = trueAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size()+undefAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size()+trueNegativeAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size()+undefNegativeAggrVars["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVars<<"}].size();\n";
        }
        if(isBound){
            *out << ind << "//"<<aggr->getGuard().getStringRep()<<"\n";
            // *out << ind << "std::cout<<\"aggr size: \"<<undefPlusTrue<<std::endl;\n";
            std::string plusSum = aggr->getAggregate().isSum() ? "+maxPossibleNegativeSum["+std::to_string(aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[aggrIdentifier]+aggr->getAggrVarAsString()])+"][{"+sharedVars+"}]":"";
            *out << ind++ << "if(!(undefPlusTrue"<<aggr->getCompareTypeAsString()<<aggr->getGuard().getStringRep()<<plusOne<<plusSum<<")){\n";
        }else{
            *out << ind << "int count"<<ruleId<<"_"<<aggr->getFormulaIndex()<<" = undefPlusTrue;\n";
            *out << ind++ << "{\n";
        }
    }
}
void CompilationManager::evaluationEndingWithAggregate(const aspc::Rule & r,std::vector<unsigned> joinOrder,unsigned start){

    const std::vector<const aspc::Formula*>& body = r.getFormulas();
    bool reason = start != joinOrder.size();
    std::string printReason = reason ? "local_reason":"";
    // *out << ind << "std::cout<<\"Evaluation starting from: literal\"<<std::endl;\n";
    int closingParenthesis=0;
    std::unordered_set<std::string> boundVariables;
    std::vector<const aspc::ArithmeticRelationWithAggregate*> aggregates;
    
    //print body literal join loops
    for(int i=0;i<joinOrder.size();i++){
        const aspc::Formula* f = r.getFormulas()[joinOrder[i]];
        if(f->containsAggregate()){
            aggregates.push_back((const aspc::ArithmeticRelationWithAggregate*)f);
        }else if (i != 0 || start == r.getBodySize()) {
            if (f->isLiteral()) {
                aspc::Literal* l = (aspc::Literal*)f;
                if (l->isNegated() || l->isBoundedLiteral(boundVariables)) {
                    if (mode == LAZY_MODE) {
                        std::string negation = "";
                        if (l->isNegated()) {
                            negation = "!";
                        }
                        *out << ind << "const Tuple * tuple" << i << " = w" << l->getPredicateName() << ".find({";
                        printLiteralTuple(l);
                        *out << "});\n";
                        *out << ind++ << "if(" << negation << "tuple" << i << "){\n";
                        closingParenthesis++;
                    } else {
                        //mode == EAGER_MODE
                        bool appearsBefore = literalPredicateAppearsBeforeSameSign(body, joinOrder, i);
                        if(appearsBefore && l->isPositiveLiteral()) {
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind++ << "if(tupleU && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<"){\n";
                            *out << ind << "const Tuple * undefRepeatingTuple = (u" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")));\n";

                            //  && tupleUNegated added. undefRepeatingTuple have to share also sign
                            *out << ind++ << "if(tupleU == undefRepeatingTuple && !tupleUNegated){\n";
                            *out << ind << "tuple" << i << " = undefRepeatingTuple;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(!tuple"<<i<<"){\n";
                            *out << ind << "tuple" << i << " = (w" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")));\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(!tuple"<<i<<" && !tupleU){\n";
                            *out << ind << "tupleU = (u" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")));\n";
                            *out << ind << "tuple" << i << " = tupleU;\n";
                            //------------------------------DEBUGGING------------------------------
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                            // *out << ind << "tupleUNegated = false;\n";
                            *out << ind++ << "if(tuple" << i << "){\n";
                            closingParenthesis++;
                        }
                        else if(appearsBefore && l->isNegated()) {
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind << "const Tuple negativeTuple = Tuple({";
                            printLiteralTuple(l);
                            *out << "}, &_" << l->getPredicateName() << ", true);\n";
                            *out << ind++ << "if(tupleU && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<"){\n;";
                            *out << ind << "const Tuple * undefRepeatingTuple = (u" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")));\n";
                            //  && tupleUNegated added. undefRepeatingTuple have to share also sign
                            *out << ind++ << "if(tupleU == undefRepeatingTuple && tupleUNegated){\n";
                            *out << ind << "tuple" << i << " = undefRepeatingTuple;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(!tuple"<<i<<"){\n;";
                            *out << ind++ << "if(!(w" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);

                            // //----------------------------------MODIFIED FOR DEBUGGING----------------------------------
                            *out << "},&_"<<l->getPredicateName()<<"))) && !(u" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            // //------------------------------------------------------------------------------------------

                            *out << "},&_"<<l->getPredicateName()<<")))){\n";
                            *out << ind << "tuple" << i << " = &negativeTuple;\n";
                            
                            // //----------------------------------MODIFIED FOR DEBUGGING----------------------------------
                            *out << --ind << "}else if(!tupleU && !(w"<<l->getPredicateName()<<".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")))){\n";
                            *out << ++ind << "tuple"<<i<<" = tupleU = &negativeTuple;\n";
                            *out << ind << "tupleUNegated=true;\n";
                            // //------------------------------------------------------------------------------------------

                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(tuple" << i << "){\n";
                            closingParenthesis++;
                        }
                        else if (l->isNegated()) {
                            *out << ind << "const Tuple negativeTuple = Tuple({";
                            printLiteralTuple(l);
                            *out << "}, &_" << l->getPredicateName() << ", true);\n";
                            *out << ind << "const Tuple * tuple" << i << " = &negativeTuple;\n";
                            *out << ind << "bool lTrue = (w" << l->getPredicateName() << ".find(negativeTuple)!=NULL);\n";
                            *out << ind << "const Tuple * undefTuple = u" << l->getPredicateName() << ".find(negativeTuple);\n";
                            *out << ind++ << "if((!lTrue && undefTuple == NULL) || (undefTuple && tupleU == NULL)){\n";
                            *out << ind++ << "if(undefTuple){\n";
                            *out << ind << "tuple" << i << " = tupleU = undefTuple;\n";
                            // *out << ind << "tupleU->print();\n";
                            *out << ind << "tupleUNegated = true;\n";
                            *out << --ind << "}\n";
                            closingParenthesis++;

                        } else {
                            *out << ind << "const Tuple * tuple" << i << " = (w" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")));\n";
                            *out << ind++ << "if(!tuple" << i << " && !tupleU ){\n";
                            *out << ind << "tuple" << i << " = tupleU = (u" << l->getPredicateName() << ".find(Tuple({";
                            printLiteralTuple(l);
                            *out << "},&_"<<l->getPredicateName()<<")));\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(tuple" << i << "){\n";
                            closingParenthesis++;

                        }
                    }

                } else {
                    std::string mapVariableName = l->getPredicateName() + "_";
                    for (unsigned t = 0; t < l->getAriety(); t++) {
                        if ((l->isVariableTermAt(t) && boundVariables.count(l->getTermAt(t))) || !l->isVariableTermAt(t)) {
                            mapVariableName += std::to_string(t) + "_";
                        }
                    }
                    if (mode == LAZY_MODE) {
                        *out << ind << "const std::vector<const Tuple* >& tuples = p" << mapVariableName << ".getValues({";
                        printLiteralTuple(l, boundVariables);
                        *out << "});\n";
                        *out << ind++ << "for( unsigned i=0; i< tuples.size();i++){\n";
                        *out << ind << "const Tuple * tuple" << i << " = tuples[i];\n";
                        closingParenthesis++;

                    } else {
                        //mode == EAGER_MODE
                        *out << ind << "const std::vector<const Tuple* >* tuples;\n";
                        *out << ind << "tuples = &p" << mapVariableName << ".getValues({";
                        printLiteralTuple(l, boundVariables);
                        *out << "});\n";
                        *out << ind << "const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;\n";
                        bool appearsBefore = literalPredicateAppearsBeforeSameSign(body, joinOrder, i);
                        if (appearsBefore) {
                            *out << ind << "std::vector<const Tuple* > tupleUInVector;\n";
                        }
                        *out << ind++ << "if(tupleU == NULL){\n";
                        *out << ind << "tuplesU = &u" << mapVariableName << ".getValues({";
                        printLiteralTuple(l, boundVariables);
                        *out << "});\n";
                        *out << --ind << "}\n";
                        //repeating literal case

                        if (appearsBefore) {
                            *out << ind++ << "else {\n";
                            //handle constants and equal cards?
                            *out << ind++ << "if(tupleU && !tupleUNegated && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<") {\n";
                            //check that bound variables have proper value
                            vector<unsigned> boundIndexes;
                            for(unsigned v = 0; v < l->getAriety(); v++) {
                                if(boundVariables.count(l->getTermAt(v))) {
                                    boundIndexes.push_back(v);
                                }
                            }
                            if(boundIndexes.size()) {
                                *out << ind++ << "if(";
                                    for(unsigned bi = 0; bi < boundIndexes.size(); bi++) {
                                        if(bi > 0) {
                                            *out << " && ";
                                        }
                                        *out << "tupleU->at(" << boundIndexes[bi] << ") == " << l->getTermAt(boundIndexes[bi]);
                                    }
                                    *out << "){\n";
                            }

                            *out << ind << "tupleUInVector.push_back(tupleU);\n";
                            if(boundIndexes.size()) {
                                    *out << --ind << "}\n";
                            }
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }

                        if (!appearsBefore) {
                            *out << ind++ << "for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){\n";
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind++ << "if(i<tuples->size()){\n";
                            *out << ind << "tuple" << i << " = tuples->at(i);\n";
                            *out << ind++ << "if(tuplesU != &EMPTY_TUPLES) {\n";
                            *out << ind << "tupleU = NULL;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else {\n";
                            *out << ind << "tuple" << i << " = tuplesU->at(i-tuples->size());\n";
                            *out << ind << "tupleU = tuple" << i << ";\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                        } else {
                            *out << ind++ << "for( unsigned i=0; i< tuples->size() + tuplesU->size() + tupleUInVector.size();i++){\n";
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind++ << "if(i<tuples->size()){\n";
                            *out << ind << "tuple" << i << " = tuples->at(i);\n";
                            *out << ind++ << "if(tuplesU != &EMPTY_TUPLES) {\n";
                            *out << ind << "tupleU = NULL;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else if(i<tuples->size()+tuplesU->size()) {\n";
                            *out << ind << "tuple" << i << " = tuplesU->at(i-tuples->size());\n";
                            *out << ind << "tupleU = tuple" << i << ";\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else {\n";
                            *out << ind << "tuple" << i << " = tupleU;\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                        }
                        closingParenthesis++;
                    }
                }
            } else if(f->containsAggregate()){


            }else{

                aspc::ArithmeticRelation* f = (aspc::ArithmeticRelation*) body[joinOrder[i]];
                if (f-> isBoundedRelation(boundVariables)) {
                    *out << ind++ << "if(" << f->getStringRep() << ") {\n";
                    closingParenthesis++;
                } else {
                    //bounded value assignment
                    *out << ind << "int " << f->getAssignmentStringRep(boundVariables) << ";\n";
                    boundVariables.insert(f->getAssignedVariable(boundVariables));

                }

            }

        }
        if (f->isPositiveLiteral() || (i == 0 && f->isLiteral())) {
            aspc::Literal* l = (aspc::Literal*)f;
            std::unordered_set<std::string> declaredVariables;
            for (unsigned t = 0; t < l->getAriety(); t++) {
                if (l->isVariableTermAt(t) && !boundVariables.count(l->getTermAt(t)) && !declaredVariables.count(l->getTermAt(t))) {
                    *out << ind << "int " << l->getTermAt(t) << " = (*tuple" << i << ")[" << t << "];\n";
                    declaredVariables.insert(l->getTermAt(t));
                }
            }
        }

        if (!r.getFormulas()[joinOrder[i]]->isBoundedLiteral(boundVariables) && !r.getFormulas()[joinOrder[i]]->isBoundedRelation(boundVariables) && r.getFormulas()[joinOrder[i]]->isLiteral() ) {
            r.getFormulas()[joinOrder[i]]->addVariablesToSet(boundVariables);
        }

        if (handleEqualCardsAndConstants(r, i, joinOrder)){
            closingParenthesis++;

        }

    }
    //aggregate evaluation
    // *out<<ind<<"std::cout<<\"Starting aggr eval\"<<std::endl;\n";
    std::string sharedVars;
    for(const aspc::ArithmeticRelationWithAggregate* aggr : aggregates){
        std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr->getFormulaIndex());
        printAggregateTrueIf(identifier,aggr,aggr->getJoinTupleName(),".",true);
        //WARNING it doesn't work with more then one lit
        sharedVars=sharedVariablesMap[identifier];
        // if(aggr->isNegated()){
        //     *out << ind << "std::cout<<undefPlusTrue<<\" count not >= 3\"<<std::endl;\n";
        //     *out << ind << "std::cout<<negativeAggrReason[0][{V,W}].size()<<std::endl;\n";
        // }
        // else{
        //     *out << ind << "std::cout<<trueAggrVars[0][{V,W}].size()+trueNegativeAggrVars[0][{V,W}].size()<<\" count >=2\"<<std::endl;\n";
        //     *out << ind << "std::cout<<positiveAggrReason[0][{V,W}].size()<<std::endl;\n";
        // }
    }

        if(reason){
            std::string aggregates_id;
            std::string aggregates_sign;
            for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
                // if(aggr.isNegated())
                //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                //     *out << ind << "local_reason.insert(local_reason.end(),negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                
                // else
                //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                //     *out << ind << "local_reason.insert(local_reason.end(),positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                // buildReason(identifier,&aggr,false);
                if(aggregates_id!=""){
                    aggregates_id+=",";
                    aggregates_sign+=",";
                }
                aggregates_id+=std::to_string(aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]);
                aggregates_sign += aggr.isNegated() ? "false":"true"; 
            }
            *out << ind << "std::vector<int> aggregates_id({"<<aggregates_id<<"});\n";
            *out << ind << "std::vector<bool> aggregates_sign({"<<aggregates_sign<<"});\n";
            *out << ind << "std::vector<int> bodyReason;\n";


//            *out << ind << "std::cout<<\"Local reason size with aggr: \"<<local_reason.size();\n";
            *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                // *out << ind << "std::cout<<\"Adding starter\"<<std::endl;\n";
                *out << ind << "bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
            *out << --ind <<"}\n";
            for(int j=1;j<joinOrder.size()-aggregates.size();j++){
                if(body[joinOrder[j]]->isLiteral()){
                    const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                    *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                        *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                            if(l->isNegated())
                                *out << ind << "bodyReason.push_back(it->second * -1);\n";
                            else
                                *out << ind << "bodyReason.push_back(it->second);\n";
                            // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                        *out << --ind <<"}\n";
                    *out << --ind <<"}\n";
                }
            }
        }
        *out << ind++ << "if(tupleU == NULL){\n";
            *out << ind << "std::cout<<\"propagation started from literal\"<<std::endl;\n";
            *out << ind << "std::cout<<\"conflict detected on propagator Ending with aggr\"<<std::endl;\n";
            // if(reason){
            //     *out<<ind<<"std::cout<<\"conflict reason\";\n";
            //     *out << ind << "for(int v : reason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
            //     *out << ind << "std::cout<<std::endl;\n";
            // }
            // *out << ind << "propagatedLiteralsAndReasons.insert({-1, std::vector<int>("<<printReason<<")});\n";
            // *out << ind << "std::cout << W <<\" \"<< U <<\" \"<< U <<std::endl;\n";
            // *out << ind << "for(const auto & k : trueAggrVars[0][{U,U,U}]) std::cout<<k[0]<<\" \"<<k[1]<<std::endl;\n";
            
            *out << ind << "propagatedLiterals.push_back(-1);\n";
            if(reason){
                *out << ind << "reasonMapping.addPropagation(-1,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVars<<"});\n";
                // *out << ind << "explainAggrLiteral(-1);\n";
            }

        *out << --ind << "}else{\n";
            *out << ++ind << "const auto & it = tupleToVar.find(*tupleU);\n";
            *out << ind++ << "if(it != tupleToVar.end()) {\n";
                *out << ind << "int sign = tupleUNegated ? -1 : 1;\n";
                // if(reason)
                //     *out << ind << "for(int v : reason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                // *out << ind << "std::cout<<\"External propagation \"<<sign;tupleU->print();std::cout<<std::endl;\n";

                // *out << ind << "propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>("<<printReason<<")}).first->second;\n";
                *out << ind << "propagatedLiterals.push_back(it->second*sign);\n";
                if(reason){
                    *out << ind << "reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVars<<"});\n";
                    // *out << ind << "if(it->second*sign == 6) explainAggrLiteral(6);\n";
                }
            *out << --ind << "}\n";
        *out << --ind << "}\n";
    for(int i=0;i<aggregates.size();i++)
        *out << --ind <<"}\n";

    printAggrEvaluation(aggregates,r.getRuleId(),reason,joinOrder,body,boundVariables,false,r);

    while(closingParenthesis>0){
        *out << --ind << "}\n";
        closingParenthesis--;
    }


    // *out << ind << "std::cout<<\"Out Ending with aggr\"<<std::endl;\n";
}
void CompilationManager::printAggrEvaluation(const std::vector<const aspc::ArithmeticRelationWithAggregate*> aggregates,int rule_id,bool reason,std::vector<unsigned> joinOrder,const std::vector<const aspc::Formula*> body,const std::unordered_set<std::string> boundVariables,bool allTrue,const aspc::Rule& r){
    std::string printReason = reason ? "reason":"";
    if(aggregates.size()>0){
        *out << ind++ << "if(tupleU == NULL){\n";
            int propAggrIndex=aggregates.size()-1;
            while(propAggrIndex>=0){
                *out << ind++ << "{\n";
                    int otherAggrIndex=0;
                    for(const aspc::ArithmeticRelationWithAggregate* other : aggregates){
                        std::string identifier = std::to_string(rule_id)+":"+std::to_string(other->getFormulaIndex());
                        std::string joinTupleName = other->getJoinTupleName();
                        std::string localSharedVars = sharedVariablesMap[identifier];

                        if(otherAggrIndex==propAggrIndex && other->isNegated()){
                            if(other->getAggregate().isSum()){
                                *out << ind << "int undefPlusTrue = actualSum["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}]+possibleSum["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}]+actualNegativeSum["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}]+possibleNegativeSum["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}];\n";
                            }else{
                                *out << ind << "int undefPlusTrue = trueAggrVars["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}].size()+undefAggrVars["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}].size()+trueNegativeAggrVars["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}].size()+undefNegativeAggrVars["<<aggregateToStructure[other->getJoinTupleName()+sharedVariablesMap[identifier]+other->getAggrVarAsString()]<<"][{"<<localSharedVars<<"}].size();\n";
                            }

                        }
                        if(otherAggrIndex!=propAggrIndex){
                            printAggregateTrueIf(identifier,other,other->getJoinTupleName(),".",other->isBoundedRelation(boundVariables));
                        }
                        otherAggrIndex++;
                    }
                    std::string propAggrIdentifier = std::to_string(rule_id)+":"+std::to_string(aggregates[propAggrIndex]->getFormulaIndex());
                    *out << ind <<"bool propagated=false;\n";
                    printCanPropagateIf(propAggrIdentifier,aggregates[propAggrIndex],".",true);
                        if(reason){
                            std::string aggregates_id;
                            std::string aggregates_sign;
                            // *out << ind << "std::vector<int> local_reason;\n";
                            for(const aspc::ArithmeticRelationWithAggregate* aggr : aggregates){
                                std::string identifier = std::to_string(rule_id)+":"+std::to_string(aggr->getFormulaIndex());
                                // if(aggr->isNegated())
                                //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                //     *out << ind << "local_reason.insert(local_reason.end(),negativeAggrReason["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[identifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[identifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";

                                // else
                                //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                //     *out << ind << "local_reason.insert(local_reason.end(),positiveAggrReason["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[identifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[identifier]+aggr->getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                                // buildReason(identifier,aggr,false);
                                if(aggregates_id != ""){
                                    aggregates_id+=",";
                                    aggregates_sign+=",";
                                }
                                aggregates_id+=std::to_string(aggregateToStructure[aggr->getJoinTupleName()+sharedVariablesMap[identifier]+aggr->getAggrVarAsString()]);
                                aggregates_sign += aggr->isNegated() ? "false":"true"; 
                            }
                            *out << ind << "std::vector<int> aggregates_id({"<<aggregates_id<<"});\n";
                            *out << ind << "std::vector<bool> aggregates_sign({"<<aggregates_sign<<"});\n";
                            *out << ind << "std::vector<int> bodyReason;\n";

//                            *out << ind << "std::cout<<\"Local reason size with aggr: \"<<local_reason.size();\n";
                            
                            // *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
                            // *out << ind++ << "if(it!=tupleToVar.end()){\n";
                            //     *out << ind << "reason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
                            // *out << --ind <<"}\n";
                            for(int j=0;j<joinOrder.size()-aggregates.size();j++){
                                if(body[joinOrder[j]]->isLiteral()){
                                    const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                                    *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                                        *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            if(l->isNegated())
                                                *out << ind << "bodyReason.push_back(it->second * -1);\n";
                                            else
                                                *out << ind << "bodyReason.push_back(it->second);\n";
                                            // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                                        *out << --ind <<"}\n";
                                    *out << --ind <<"}\n";
                                }
                            }
                            
                        }
                        propAggr(aggregates[propAggrIndex],propAggrIdentifier,reason,".");
                    *out << --ind << "}\n";
                    if(aggregates[propAggrIndex]->getAggregate().isSum()){
                        *out << ind++ << "if(!propagated){\n";
                    }else{
                        *out << ind++ << "else{\n";
                    }
                        // *out << ind << "std::cout<<\"Ending\"<<std::endl;\n";
                        // if(aggregates[propAggrIndex]->getAggregate().getAggregateLiterals().size()>1)
                        //     propIfMultipleJoin(aggregates[propAggrIndex],propAggrIdentifier,reason,body,joinOrder,r);

                    for(int i=0;i<aggregates.size();i++)
                        *out << --ind << "}\n";
                *out << --ind << "}\n";
                propAggrIndex--;
            }
        *out << --ind << "}\n";
    }
}
void CompilationManager::evaluationStartingFromAggregate(const aspc::Rule & r,std::vector<unsigned> joinOrder,unsigned start){

    const std::vector<const aspc::Formula*>& body = r.getFormulas();

    const aspc::ArithmeticRelationWithAggregate* starter = (aspc::ArithmeticRelationWithAggregate*) body[joinOrder[0]];

    std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(joinOrder[0]);
    std::string joinTupleName = starter->getJoinTupleName();
    bool reason = start != joinOrder.size();
    std::string printReason = reason ? "local_reason":"";
    unsigned closingParenthesis=0;
    std::unordered_set<std::string> boundVariables;

    if(reason){
        *out << ind++ << "if(";
        int aggrLitIndex=0;
        for(const aspc::Literal& aggrLit : starter->getAggregate().getAggregateLiterals()){

            if(aggrLitIndex > 0)
                *out << " || ";
            std::string op = ">";
            if((starter->isNegated() && !aggrLit.isNegated()) || (!starter->isNegated() && aggrLit.isNegated())){
                op = "<";
            }
            if(false)
                *out << "(starter.getPredicateName()== &_" << aggrLit.getPredicateName()<<" && facts[i]"<<op<<"0)";
            else 
                *out << "starter.getPredicateName()== &_" << aggrLit.getPredicateName();

            aggrLitIndex++;
        }

        *out << "){\n";
        closingParenthesis++;


    }
        std::string sharedVars = sharedVariablesMap[aggrIdentifier];

        std::unordered_set<std::string> sharedVarsSet;
        bool boundStarter = starter->isBoundedRelation(boundVariables);
        // *out << ind << "std::cout<<\"Starting From Aggregate\"<<std::endl;\n";
        std::string op = "->";
        //more than 0 shared variable
        if(sharedVars!=""){
            // *out << ind << "std::cout<<\"Shared variables size: \"<<sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<joinOrder[0]<<".size()<<std::endl;\n";
            *out << ind++ << "for(const auto & sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<" : sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<joinOrder[0]<<"){\n";
            // *out << ind << "std::cout<<\"true sharedVars \"<<sharedVarTuple.second->first->size()<<std::endl;\n";
            // *out << ind << "std::cout<<\"undef sharedVars \"<<sharedVarTuple.second->second->size()<<std::endl;\n";
            // *out << ind << "std::cout<<sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<0<<"]<<\" \"<<sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<1<<"]<<\" \"<<sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<2<<"]<<\" \"<<sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<3<<"]<<std::endl;\n";
            // std::unordered_set<std::string> literalOccurances;
            // for(const aspc::Literal& l : starter->getAggregate().getAggregateLiterals()){
            //     literalOccurances.insert(l.getPredicateName());
            // }
            // for(auto & litOccurs : literalOccurances){
            //     bool firstFound=false;
            //     std::cout << "Checking "<<litOccurs<<std::endl;
            //     for(const aspc::Literal& l : starter->getAggregate().getAggregateLiterals()){
            //         if(l.getPredicateName()==litOccurs){
                        
            //             bool boundSharedVars=true;
            //             for(int i:sharedVariablesIndexesMap[aggrIdentifier]){
            //                 if(l.getVariables().count(starter->getTermAt(i))<=0){
            //                     boundSharedVars=false;
            //                     break;
            //                 }
            //             }
            //             if(boundSharedVars){
            //                 for(int j=0;j<l.getAriety();j++){
            //                     std::cout<<l.getTermAt(j)<<" ";
            //                 }
            //                 std::cout<<std::endl;
            //                 if(!firstFound){
            //                     firstFound=true;
            //                     *out << ind++ << "if(starter.getPredicateName() == &_"<<litOccurs<<"){\n";
            //                         *out << ind++ << "if(";
            //                 }else{
            //                     *out << " && ";
            //                 }
            //                 *out << "(";
            //                 int vIndex=0;
            //                 for(int i:sharedVariablesIndexesMap[aggrIdentifier]){
            //                     if(vIndex>0)
            //                         *out << " || ";
            //                     for(int j=0;j<l.getAriety();j++){
            //                         if(starter->getTermAt(i)==l.getTermAt(j)){
            //                             *out << "sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<vIndex<<"] != starter["<<j<<"]";
            //                             break;
            //                         }
            //                     }
            //                     vIndex++;
            //                 }
            //                 *out << ")";
            //             }
            //         }
                    
            //     }
            //     if(firstFound){
            //             *out << "){\n";
            //                 *out << ind << "continue;\n";
            //             *out << --ind << "}\n";
            //         *out << --ind << "}\n"; 
            //     }

            // }
            
            closingParenthesis++;
                int pos = sharedVars.find(',');
                int var=0;
                std::unordered_set<std::string> alreadyDeclared;

                // only one shared variable
                if(sharedVars!="" && pos == std::string::npos){
                    if(!alreadyDeclared.count(sharedVars)){
                        *out << ind << "int " << sharedVars<< " = sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<var<<"];\n";
                        alreadyDeclared.insert(sharedVars);
                    }
                    boundVariables.insert(sharedVars);
                    sharedVarsSet.insert(sharedVars);

                }

                //more than one shared variable
                while(pos!=std::string::npos){
                    if(!alreadyDeclared.count(sharedVars.substr(0,pos))){
                        *out << ind << "int " << sharedVars.substr(0,pos)<< " = sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<var<<"];\n";
                        alreadyDeclared.insert(sharedVars.substr(0,pos));
                    }
                    boundVariables.insert(sharedVars.substr(0,pos));
                    sharedVarsSet.insert(sharedVars.substr(0,pos));
                    sharedVars=sharedVars.substr(pos+1,sharedVars.length());
                    pos = sharedVars.find(',');
                    var++;
                    if(sharedVars!="" && pos == std::string::npos){
                        if(!alreadyDeclared.count(sharedVars)){
                            *out << ind << "int " << sharedVars<< " = sharedVarTuple"<<r.getRuleId()<<"_"<<joinOrder[0]<<"["<<var<<"];\n";
                            alreadyDeclared.insert(sharedVars);
                        }
                        boundVariables.insert(sharedVars);
                        sharedVarsSet.insert(sharedVars);

                    }

                }

        }else{
            //no shared variables
            *out << ind++ << "{\n";
            closingParenthesis++;
            op=".";
        }
        if(boundStarter)
            printAggregateTrueIf(aggrIdentifier,starter,joinTupleName,op,boundStarter);
            // *out << ind << "std::cout << \"Aggr true\"<<std::endl;\n";
        bool propFirst = false;
        bool notPropFirst = true;
        bool multiProp = false;
        while(!propFirst || notPropFirst || !multiProp){
            std::vector<const aspc::ArithmeticRelationWithAggregate* > aggregates;

            *out << ind << "tupleU=NULL;\n";
            for(int i=1;i<body.size();i++){
                const aspc::Formula* f = body[joinOrder[i]];
                if(f->containsAggregate()){
                    aggregates.push_back((const aspc::ArithmeticRelationWithAggregate*)f);
                }else if (i != 0 || start == r.getBodySize()) {
                    //std::cout<<"Evaluating literal"<<boundVariables.count("X")<<std::endl;
                    if (f->isLiteral()) {
                        aspc::Literal* l = (aspc::Literal*)f;
                        if (l->isNegated() || l->isBoundedLiteral(boundVariables)) {
                            if (mode == LAZY_MODE) {
                                std::string negation = "";
                                if (l->isNegated()) {
                                    negation = "!";
                                }
                                *out << ind << "const Tuple * tuple" << i << " = w" << l->getPredicateName() << ".find(Tuple({";
                                printLiteralTuple(l);
                                *out << "},&_"<<l->getPredicateName()<<"));\n";
                                *out << ind++ << "if(" << negation << "tuple" << i << "){\n";
                                closingParenthesis++;
                            } else {
                                //mode == EAGER_MODE
                                bool appearsBefore = literalPredicateAppearsBeforeSameSign(body, joinOrder, i);
                                if(appearsBefore && l->isPositiveLiteral()) {
                                    *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                                    *out << ind++ << "if(tupleU && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<"){\n";
                                    *out << ind << "const Tuple * undefRepeatingTuple = (u" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")));\n";

                                    //  && tupleUNegated added. undefRepeatingTuple have to share also sign
                                    *out << ind++ << "if(tupleU == undefRepeatingTuple && !tupleUNegated){\n";
                                    *out << ind << "tuple" << i << " = undefRepeatingTuple;\n";
                                    *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(!tuple"<<i<<"){\n;";
                                    *out << ind << "tuple" << i << " = (w" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")));\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(!tuple"<<i<<" && !tupleU){\n;";
                                    *out << ind << "tuple" << i << " = tupleU = (u" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")));\n";
                                    *out << ind << "tupleUNegated = false;\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(tuple" << i << "){\n";
                                    closingParenthesis++;
                                }
                                else if(appearsBefore && l->isNegated()) {
                                    *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                                    *out << ind << "const Tuple negativeTuple = Tuple({";
                                    printLiteralTuple(l);
                                    *out << "}, &_" << l->getPredicateName() << ", true);\n";
                                    *out << ind++ << "if(tupleU && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<"){\n;";
                                    *out << ind << "const Tuple * undefRepeatingTuple = (u" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")));\n";
                                    //  && tupleUNegated added. undefRepeatingTuple have to share also sign
                                    *out << ind++ << "if(tupleU == undefRepeatingTuple && tupleUNegated){\n";
                                    *out << ind << "tuple" << i << " = undefRepeatingTuple;\n";
                                    *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(!tuple"<<i<<"){\n;";
                                    *out << ind++ << "if(!(w" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    // // //----------------------------------MODIFIED FOR DEBUGGING----------------------------------
                                    *out << "},&_"<<l->getPredicateName()<<"))) && !(u" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    // // //------------------------------------------------------------------------------------------
                                    *out << "},&_"<<l->getPredicateName()<<")))){\n";
                                    *out << ind << "tuple" << i << " = &negativeTuple;\n";
                                    
                                    // //----------------------------------MODIFIED FOR DEBUGGING----------------------------------
                                    *out << --ind << "}else if(!tupleU && !(w"<<l->getPredicateName()<<".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")))){\n";
                                    *out << ++ind << "tuple"<<i<<" = tupleU = &negativeTuple;\n";
                                    *out << ind << "tupleUNegated=true;\n";
                                    // //------------------------------------------------------------------------------------------

                                    *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(tuple" << i << "){\n";
                                    closingParenthesis++;
                                }
                                else if (l->isNegated()) {
                                    *out << ind << "const Tuple negativeTuple = Tuple({";
                                    printLiteralTuple(l);
                                    *out << "}, &_" << l->getPredicateName() << ", true);\n";
                                    *out << ind << "const Tuple * tuple" << i << " = &negativeTuple;\n";
                                    *out << ind << "bool lTrue = (w" << l->getPredicateName() << ".find(negativeTuple)!=NULL);\n";
                                    *out << ind << "const Tuple * undefTuple = u" << l->getPredicateName() << ".find(negativeTuple);\n";
                                    *out << ind++ << "if((!lTrue && undefTuple == NULL) || (undefTuple && tupleU == NULL)){\n";
                                    *out << ind++ << "if(undefTuple){\n";
                                    *out << ind << "tuple" << i << " = tupleU = undefTuple;\n";
                                    // *out << ind << "tupleU->print();\n";
                                    *out << ind << "tupleUNegated = true;\n";
                                    *out << --ind << "}\n";
                                    closingParenthesis++;

                                } else {
                                    *out << ind << "const Tuple * tuple" << i << " = (w" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")));\n";
                                    *out << ind++ << "if(!tuple" << i << " && !tupleU ){\n";
                                    *out << ind << "tuple" << i << " = tupleU = (u" << l->getPredicateName() << ".find(Tuple({";
                                    printLiteralTuple(l);
                                    *out << "},&_"<<l->getPredicateName()<<")));\n";
                                    //------------------------------DEBUGGING------------------------------
                                    *out << ind << "tupleUNegated = false;\n";
                                    //---------------------------------------------------------------------
                                    *out << --ind << "}\n";
                                    // *out << ind << "tupleUNegated = false;\n";
                                    *out << ind++ << "if(tuple" << i << "){\n";
                                    closingParenthesis++;
                                }
                            }

                        } else {
                            std::string mapVariableName = l->getPredicateName() + "_";
                            for (unsigned t = 0; t < l->getAriety(); t++) {
                                if ((l->isVariableTermAt(t) && boundVariables.count(l->getTermAt(t))) || !l->isVariableTermAt(t)) {
                                    mapVariableName += std::to_string(t) + "_";
                                }
                            }
                            if (mode == LAZY_MODE) {
                                *out << ind << "const std::vector<const Tuple* >& tuples = p" << mapVariableName << ".getValues({";
                                printLiteralTuple(l, boundVariables);
                                *out << "});\n";
                                *out << ind++ << "for( unsigned i=0; i< tuples.size();i++){\n";
                                *out << ind << "const Tuple * tuple" << i << " = tuples[i];\n";
                                closingParenthesis++;
                            } else {
                                //mode == EAGER_MODE
                                *out << ind << "const std::vector<const Tuple* >* tuples;\n";
                                *out << ind << "tuples = &p" << mapVariableName << ".getValues({";
                                printLiteralTuple(l, boundVariables);
                                *out << "});\n";
                                *out << ind << "const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;\n";
                                bool appearsBefore = literalPredicateAppearsBeforeSameSign(body, joinOrder, i);
                                if (appearsBefore) {
                                    *out << ind << "std::vector<const Tuple* > tupleUInVector;\n";
                                }
                                *out << ind++ << "if(tupleU == NULL){\n";
                                *out << ind << "tuplesU = &u" << mapVariableName << ".getValues({";
                                printLiteralTuple(l, boundVariables);
                                *out << "});\n";
                                *out << --ind << "}\n";
                                //repeating literal case

                                if (appearsBefore) {
                                    *out << ind++ << "else {\n";
                                    //handle constants and equal cards?
                                    *out << ind++ << "if(tupleU && !tupleUNegated && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<") {\n";
                                    //check that bound variables have proper value
                                    vector<unsigned> boundIndexes;
                                    for(unsigned v = 0; v < l->getAriety(); v++) {
                                        if(boundVariables.count(l->getTermAt(v))) {
                                            boundIndexes.push_back(v);
                                        }
                                    }
                                    if(boundIndexes.size()) {
                                        *out << ind++ << "if(";
                                            for(unsigned bi = 0; bi < boundIndexes.size(); bi++) {
                                                if(bi > 0) {
                                                    *out << " && ";
                                                }
                                                *out << "tupleU->at(" << boundIndexes[bi] << ") == " << l->getTermAt(boundIndexes[bi]);
                                            }
                                            *out << "){\n";
                                    }

                                    *out << ind << "tupleUInVector.push_back(tupleU);\n";
                                    if(boundIndexes.size()) {
                                            *out << --ind << "}\n";
                                    }
                                    *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                }

                                if (!appearsBefore) {
                                    *out << ind++ << "for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){\n";
                                    *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                                    *out << ind++ << "if(i<tuples->size()){\n";
                                    *out << ind << "tuple" << i << " = tuples->at(i);\n";
                                    *out << ind++ << "if(tuplesU != &EMPTY_TUPLES) {\n";
                                    *out << ind << "tupleU = NULL;\n";
                                    *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "else {\n";
                                    *out << ind << "tuple" << i << " = tuplesU->at(i-tuples->size());\n";
                                    *out << ind << "tupleU = tuple" << i << ";\n";
                                    *out << ind << "tupleUNegated = false;\n";
                                    *out << --ind << "}\n";
                                } else {
                                    *out << ind++ << "for( unsigned i=0; i< tuples->size() + tuplesU->size() + tupleUInVector.size();i++){\n";
                                    *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                                    *out << ind++ << "if(i<tuples->size()){\n";
                                    *out << ind << "tuple" << i << " = tuples->at(i);\n";
                                    *out << ind++ << "if(tuplesU != &EMPTY_TUPLES) {\n";
                                    *out << ind << "tupleU = NULL;\n";
                                    *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "else if(i<tuples->size()+tuplesU->size()) {\n";
                                    *out << ind << "tuple" << i << " = tuplesU->at(i-tuples->size());\n";
                                    *out << ind << "tupleU = tuple" << i << ";\n";
                                    *out << ind << "tupleUNegated = false;\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "else {\n";
                                    *out << ind << "tuple" << i << " = tupleU;\n";
                                    *out << ind << "tupleUNegated = false;\n";
                                    *out << --ind << "}\n";
                                }
                                closingParenthesis++;
                            }
                        }
                    } else if(f->containsAggregate()){


                    }else{

                        aspc::ArithmeticRelation* f = (aspc::ArithmeticRelation*) body[joinOrder[i]];
                        if (f-> isBoundedRelation(boundVariables)) {
                            *out << ind++ << "if(" << f->getStringRep() << ") {\n";
                            closingParenthesis++;
                        } else {
                            //bounded value assignment
                            *out << ind << "int " << f->getAssignmentStringRep(boundVariables) << ";\n";
                            boundVariables.insert(f->getAssignedVariable(boundVariables));

                        }

                    }

                }
                if (f->isPositiveLiteral() || (i == 0 && f->isLiteral())) {
                    aspc::Literal* l = (aspc::Literal*)f;
                    std::unordered_set<std::string> declaredVariables;
                    for (unsigned t = 0; t < l->getAriety(); t++) {
                        if (l->isVariableTermAt(t) && !boundVariables.count(l->getTermAt(t)) && !declaredVariables.count(l->getTermAt(t))) {
                            *out << ind << "int " << l->getTermAt(t) << " = (*tuple" << i << ")[" << t << "];\n";
                            declaredVariables.insert(l->getTermAt(t));
                        }
                    }
                }

                if (!r.getFormulas()[joinOrder[i]]->isBoundedLiteral(boundVariables) && !r.getFormulas()[joinOrder[i]]->isBoundedRelation(boundVariables) && r.getFormulas()[joinOrder[i]]->isLiteral() ) {
                    r.getFormulas()[joinOrder[i]]->addVariablesToSet(boundVariables);
                }

                if (handleEqualCardsAndConstants(r, i, joinOrder))
                    closingParenthesis++;
            }
            for(const aspc::ArithmeticRelationWithAggregate* aggr : aggregates){
                std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr->getFormulaIndex());
                printAggregateTrueIf(identifier,aggr,aggr->getJoinTupleName(),".",true);
            }
            if(!boundStarter){
                printAggregateTrueIf(aggrIdentifier,starter,joinTupleName,op,true);
                
                    // if(starter->isNegated())
                    //     *out << ind << "std::cout << undefPlusTrue << \" Starting True\" << std::endl;\n";
                    // else
                    //     *out << ind << "std::cout << trueAggrVars["<<starter->getJoinTupleName()<<sharedVariablesMap[aggrIdentifier]<<"\"][{"<<sharedVariablesMap[aggrIdentifier]<<"}]+size()<<\" Starting true <<std::endl;\n";
                    string aggregates_id;
                    string aggregates_sign;
                    
                    if(reason){
                        // *out << ind << "std::vector<int> local_reason;\n";
                        for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                            std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
                        //     if(aggr.isNegated())
                        //         // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                        //         *out << ind << "local_reason.insert(local_reason.end(),negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                            
                        //     else
                        //         // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                        //         *out << ind << "local_reason.insert(local_reason.end(),positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                        //     // buildReason(identifier,&aggr,false);
                        //     if(aggregates_id != ""){
                        //         aggregates_id+=",";
                        //     }
                            if(aggregates_id != ""){
                                aggregates_id+=",";
                                aggregates_sign+=",";
                            }
                            aggregates_id += std::to_string(aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]);
                            aggregates_sign += aggr.isNegated() ? "false" : "true";
                            
                        }
                        *out << ind << "std::vector<int> aggregates_id({"<<aggregates_id<<"});\n";
                        *out << ind << "std::vector<bool> aggregates_sign({"<<aggregates_sign<<"});\n";
                        *out << ind << "std::vector<int> bodyReason;\n";
                        //*out << ind << "std::cout<<\"Local reason size with aggr: \"<<local_reason.size();\n";
                        *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                            // *out << ind << "std::cout<<\"Adding starter\"<<std::endl;\n";
                            *out << ind << "bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
                        *out << --ind <<"}\n";
                        for(int j=1;j<joinOrder.size()-aggregates.size();j++){
                            if(body[joinOrder[j]]->isLiteral()){
                                const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                                *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                                    *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                        if(l->isNegated())
                                            *out << ind << "bodyReason.push_back(it->second * -1);\n";
                                        else
                                            *out << ind << "bodyReason.push_back(it->second);\n";
                                        // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                                    *out << --ind <<"}\n";
                                *out << --ind <<"}\n";
                            }
                        }
                    }    
                    *out << ind++ << "if(tupleU == NULL){\n";
                        *out << ind << "std::cout<<\"propagation started from Aggr\"<<std::endl;\n";
                        *out << ind << "std::cout<<\"conflict detected on propagator Ending with aggr\"<<std::endl;\n";
                        // if(reason){
                        //     *out<<ind<<"std::cout<<\"propagation reason\";\n";
                        //     *out << ind << "for(int v : reason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                        //     *out << ind << "std::cout<<std::endl;\n";
                        // }
                        *out << ind << "propagatedLiterals.push_back(-1);\n";
                        if(reason){
                            *out << ind << "reasonMapping.addPropagation(-1,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariablesMap[aggrIdentifier]<<"});\n";
                            
                        }
                        // *out << ind << "propagatedLiteralsAndReasons.insert({-1, std::vector<int>("<<printReason<<")});\n";
                    *out << --ind << "}else{\n";
                        *out << ++ind << "const auto & it = tupleToVar.find(*tupleU);\n";
                        *out << ind++ << "if(it != tupleToVar.end()) {\n";
                            *out << ind << "int sign = tupleUNegated ? -1 : 1;\n";
                            // if(reason)
                            //     *out << ind << "for(int v : reason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                            // *out << ind << "std::cout<<\"External propagation \"<<sign;tupleU->print();std::cout<<std::endl;\n";
                            // *out << ind << "propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>("<<printReason<<")}).first->second;\n";
                            *out << ind << "propagatedLiterals.push_back(it->second*sign);\n";
                            if(reason){
                                *out << ind << "reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariablesMap[aggrIdentifier]<<"});\n";
                            }
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                    // *out << ind << "std::cout<<\"End aggr true\"<<std::endl;\n";

                *out << --ind << "}else{\n";
                    ind++;
                    // if(starter->isNegated())
                    //     *out << ind << "std::cout << undefPlusTrue << \" Starting not true\" << std::endl;\n";
                    // else
                    //     *out << ind << "std::cout << actualSum["<<starter->getJoinTupleName()<<sharedVariablesMap[aggrIdentifier]<<"\"][{"<<sharedVariablesMap[aggrIdentifier]<<"}]<<\" Starting not true <<std::endl;\n";
                    *out << ind << "bool propagated=false;\n";

                    printCanPropagateIf(aggrIdentifier,starter,".",true);
                        
                        // if(starter->isNegated())
                            // *out << ind << "std::cout<<\"UndefPlusTrue: \"<<undefPlusTrue<<std::endl;\n";
                        *out << ind++ << "if(tupleU == NULL){\n";
                            if(reason){
                                std::string aggregates_id;
                                std::string aggregates_sign;
                                *out << ind << "std::vector<int> local_reason;\n";
                                for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                                    std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
                                    // if(aggr.isNegated())
                                    //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                    //     *out << ind << "local_reason.insert(local_reason.end(),negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                                    
                                    // else
                                    //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                    //     *out << ind << "local_reason.insert(local_reason.end(),positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                                    // // buildReason(identifier,&aggr,false);
                                    if(aggregates_id != ""){
                                        aggregates_id+=",";
                                        aggregates_sign+=",";
                                    }
                                    aggregates_id += std::to_string(aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]);
                                    aggregates_sign += aggr.isNegated() ? "false" : "true";
                                    
                                }
                                *out << ind << "std::vector<int> aggregates_id({"<<aggregates_id<<"});\n";
                                *out << ind << "std::vector<bool> aggregates_sign({"<<aggregates_sign<<"});\n";
                                *out << ind << "std::vector<int> bodyReason;\n";

                                //*out << ind << "std::cout<<\"Local reason size with aggr: \"<<local_reason.size();\n";
                                *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    *out << ind << "bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
                                *out << --ind <<"}\n";
                                for(int j=1;j<joinOrder.size()-aggregates.size();j++){
                                    if(body[joinOrder[j]]->isLiteral()){
                                        const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                                        *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                                            *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                if(l->isNegated())
                                                    *out << ind << "bodyReason.push_back(it->second * -1);\n";
                                                else
                                                    *out << ind << "bodyReason.push_back(it->second);\n";
                                                // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                                            *out << --ind <<"}\n";
                                        *out << --ind <<"}\n";
                                    }
                                }
                        
                            }
                            // *out << ind << "std::cout<<\"prop not tupleU\"<<std::endl;\n";
                            propAggr(starter,aggrIdentifier,reason,".");
                            // *out << ind << "std::cout<<\" end prop\"<<std::endl;\n";

                        *out << --ind <<"}\n";
                    *out << --ind << "}\n";
                    *out << ind++ << "if(tupleU == NULL && !propagated){\n";
                        // *out << ind << "std::cout<<\"Starting\"<<std::endl;\n";
                        // if(starter->getAggregate().getAggregateLiterals().size()>1)
                        //     propIfMultipleJoin(starter,aggrIdentifier,reason,body,joinOrder,r);
                    *out << --ind <<"}\n";
                *out << --ind << "}\n";

                for(int i=0;i<aggregates.size();i++)
                    *out << --ind <<"}\n";

                while(closingParenthesis>2){
                    *out << --ind <<"}\n";
                    closingParenthesis--;
                }
                *out << ind << "//nested join closed\n";
                notPropFirst=false;
                propFirst=true;
                multiProp=true;

            }else if(notPropFirst){
                if(reason){
                    *out << ind << "std::vector<int> local_reason;\n";
                    std::string aggregates_id;
                    std::string aggregates_sign;
                    for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                        std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
                        // if(aggr.isNegated())
                        //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                        //     *out << ind << "local_reason.insert(local_reason.end(),negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                        
                        // else
                        //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                        //     *out << ind << "local_reason.insert(local_reason.end(),positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                        // buildReason(identifier,&aggr,false);
                            if(aggregates_id != ""){
                                aggregates_id+=",";
                                aggregates_sign+=",";
                            }
                            aggregates_id += std::to_string(aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]);
                            aggregates_sign += aggr.isNegated() ? "false" : "true";
                            
                            
                    }
                    *out << ind << "std::vector<int> aggregates_id({"<<aggregates_id<<"});\n";
                    *out << ind << "std::vector<bool> aggregates_sign({"<<aggregates_sign<<"});\n";
                    *out << ind << "std::vector<int> bodyReason;\n";

//            *out << ind << "std::cout<<\"Local reason size with aggr: \"<<local_reason.size();\n";
                    *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                        // *out << ind << "std::cout<<\"Adding starter\"<<std::endl;\n";
                        *out << ind << "bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
                    *out << --ind <<"}\n";
                    for(int j=1;j<joinOrder.size()-aggregates.size();j++){
                        if(body[joinOrder[j]]->isLiteral()){
                            const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                            *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                                *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    if(l->isNegated())
                                        *out << ind << "bodyReason.push_back(it->second * -1);\n";
                                    else
                                        *out << ind << "bodyReason.push_back(it->second);\n";
                                    // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                                *out << --ind <<"}\n";
                            *out << --ind <<"}\n";
                        }
                    }
                }
                    *out << ind++ << "if(tupleU == NULL){\n";
                        *out << ind << "std::cout<<\"propagation started from Aggr\"<<std::endl;\n";
                        *out << ind << "std::cout<<\"conflict detected on propagator Ending with aggr\"<<std::endl;\n";
                        // if(reason){
                        //     *out<<ind<<"std::cout<<\"propagation reason\";\n";
                        //     *out << ind << "for(int v : reason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                        //     *out << ind << "std::cout<<std::endl;\n";
                        // }
                        // *out << ind << "propagatedLiteralsAndReasons.insert({-1, std::vector<int>("<<printReason<<")});\n";
                        // *out << ind << "std::cout << W <<\" \"<< U <<\" \"<< U <<std::endl;\n";
                        // *out << ind << "for(const auto & k : trueAggrVars[0][{U,U,U}]) std::cout<<k[0]<<\" \"<<k[1]<<std::endl;\n";
                        // *out << ind << "std::cout << \" Negative \" <<std::endl;\n";
                        // *out << ind << "for(const auto & k : trueNegativeAggrVars[0][{U,U,U}]) std::cout<<k[0]<<\" \"<<k[1]<<std::endl;\n";
                        // *out << ind << "std::cout<<\"BodyReason: \"<<bodyReason.size()<<std::endl;\n";
                        *out << ind << "propagatedLiterals.push_back(-1);\n";
                        if(reason){
                            *out << ind << "reasonMapping.addPropagation(-1,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariablesMap[aggrIdentifier]<<"});\n";
                            // *out << ind << "explainAggrLiteral(-1);\n";
                            // *out << ind << "reasonMapping.print();\n";
                        }

                    *out << --ind << "}else{\n";
                        *out << ++ind << "const auto & it = tupleToVar.find(*tupleU);\n";
                        *out << ind++ << "if(it != tupleToVar.end()) {\n";
                            *out << ind << "int sign = tupleUNegated ? -1 : 1;\n";
                            // if(reason)
                            //     *out << ind << "for(int v : reason) {if (v < 0){ std::cout<<\"-\"; v*=-1;}atomsTable[v].print();}\n";
                            // *out << ind << "std::cout << W <<\" \"<< U <<\" \"<< U <<std::endl;\n";
                        
                            // *out << ind << "std::cout<<\"External propagation \"<<sign;tupleU->print();std::cout<<std::endl;\n";
                            // *out << ind << "propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>("<<printReason<<")}).first->second;\n";
                            *out << ind << "propagatedLiterals.push_back(it->second*sign);\n";
                            if(reason){
                                *out << ind << "reasonMapping.addPropagation(it->second*sign,aggregates_id,aggregates_sign,currentReasonLevel,bodyReason,{"<<sharedVariablesMap[aggrIdentifier]<<"});\n";
                            }
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";

                for(int i=0;i<aggregates.size();i++)
                    *out << --ind <<"}\n";

                while(closingParenthesis>2){
                    *out << --ind <<"}\n";
                    closingParenthesis--;
                }

                *out << --ind <<"}//close aggr true if\n";
                boundVariables.clear();
                for(std::string v :sharedVarsSet){
                    boundVariables.insert(v);
                }
                if(!starter->getAggregate().isSum()){
                    printCanPropagateIf(aggrIdentifier,starter,".",boundStarter);
                    
                }else{
                    *out << ind++ << "else{\n";
                    
                }
                *out << ind << "bool propagated=false;\n";

                notPropFirst=false;

            }else if(!propFirst){
                    // *out << ind << "std::cout<<\"Starting prop\"<<std::endl;\n";
                    // *out << ind << "tuple1->print();starter.print();std::cout<<std::endl;\n";

                    // *out << ind << "std::cout << \"Aggr can prop\"<<std::endl;\n";
                    *out << ind++ << "if(tupleU == NULL){\n";
                        // *out << ind << "std::cout<<\"not tupleU\"<<std::endl;\n";
                        if(reason){
                            std::string aggregates_id;
                            std::string aggregates_sign;
                            *out << ind << "std::vector<int> local_reason;\n";
                            for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
                                std::string identifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
                                // if(aggr.isNegated()){
                                //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                //     // *out << ind << "negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].print();\n";
                                //     *out << ind << "local_reason.insert(local_reason.end(),negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), negativeAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                                // }
                                // else
                                //     // *out << ind << "std::set<int> aggrReason"<<aggr.getFormulaIndex()<<"(positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]]<<"][{"<<sharedVariablesMap[identifier]<<"}]);\n";
                                //     *out << ind << "local_reason.insert(local_reason.end(),positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].begin(), positiveAggrReason["<<aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]<<"][{"<<sharedVariablesMap[identifier]<<"}].end());\n";
                                // buildReason(identifier,&aggr,false);
                                if(aggregates_id != ""){
                                    aggregates_id+=",";
                                    aggregates_sign+=",";
                                }
                                aggregates_id += std::to_string(aggregateToStructure[aggr.getJoinTupleName()+sharedVariablesMap[identifier]+aggr.getAggrVarAsString()]);
                                aggregates_sign += aggr.isNegated() ? "false" : "true";
                                    
                            }
                            *out << ind << "std::vector<int> aggregates_id({"<<aggregates_id<<"});\n";
                            *out << ind << "std::vector<bool> aggregates_sign({"<<aggregates_sign<<"});\n";
                            *out << ind << "std::vector<int> bodyReason;\n";

                            // *out << ind << "std::cout<<\"Local reason size with aggr: \"<<local_reason.size();\n";
                            *out << ind << "const auto & it = tupleToVar.find(Tuple(starter));\n";
                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                // *out << ind << "std::cout<<\"Adding starter\"<<std::endl;\n";
                                *out << ind << "bodyReason.push_back(it->second * (starter.isNegated() ? -1:1));\n";
                            *out << --ind <<"}\n";
                            for(int j=1;j<joinOrder.size()-aggregates.size();j++){
                                if(body[joinOrder[j]]->isLiteral()){
                                    const aspc::Literal* l = (aspc::Literal*)body[joinOrder[j]];
                                    *out << ind++ << "if(tuple"<<j<<"!=tupleU){\n";
                                        *out << ind << "const auto & it = tupleToVar.find(Tuple(*tuple"<<j<<"));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            if(l->isNegated())
                                                *out << ind << "bodyReason.push_back(it->second * -1);\n";
                                            else
                                                *out << ind << "bodyReason.push_back(it->second);\n";
                                            // *out << ind << "tuple"<<j<<"->print();std::cout<<\"Added to reason "<<j<<"\"<<std::endl;\n";
                                        *out << --ind <<"}\n";
                                    *out << --ind <<"}\n";
                                }
                            }
                        }
                        propAggr(starter,aggrIdentifier,reason,".");
                    *out << --ind <<"}\n";

                for(int i=0;i<aggregates.size();i++)
                    *out << --ind <<"}\n";

                while(closingParenthesis>2){
                    *out << --ind <<"}\n";
                    closingParenthesis--;
                }
                *out << --ind <<"}//close can prop if\n";
                // if(starter->getAggregate().getAggregateLiterals().size()>1){
                //     if(!starter->getAggregate().isSum())
                //     *out << ind++ << "else{\n";
                //     else
                //         *out << ind++ << "if(!propagated){\n";

                // }else{
                //     multiProp=true;
                // }
                multiProp=true;
                boundVariables.clear();
                for(std::string v :sharedVarsSet){
                    boundVariables.insert(v);
                }
                propFirst=true;
            }else{
                *out << ind++ << "if(tupleU == NULL){\n";
                    // // *out << ind << "std::cout<<\"Starting\"<<std::endl;\n";
                    // propIfMultipleJoin(starter,aggrIdentifier,reason,body,joinOrder,r);
                *out << --ind <<"}\n";

                for(int i=0;i<aggregates.size();i++)
                    *out << --ind <<"}\n";
                while(closingParenthesis>2){
                    *out << --ind <<"}\n";
                    closingParenthesis--;
                }
                *out << --ind <<"}//close prop multi join\n";
                multiProp=true;
            }
        }
        while(closingParenthesis>0){
            *out << --ind <<"}\n";
            closingParenthesis--;
        }

}
void CompilationManager::compileConstraintWithAggregate(const aspc::Rule & r, unsigned start, const aspc::Program & p){

    std::vector<unsigned> joinOrder = r.getOrderedBodyIndexesByStarter(start);
    std::unordered_set<std::string> boundVariables;

    if(r.getFormulas()[joinOrder[0]]->containsAggregate()){
        evaluationStartingFromAggregate(r,joinOrder,start);
    }else{
        evaluationEndingWithAggregate(r,joinOrder,start);
    }
}

void CompilationManager::compileRule(const aspc::Rule & r, unsigned start, const aspc::Program & p) {

    //Iterate over starting workingset
    std::vector<unsigned> joinOrder = r.getOrderedBodyIndexesByStarter(start);
    const std::vector<const aspc::Formula*>& body = r.getFormulas();
    unsigned closingParenthesis = 0;
    std::unordered_set<std::string> boundVariables;


    //join loops, for each body formula
    for (unsigned i = 0; i < body.size(); i++) {
        const aspc::Formula* f = body[joinOrder[i]];
        if (i != 0 || start == r.getBodySize()) {
            if (f->isLiteral()) {
                aspc::Literal* l = (aspc::Literal*)f;
                if (l->isNegated() || l->isBoundedLiteral(boundVariables)) {

                    if (mode == LAZY_MODE) {
                        std::string negation = "";
                        if (l->isNegated()) {
                            negation = "!";
                        }
                        *out << ind << "const Tuple * tuple" << i << " = w" << l->getPredicateName() << ".find({";
                        printLiteralTuple(l);
                        *out << "});\n";
                        *out << ind++ << "if(" << negation << "tuple" << i << "){\n";
                        closingParenthesis++;
                    } else {
                        //mode == EAGER_MODE
                        bool appearsBefore = literalPredicateAppearsBeforeSameSign(body, joinOrder, i);
                        if(appearsBefore && l->isPositiveLiteral()) {
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind++ << "if(tupleU && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<"){\n;";
                            *out << ind << "const Tuple * undefRepeatingTuple = (u" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}));\n";
                            *out << ind++ << "if(tupleU == undefRepeatingTuple){\n";
                            *out << ind << "tuple" << i << " = undefRepeatingTuple;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(!tuple"<<i<<"){\n;";
                            *out << ind << "tuple" << i << " = (w" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}));\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(!tuple"<<i<<" && !tupleU){\n;";
                            *out << ind << "tuple" << i << " = tupleU = (u" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}));\n";
                            *out << --ind << "}\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << ind++ << "if(tuple" << i << "){\n";
                            closingParenthesis++;
                        }
                        else if(appearsBefore && l->isNegated()) {
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind << "const Tuple negativeTuple = Tuple({";
                            printLiteralTuple(l);
                            *out << "}, &_" << l->getPredicateName() << ", true);\n";
                            *out << ind++ << "if(tupleU && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<"){\n;";
                            *out << ind << "const Tuple * undefRepeatingTuple = (u" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}));\n";
                            *out << ind++ << "if(tupleU == undefRepeatingTuple){\n";
                            *out << ind << "tuple" << i << " = undefRepeatingTuple;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(!tuple"<<i<<"){\n;";
                            *out << ind++ << "if(!(w" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}))){\n";
                            *out << ind << "tuple" << i << " = &negativeTuple;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(tuple" << i << "){\n";
                            closingParenthesis++;
                        }
                        else if (l->isNegated()) {
                            *out << ind << "const Tuple negativeTuple = Tuple({";
                            printLiteralTuple(l);
                            *out << "}, &_" << l->getPredicateName() << ", true);\n";
                            *out << ind << "const Tuple * tuple" << i << " = &negativeTuple;\n";
                            *out << ind << "bool lTrue = (w" << l->getPredicateName() << ".find(negativeTuple)!=NULL);\n";
                            *out << ind << "const Tuple * undefTuple = u" << l->getPredicateName() << ".find(negativeTuple);\n";
                            *out << ind++ << "if((!lTrue && undefTuple == NULL) || (undefTuple && tupleU == NULL)){\n";
                            *out << ind++ << "if(undefTuple){\n";
                            *out << ind << "tuple" << i << " = tupleU = undefTuple;\n";
                            *out << ind << "tupleUNegated = true;\n";
                            *out << --ind << "}\n";
                            closingParenthesis++;

                        } else {
                            *out << ind << "const Tuple * tuple" << i << " = (w" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}));\n";
                            *out << ind++ << "if(!tuple" << i << " && !tupleU ){\n";
                            *out << ind << "tuple" << i << " = tupleU = (u" << l->getPredicateName() << ".find({";
                            printLiteralTuple(l);
                            *out << "}));\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(tuple" << i << "){\n";
                            closingParenthesis++;
                        }
                    }

                } else {
                    std::string mapVariableName = l->getPredicateName() + "_";
                    for (unsigned t = 0; t < l->getAriety(); t++) {
                        if ((l->isVariableTermAt(t) && boundVariables.count(l->getTermAt(t))) || !l->isVariableTermAt(t)) {
                            mapVariableName += std::to_string(t) + "_";
                        }
                    }
                    if (mode == LAZY_MODE) {
                        *out << ind << "const std::vector<const Tuple* >& tuples = p" << mapVariableName << ".getValues({";
                        printLiteralTuple(l, boundVariables);
                        *out << "});\n";
                        *out << ind++ << "for( unsigned i=0; i< tuples.size();i++){\n";
                        *out << ind << "const Tuple * tuple" << i << " = tuples[i];\n";
                        closingParenthesis++;
                    } else {
                        //mode == EAGER_MODE
                        *out << ind << "const std::vector<const Tuple* >* tuples;\n";
                        *out << ind << "tuples = &p" << mapVariableName << ".getValues({";
                        printLiteralTuple(l, boundVariables);
                        *out << "});\n";
                        *out << ind << "const std::vector<const Tuple* >* tuplesU = &EMPTY_TUPLES;\n";
                        bool appearsBefore = literalPredicateAppearsBeforeSameSign(body, joinOrder, i);
                        if (appearsBefore) {
                            *out << ind << "std::vector<const Tuple* > tupleUInVector;\n";
                        }
                        *out << ind++ << "if(tupleU == NULL){\n";
                        *out << ind << "tuplesU = &u" << mapVariableName << ".getValues({";
                        printLiteralTuple(l, boundVariables);
                        *out << "});\n";
                        *out << --ind << "}\n";
                        //repeating literal case

                        if (appearsBefore) {
                            *out << ind++ << "else {\n";
                            //handle constants and equal cards?
                            *out << ind++ << "if(tupleU && !tupleUNegated && tupleU->getPredicateName() == &_"<<l->getPredicateName()<<") {\n";
                            //check that bound variables have proper value
                            vector<unsigned> boundIndexes;
                            for(unsigned v = 0; v < l->getAriety(); v++) {
                                if(boundVariables.count(l->getTermAt(v))) {
                                    boundIndexes.push_back(v);
                                }
                            }
                            if(boundIndexes.size()) {
                                *out << ind++ << "if(";
                                 for(unsigned bi = 0; bi < boundIndexes.size(); bi++) {
                                     if(bi > 0) {
                                         *out << " && ";
                                     }
                                     *out << "tupleU->at(" << boundIndexes[bi] << ") == " << l->getTermAt(boundIndexes[bi]);
                                 }
                                 *out << "){\n";
                            }

                            *out << ind << "tupleUInVector.push_back(tupleU);\n";
                            if(boundIndexes.size()) {
                                 *out << --ind << "}\n";
                            }
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }

                        if (!appearsBefore) {
                            *out << ind++ << "for( unsigned i=0; i< tuples->size() + tuplesU->size();i++){\n";
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind++ << "if(i<tuples->size()){\n";
                            *out << ind << "tuple" << i << " = tuples->at(i);\n";
                            *out << ind++ << "if(tuplesU != &EMPTY_TUPLES) {\n";
                            *out << ind << "tupleU = NULL;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else {\n";
                            *out << ind << "tuple" << i << " = tuplesU->at(i-tuples->size());\n";
                            *out << ind << "tupleU = tuple" << i << ";\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                        } else {
                            *out << ind++ << "for( unsigned i=0; i< tuples->size() + tuplesU->size() + tupleUInVector.size();i++){\n";
                            *out << ind << "const Tuple * tuple" << i << " = NULL;\n";
                            *out << ind++ << "if(i<tuples->size()){\n";
                            *out << ind << "tuple" << i << " = tuples->at(i);\n";
                            *out << ind++ << "if(tuplesU != &EMPTY_TUPLES) {\n";
                            *out << ind << "tupleU = NULL;\n";
                            *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else if(i<tuples->size()+tuplesU->size()) {\n";
                            *out << ind << "tuple" << i << " = tuplesU->at(i-tuples->size());\n";
                            *out << ind << "tupleU = tuple" << i << ";\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "else {\n";
                            *out << ind << "tuple" << i << " = tupleU;\n";
                            *out << ind << "tupleUNegated = false;\n";
                            *out << --ind << "}\n";
                        }
                        closingParenthesis++;
                    }
                }
            } else {
                aspc::ArithmeticRelation* f = (aspc::ArithmeticRelation*) body[joinOrder[i]];
                if (f-> isBoundedRelation(boundVariables)) {
                    *out << ind++ << "if(" << f->getStringRep() << ") {\n";
                    closingParenthesis++;
                } else {
                    //bounded value assignment
                    *out << ind << "int " << f->getAssignmentStringRep(boundVariables) << ";\n";
                    boundVariables.insert(f->getAssignedVariable(boundVariables));

                }

            }

        }
        if (f->isPositiveLiteral() || (i == 0 && f->isLiteral())) {
            aspc::Literal* l = (aspc::Literal*)f;
            std::unordered_set<std::string> declaredVariables;
            for (unsigned t = 0; t < l->getAriety(); t++) {
                if (l->isVariableTermAt(t) && !boundVariables.count(l->getTermAt(t)) && !declaredVariables.count(l->getTermAt(t))) {
                    *out << ind << "int " << l->getTermAt(t) << " = (*tuple" << i << ")[" << t << "];\n";
                    declaredVariables.insert(l->getTermAt(t));
                }
            }
        }
        if (!r.getFormulas()[joinOrder[i]]->isBoundedLiteral(boundVariables) && !r.getFormulas()[joinOrder[i]]->isBoundedRelation(boundVariables)) {
            r.getFormulas()[joinOrder[i]]->addVariablesToSet(boundVariables);
        }

        if (handleEqualCardsAndConstants(r, i, joinOrder))
            closingParenthesis++;

        //rule fires
        if (i == body.size() - 1) {

            if (!r.isConstraint()) {

                //a rule is firing
                string tupleType = "TupleWithoutReasons";
                if (p.hasConstraint()) {
                    tupleType = "TupleWithReasons";
                }
                *out << ind << "const auto & insertResult = w" << r.getHead().front().getPredicateName() << ".insert(" << tupleType << "({";

                for (unsigned th = 0; th < r.getHead().front().getTermsSize(); th++) {
                    if (!r.getHead().front().isVariableTermAt(th)) {
                        if (isInteger(r.getHead().front().getTermAt(th))) {
                            *out << r.getHead().front().getTermAt(th);
                        } else {
                            *out << "ConstantsManager::getInstance().mapConstant(\"" << escapeDoubleQuotes(r.getHead().front().getTermAt(th)) << "\")";
                        }
                    } else {
                        *out << r.getHead().front().getTermAt(th);
                    }
                    if (th < r.getHead().front().getTermsSize() - 1) {
                        *out << ",";
                    }
                }


                *out << "}, &_" << r.getHead().front().getPredicateName() << "));\n";
                *out << ind++ << "if(insertResult.second){\n";

                if (p.hasConstraint()) {
                    for (unsigned i = 0; i < body.size(); i++) {
                        if (body[joinOrder[i]]->isPositiveLiteral()) {
                            *out << ind << "insertResult.first->addPositiveReason(tuple" << i << ");\n";
                        } else if (body[joinOrder[i]]->isLiteral()) {
                            aspc::Literal* l = (aspc::Literal*) body[joinOrder[i]];
                            *out << ind << "insertResult.first->addNegativeReason(Tuple({";
                            printLiteralTuple(l);
                            *out << "}, &_" << l->getPredicateName() << ", true));\n";
                        }
                    }
                }

                for (const std::string& auxMapName : predicateToAuxiliaryMaps[r.getHead().front().getPredicateName()]) {
                    *out << ind << "p" << auxMapName << ".insert2(*w" << r.getHead().front().getPredicateName() << ".getTuples().back());\n";
                }

                *out << --ind << "}\n";
            } else {
                //*out << ind << "std::cout<<\"constraint failed\"<<std::endl;\n";
                //we are handling a constraint
                if (mode == LAZY_MODE) {
                    *out << ind << "failedConstraints.push_back(std::vector<aspc::Literal>());\n";

                    *out << ind << "std::vector<const Tuple *> reasons;\n";

                    for (unsigned i = 0; i < body.size(); i++) {
                        if (body[joinOrder[i]]->isLiteral()) {
                            aspc::Literal* l = (aspc::Literal*) body[joinOrder[i]];
                            if (idbs.count(l->getPredicateName()) || headPredicates.count(l->getPredicateName())) {
                                *out << ind << "std::unordered_set<std::string> open_set" << i << ";\n";
                                if (l->isPositiveLiteral()) {
                                    *out << ind << "explainPositiveLiteral(tuple" << i << ", open_set" << i << ", reasons);\n";
                                } else {
                                    *out << ind << "Tuple tuple" << i << " = Tuple({";
                                    printLiteralTuple(l);
                                    *out << "}, &_" << l->getPredicateName() << ", true);\n";
                                    *out << ind << "explainNegativeLiteral(&tuple" << i << ", open_set" << i << ", reasons);\n";
                                    //*out << ind << "failedConstraints.back().push_back(tupleToLiteral(Tuple({";
                                    //writeNegativeTuple(r, joinOrder, start, i);
                                    //*out << "}, 0, &ConstantsManager::getInstance().getPredicateName(\"" << l->getPredicateName() << "\"), true)));\n";
                                }
                            }
                        }
                    }
                    *out << ind++ << "for(const Tuple * reason: reasons) {\n";
                    *out << ind << "failedConstraints.back().push_back(tupleToLiteral(*reason));\n";
                    *out << --ind << "}\n";
                } else {
                    //mode == EAGER_MODE
                    //*out << ind << "aspc::Literal propagatedLiteral = (tupleToLiteral(*tupleU));\n";
                    //*out << ind << "propagatedLiteral.setNegated(tupleUNegated);\n";
                    //TODO maybe negate literal
                    //*out << ind << "propagatedLiteral.print();\n";
                    *out << ind << "int sign = tupleUNegated ? -1 : 1;\n";

                    //needed for propagations at level 0.. constraint may fail, then return incoherence (value 1)
                    *out << ind++ << "if(!tupleU) {\n";
                    *out << ind << "std::cout<<\"conflict detected in propagator\"<<std::endl;\n";
                    *out << ind << "propagatedLiteralsAndReasons.insert({-1, std::vector<int>()});\n";
                    *out << --ind << "}\n";

                    *out << ind++ << "else {\n";
                    *out << ind << "const auto & it = tupleToVar.find(*tupleU);\n";
#ifdef EAGER_DEBUG
                    *out << ind << "std::cout<<\"propagating \";\n";
                    *out << ind << "std::cout<<(-1 * sign* ((int) (it->second)))<<\" \";\n";
                    *out << ind++ << "if(sign > 0) {\n";
                    *out << ind << "std::cout<<\"not \";\n";
                    *out << --ind << "}\n";
                    *out << ind << "tupleU->print();\n";
                    *out << ind << "std::cout<<\"\\n\";\n";
#endif
                    *out << ind++ << "if(it != tupleToVar.end()) {\n";
                    *out << ind << "auto & reas = propagatedLiteralsAndReasons.insert({it->second*sign, std::vector<int>()}).first->second;\n";
                    //*out << ind << "propagatedLiteralsAndReasons[tupleToVar[*tupleU]] = std::vector<int>();\n";
                    //*out << ind << "std::cout<<\"constraint failed\"<<std::endl;\n";

                    //*out << ind << "reasonsForPropagatedLiterals.push_back(std::vector<aspc::Literal>());\n";

                    *out << ind << "std::vector<const Tuple *> reasons;\n";

                    for (unsigned i = 0; i < body.size(); i++) {
                        if (body[joinOrder[i]]->isLiteral()) {
                            aspc::Literal* l = (aspc::Literal*) body[joinOrder[i]];
                            //if (idbs.count(l->getPredicateName()) || headPredicates.count(l->getPredicateName())) {
                            *out << ind++ << "if(tuple" << i << " != tupleU){\n";
                            *out << ind << "std::unordered_set<std::string> open_set" << i << ";\n";
#ifdef EAGER_DEBUG
                            *out << ind << "tuple" << i << "->print();\n";
                            *out << ind << "std::cout<<\"\\n\";\n";
#endif
                            if (l->isPositiveLiteral()) {
                                //*out << ind << "reasons.push_back(tuple" << i << ");\n";
                                *out << ind << "explainPositiveLiteral(tuple" << i << ", open_set" << i << ", reasons);\n";

                            } else {
                                //                                *out << ind << "Tuple tuple" << i << " = Tuple({";
                                //                                printLiteralTuple(l);
                                //                                *out << "}, &_" << l->getPredicateName() << ", true);\n";
                                *out << ind << "reasons.push_back(tuple" << i << ");\n";
                                //*out << ind << "explainNegativeLiteral(tuple" << i << ", open_set" << i << ", reasons);\n";
                            }
                            *out << --ind << "}\n";
                            //}
                        }
                    }
                    *out << ind << "reas.reserve(reasons.size());\n";
                    *out << ind++ << "for(const Tuple * reason: reasons) {\n";
                    *out << ind << "const auto & it = tupleToVar.find(*reason);\n";
                    *out << ind++ << "if(it != tupleToVar.end()) {\n";
                    *out << ind << "reas.push_back(it->second * (reason->isNegated()? -1:1));\n";
                    *out << --ind << "}\n";
                    *out << --ind << "}\n";
                    //*out << ind++ << "if(decisionLevel == -1) {\n";
                    //*out << ind << "executeProgramOnFacts({-1,it->second*sign*-1});\n";
                    //*out << --ind << "}\n";
                    *out << --ind << "}\n";
                    *out << --ind << "}\n";


                }
                //TESTING FEATURE, LIMIT NUMBER OF FAILED CONSTRAINTS
                //                *out << ind++ << "if(failedConstraints.size() >= 1000) {\n";
                //                *out << ind << "return;\n";
                //                *out << --ind << "}\n";
            }

        }


    }
    for (unsigned i = 0; i < closingParenthesis; i++) {
        *out << --ind << "}//close par\n";
    }

        /*unsigned i = 1;
        if(start == r.getBodySize()) {
            i=0;
        }
        for (unsigned i = 1; i < body.size(); i++) {
            if (body[i]->isLiteral()) {
         *out << --ind << "}//close lit\n";
            }
        }*/
    //}


}

void CompilationManager::printLiteralTuple(const aspc::Literal* l, const std::vector<bool> & coveredMask) {

    bool first = true;
    for (unsigned term = 0; term < l->getAriety(); term++) {
        if (!l->isVariableTermAt(term) || coveredMask[term]) {
            if (!first) {
                *out << ", ";
            }
            if (!l->isVariableTermAt(term) && !isInteger(l->getTermAt(term))) {
                *out << "ConstantsManager::getInstance().mapConstant(\"" << escapeDoubleQuotes(l->getTermAt(term)) << "\")";
            } else {
                *out << l->getTermAt(term);
            }
            first = false;
        }
    }

}

void CompilationManager::printLiteralTuple(const aspc::Literal* l) {
    for (unsigned t = 0; t < l->getAriety(); t++) {
        if (t > 0) {
            *out << ", ";
        }
        if (!l->isVariableTermAt(t) && !isInteger(l->getTermAt(t))) {
            *out << "ConstantsManager::getInstance().mapConstant(\"" << escapeDoubleQuotes(l->getTermAt(t)) << "\")";
        } else {
            *out << l->getTermAt(t);
        }
    }


}

void CompilationManager::printLiteralTuple(const aspc::Literal* l, const std::unordered_set<std::string> & boundVariables) {
    bool first = true;
    for (unsigned t = 0; t < l->getAriety(); t++) {
        if (!l->isVariableTermAt(t) || boundVariables.count(l->getTermAt(t))) {
            if (!first) {
                *out << ", ";
            }
            if (!l->isVariableTermAt(t) && !isInteger(l->getTermAt(t))) {
                *out << "ConstantsManager::getInstance().mapConstant(\"" << escapeDoubleQuotes(l->getTermAt(t)) << "\")";
            } else {
                *out << l->getTermAt(t);
            }
            first = false;
        }
    }


}

void initRuleBoundVariablesAux(std::unordered_set<std::string> & output, const aspc::Literal & lit, const std::unordered_set<std::string> & litBoundVariables, const aspc::Atom & head) {
    for (unsigned i = 0; i < lit.getAriety(); i++) {
        if (litBoundVariables.count(lit.getTermAt(i))) {
            output.insert(head.getTermAt(i));
        }
    }
}

void CompilationManager::declareDataStructuresForReasonsOfNegative(const aspc::Program & program, const aspc::Literal & lit, std::unordered_set<std::string> & boundVariables, std::unordered_set<std::string> & openSet) {


    std::string canonicalRep = lit.getCanonicalRepresentation(boundVariables);
    if (openSet.count(canonicalRep)) {
        return;
    }

    if (lit.isNegated() && modelGeneratorPredicates.count(lit.getPredicateName())) {
        modelGeneratorPredicatesInNegativeReasons.insert(lit.getPredicateName());
        predicateArieties.insert(std::make_pair(lit.getPredicateName(), lit.getAriety()));
    }

    openSet.insert(canonicalRep);

    for (const aspc::Rule & r : program.getRules()) {
        if (!r.isConstraint() && lit.unifies(r.getHead()[0])) {
            std::unordered_set<std::string> ruleBoundVariables;
            const aspc::Atom & head = r.getHead()[0];
            initRuleBoundVariablesAux(ruleBoundVariables, lit, boundVariables, head);
            std::vector<const aspc::Formula*> orderedFormulas = r.getOrderedBodyForReasons(ruleBoundVariables);
            for (unsigned i = 0; i < r.getBodySize(); i++) {
                const aspc::Formula * f = orderedFormulas[i];
                if (f -> isLiteral()) {
                    const aspc::Literal * bodyLit = (const aspc::Literal *) f;
                    if (lit.isNegated()) {
                        if (!bodyLit->isNegated()) {
                            std::vector<unsigned> coveredVariableIndexes;
                            bodyLit->getAtom().getCoveredVariables(ruleBoundVariables, coveredVariableIndexes);
                            if (coveredVariableIndexes.size() < bodyLit->getAriety()) {
                                std::string mapVariableName = bodyLit->getPredicateName() + "_";
                                for (unsigned index : coveredVariableIndexes) {
                                    mapVariableName += std::to_string(index) + "_";
                                }
                                if (!declaredMaps.count(mapVariableName)) {
                                    *out << ind << "AuxMap p" << mapVariableName << "({";
                                    for (unsigned k = 0; k < coveredVariableIndexes.size(); k++) {
                                        if (k > 0) {
                                            *out << ",";
                                        }
                                        *out << coveredVariableIndexes[k];
                                    }
                                    *out << "});\n";
                                    predicateToAuxiliaryMaps[bodyLit->getPredicateName()].insert(mapVariableName);
                                    //                                    *out << ind << "predicateToAuxiliaryMaps[" << bodyLit->getPredicateName() << "].push_back(&p" << mapVariableName << ");\n";
                                    //*out << ind << "std::string " << mapVariableName << ";\n";
                                    declaredMaps.insert(mapVariableName);
                                }
                                mapVariableName = "false_p" + mapVariableName;
                                if (!declaredMaps.count(mapVariableName) && modelGeneratorPredicates.count(bodyLit -> getPredicateName())) {
                                    *out << ind << "AuxMap " << mapVariableName << "({";
                                    for (unsigned k = 0; k < coveredVariableIndexes.size(); k++) {
                                        if (k > 0) {
                                            *out << ",";
                                        }
                                        *out << coveredVariableIndexes[k];
                                    }
                                    *out << "});\n";
                                    predicateToFalseAuxiliaryMaps[bodyLit->getPredicateName()].insert(mapVariableName);
                                    declaredMaps.insert(mapVariableName);
                                }

                            }
                            aspc::Literal temp = *bodyLit;
                            temp.setNegated(true);
                            declareDataStructuresForReasonsOfNegative(program, temp, ruleBoundVariables, openSet);
                        } else {
                            aspc::Literal temp = *bodyLit;
                            temp.setNegated(false);
                            declareDataStructuresForReasonsOfNegative(program, temp, ruleBoundVariables, openSet);
                        }
                    } else if (!modelGeneratorPredicates.count(bodyLit -> getPredicateName()) || bodyLit->isNegated()) {
                        std::unordered_set<std::string> bodyLitVariables = bodyLit->getVariables();
                        declareDataStructuresForReasonsOfNegative(program, *bodyLit, bodyLitVariables, openSet);
                    }
                    for (unsigned t = 0; t < bodyLit->getAriety(); t++) {
                        if (bodyLit -> isVariableTermAt(t)) {
                            ruleBoundVariables.insert(bodyLit->getTermAt(t));
                        }
                    }
                }
            }
        }
    }
}

void CompilationManager::declareDataStructuresForReasonsOfNegative(const aspc::Program & program) {

    *out << ind << "//printing aux maps needed for reasons of negative literals;\n";
    std::unordered_set<std::string> open_set;

    for (const aspc::Rule & r : program.getRules()) {
        if (r.isConstraint()) {
            for (const aspc::Formula * f : r.getFormulas()) {
                if (f->isLiteral()) {
                    const aspc::Literal & lit = (const aspc::Literal &) * f;
                    std::unordered_set<std::string> litVariables = lit.getVariables();
                    declareDataStructuresForReasonsOfNegative(program, lit, litVariables, open_set);
                }
            }
        }
    }
}

bool CompilationManager::handleEqualCardsAndConstants(const aspc::Rule& r, unsigned i, const std::vector<unsigned>& joinOrder) {

    if (!r.getFormulas()[joinOrder[i]]->isLiteral()) {
        return false;
    }

    bool hasCondition = false;
    const aspc::Literal * l = (aspc::Literal *) r.getFormulas()[joinOrder[i]];
    if (l->isNegated() && i != 0) {
        return false;
    }
    for (unsigned t1 = 0; t1 < l->getAriety(); t1++) {
        if (!l->isVariableTermAt(t1)) {
            if (!hasCondition) {
                *out << ind++ << "if( ";
                hasCondition = true;
            } else
                *out << " && ";

            *out << "(*tuple" << i << ")[" << t1 << "] == ";
            if (isInteger(l->getTermAt(t1))) {
                *out << l->getTermAt(t1);
            } else {
                *out << "ConstantsManager::getInstance().mapConstant(\"" << escapeDoubleQuotes(l->getTermAt(t1)) << "\")";
            }

        }
        for (unsigned t2 = t1 + 1; t2 < l->getAriety(); t2++)
            if (l->isVariableTermAt(t1) && l->getTermAt(t1) == l->getTermAt(t2)) {
                if (!hasCondition) {
                    *out << ind++ << "if( ";
                    hasCondition = true;
                } else
                    *out << " && ";
                *out << "(*tuple" << i << ")[" << t1 << "] == (*tuple" << i << ")[" << t2 << "]";
            }
    }
    if (hasCondition)
        *out << "){\n";
    return hasCondition;
}
const std::set<std::string>& CompilationManager::getBodyPredicates() {
    return bodyPredicates;
}