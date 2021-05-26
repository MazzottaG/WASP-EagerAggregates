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

    // COMMENTED FOR INCOMPATIBILITIES
    // *out << ind++ << "void createFunctionsMap() {\n";
    // for (const auto & entry : functionsMap) {
    //     *out << ind << "explainNegativeFunctionsMap[&_" << entry.first << "] = " << entry.second << ";\n";
    // }
    // *out << --ind << "}\n";
}
// void CompilationManager::checkExistsShareVariableMap(int ruleId, int aggrIndex,std::string& sharedVariables,bool create){

//     //*out << ind << "std::cout<<\"check exists shared value tuple\"<<std::endl;\n";

//     int countVar=0;
//     std::string indexesToString="";
//     for(unsigned varIndex : aggregateVariablesIndex[std::to_string(ruleId)+":"+std::to_string(aggrIndex)]){
//         indexesToString+=std::to_string(varIndex);
//         if(countVar < aggregateVariablesIndex[std::to_string(ruleId)+":"+std::to_string(aggrIndex)].size()-1)
//             indexesToString+=",";
//         countVar++;
//     }

//     if(create){
//         *out << ind++ << "if(!sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariables<<"})){\n";
//             *out << ind << "sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".insert({"<<sharedVariables<<"});\n";
//     }else{
//         *out << ind++ << "if(sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariables<<"})!=0){\n";
//     }
// }
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
bool CompilationManager::checkTupleFormat(const aspc::Literal& li,std::string tupleName,bool tuplePointer){
    std::string point = tuplePointer ? "->":".";
    std::string conditions;
    for(unsigned i = 0; i < li.getAriety(); i++){
        if(!li.isVariableTermAt(i)){
            if(conditions!="")
                conditions+=" && ";
            conditions+=tupleName+point+"at("+std::to_string(i)+")=="+li.getTermAt(i);
        }else{
            for(unsigned j = i+1; j < li.getAriety(); j++){
                if(li.isVariableTermAt(j) && li.getTermAt(i) == li.getTermAt(j)){
                    if(conditions!="")
                        conditions+=" && ";
                    conditions+=tupleName+point+"at("+std::to_string(i)+")=="+tupleName+point+"at("+std::to_string(j)+")";
                }
            }
        }
    }
    if(conditions!=""){
        *out << ind++ << "if("<<conditions<<"){\n";
        return true;
    }
    return false;

    // std::string point = tuplePointer ? "->":".";
    // bool checkVariablesEquals=false;
    // for(unsigned i=0;i<li.getAriety();i++){
    //     for(unsigned j=i+1;j<li.getAriety();j++){
    //         if(li.isVariableTermAt(i) && li.isVariableTermAt(j) && li.getTermAt(i)==li.getTermAt(j)){
    //             if(!checkVariablesEquals){
    //                 *out << ind++ << "if(tuple"<<buildIndex<<point<<"at("<<i<<") == tuple"<<buildIndex<<point<<"at("<<j<<")";
    //                 checkVariablesEquals=true;
    //             }else
    //                 *out << "&& tuple"<<buildIndex<<point<<"at("<<i<<") == tuple"<<buildIndex<<point<<"at("<<j<<")";
    //         }
    //     }
    //     if(!li.isVariableTermAt(i)){
    //         std::string mapStringConstant = !isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);

    //         if(!checkVariablesEquals){
    //             *out << ind++ << "if(tuple"<<buildIndex<<point<<"at("<<i<<") == "<<mapStringConstant;
    //             checkVariablesEquals=true;
    //         }else{
    //             *out << "&& tuple"<<buildIndex<<point<<"at("<<i<<") == "<<mapStringConstant;
    //         }
    //     }
    // }
    // if(checkVariablesEquals){
    //     *out << "){\n";
    // }

    // return checkVariablesEquals;
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
        // if(createFalseAuxMap){
            *out << ind << "AuxMap f" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";
        // }
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
// void CompilationManager::updateUndefinedSharedVariablesMap(const aspc::Rule& r,int startLit){

//     std::unordered_set<std::string> boundVars;
//     printVars(r.getBodyLiterals()[startLit],"tuple.",boundVars);
//     // *out << ind << "tuple.print();\n";
//     // *out << ind << "std::cout<<\"updatesharedvariables\"<<std::endl;\n";
//     r.getBodyLiterals()[startLit].addVariablesToSet(boundVars);
//     bool checkFormat = checkTupleFormat(r.getBodyLiterals()[startLit],"",false);
//     int closingParenthesis = checkFormat ? 1:0;
//     const std::vector<unsigned> & joinOrder = r.getOrderedBodyIndexesByStarter(startLit);

//     for(unsigned i=0;i<joinOrder.size();i++){
//         const aspc::Formula* f =r.getFormulas()[joinOrder[i]];

//         if(joinOrder[i] !=startLit && !f->containsAggregate()){
//             if(f->isBoundedRelation(boundVars)){
//                 *out << ind << "if("<< ((const aspc::ArithmeticRelation*)f)->getStringRep()<<"){\n";
//                 closingParenthesis++;
//             }else if(f->isBoundedValueAssignment(boundVars)){
//                 *out << ind << "int " << ((const aspc::ArithmeticRelation*)f)->getAssignmentStringRep(boundVars) << ";\n";
//                 f->addVariablesToSet(boundVars);
//             }else if(!f->isBoundedLiteral(boundVars)){
//                 const aspc::Literal* l = (const aspc::Literal*)f;
//                 std::string mapVariableName = l->getPredicateName() + "_";
//                 for (unsigned tiIndex = 0; tiIndex < l->getAriety(); tiIndex++) {
//                     if ((l->isVariableTermAt(tiIndex) && boundVars.count(l->getTermAt(tiIndex))) || !l->isVariableTermAt(tiIndex)) {
//                         mapVariableName += std::to_string(tiIndex) + "_";
//                     }
//                 }
//                 *out << ind << "const std::vector<const Tuple *>& undefTuples"<<i<<" = u"<<mapVariableName<<".getValues({";
//                 printLiteralTuple(l,boundVars);
//                 *out << "});\n";
//                 *out << ind << "const std::vector<const Tuple*>& trueTuples"<<i<<" = p"<<mapVariableName<<".getValues({";
//                 printLiteralTuple(l,boundVars);
//                 *out << "});\n";
//                 *out << ind++ << "for(int i=0;i<undefTuples"<<i<<".size()+trueTuples"<<i<<".size();i++){\n";
//                 *out << ind << "const Tuple * tuple"<<i<<";\n";

//                 *out << ind++ << "if(i<undefTuples"<<i<<".size())\n";
//                 *out << ind << "tuple"<<i<<" = undefTuples"<<i<<"[i];\n";
//                 *out << --ind << "else tuple"<<i<<" = trueTuples"<<i<<"[i-undefTuples"<<i<<".size()];\n";

//                 closingParenthesis++;
//                 printVars(*l,"tuple"+std::to_string(i)+"->",boundVars);
//                 l->addVariablesToSet(boundVars);
//                 if(checkTupleFormat(*l,std::to_string(i),true))
//                     closingParenthesis++;
//             }
//         }
//     }

    //join partendos dal letterale startLit costruito

//     for(const aspc::ArithmeticRelationWithAggregate& ar: r.getArithmeticRelationsWithAggregate()){
//         //vedo le variabili condivise tra i letterali del corpo ed ogni aggregato della regola
//         std::string key(std::to_string(r.getRuleId())+":"+std::to_string(ar.getFormulaIndex()));


//         std::string sharedVarsIndexesToString="";
//         for(unsigned varIndex : sharedVariablesIndexesMap[key]){

//             //salvo gli indici delle variabili di aggregazione
//             sharedVarsIndexesToString+=std::to_string(varIndex)+"_";
//         }

//         std::string sharedVars = sharedVariablesMap[key];
//         if(sharedVars!=""){
//             *out << ind++ << "{\n";
//                 checkExistsShareVariableMap(r.getRuleId(),ar.getFormulaIndex(),sharedVars,true);
//                 *out << --ind << "}\n";
//             *out << --ind << "}\n";
//             //*out << ind << "std::cout<<\"True size: \"<<sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<"[sharedTuple]->first->size()<<std::endl;\n";
//             //*out << ind << "std::cout<<\"Undef size: \"<<sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<"[sharedTuple]->second->size()<<std::endl;\n";

//         }
//     }

//     for(int i=0;i<closingParenthesis;i++){
//         *out << --ind << "}\n";
//     }

//     //comment
//     // *out << ind << "std::cout<<\"saved for all aggregate\"<<std::endl;\n";

// }
// void CompilationManager::declareDataStructureForAggregate(const aspc::Rule& r,const std::set< pair<std::string, unsigned> >& aggregatePredicates){

//     //BUILD AGGREGATE JOIN
//     for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
//         sharedVariablesMapForAggregateBody[aggr.getJoinTupleName()].push_back("sharedVariables_"+std::to_string(r.getRuleId())+"_ToAggregate_"+std::to_string(aggr.getFormulaIndex()));
//         aggrIdentifierForAggregateBody[aggr.getJoinTupleName()].push_back({r.getRuleId(),aggr.getFormulaIndex()});

//         int startingId = 0;
//         for(const aspc::Literal& starter :aggr.getAggregate().getAggregateLiterals()){
//             std::unordered_set<std::string> boundVars;
//             for(int i=0;i<starter.getAriety();i++){
//                 if(starter.isVariableTermAt(i)){
//                     boundVars.insert(starter.getTermAt(i));
//                 }
//             }
//             int liIndex=0;
//             for(const aspc::Literal& li :aggr.getAggregate().getAggregateLiterals()){
//                 std::vector<unsigned> boundIndices;
//                 std::string auxMapName = li.getPredicateName()+"_";
//                 if(liIndex!=startingId){
//                     for(unsigned i=0;i<li.getAriety();i++){
//                         if(!li.isVariableTermAt(i) || boundVars.count(li.getTermAt(i))){
//                             boundIndices.push_back(i);
//                             auxMapName+=std::to_string(i)+"_";
//                         }
//                     }
//                     for(unsigned i=0;i<li.getAriety();i++){
//                         if(li.isVariableTermAt(i))
//                             boundVars.insert(li.getTermAt(i));
//                     }
//                     declareAuxMap(auxMapName,boundIndices,li.getPredicateName(),false,false);
//                 }
//                 liIndex++;
//             }
//             startingId++;
//         }
//     }

//     //Jointuple auxMap
//     for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
//         std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
//         std::vector<unsigned int> sharedVariablesIndex(sharedVariablesIndexesMap[aggrIdentifier]);
//         std::string sharedVarProj;
//         for(unsigned int i : sharedVariablesIndex){
//             sharedVarProj+=std::to_string(i)+"_";
//         }
//         declareAuxMap("_"+aggr.getJoinTupleName()+sharedVarProj,sharedVariablesIndex,aggr.getJoinTupleName(),false,true);
//         std::vector<unsigned int> aggrVarIndex(aggregateVariablesIndex[aggrIdentifier]);
//         std::string aggrVarProj;
//         for(unsigned int i : aggrVarIndex){
//             aggrVarProj+=std::to_string(i)+"_";
//             sharedVariablesIndex.push_back(i);
//         }
//         declareAuxMap("_"+aggr.getJoinTupleName()+aggrVarProj,aggrVarIndex,aggr.getJoinTupleName(),false,true);


//         declareAuxMap("_"+aggr.getJoinTupleName()+sharedVarProj+aggrVarProj,sharedVariablesIndex,aggr.getJoinTupleName(),false,true);
//         int ariety=0;
//         for(const aspc::Literal& li : aggr.getAggregate().getAggregateLiterals()){
//             std::vector<unsigned int> index;
//             std::string proj;
//             for(unsigned int i=0;i<li.getAriety();i++){
//                 proj+=std::to_string(ariety+i)+"_";
//                 index.push_back(ariety+i);
//             }
//             declareAuxMap("_"+aggr.getJoinTupleName()+proj,index,aggr.getJoinTupleName(),false,true);
//             ariety+=li.getAriety();
//         }

//     }

//     int startLit=0;
//     for(const aspc::Literal& starter: r.getBodyLiterals()){
//         for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
//             std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());
//             std::string auxMapName=starter.getPredicateName()+"_";
//             std::vector<unsigned int> boundIndices;
//             for(int i=0;i<starter.getAriety();i++){
//                 if(!starter.isVariableTermAt(i)){
//                     auxMapName+=std::to_string(i)+"_";
//                     boundIndices.push_back(i);
//                 }else{
//                     for(int v:sharedVariablesIndexesMap[aggrIdentifier]){
//                         if(starter.getTermAt(i) == aggr.getTermAt(v)){
//                             auxMapName+=std::to_string(i)+"_";
//                             boundIndices.push_back(i);
//                             break;
//                         }
//                     }
//                 }
//             }
//             declareAuxMap(auxMapName,boundIndices,starter.getPredicateName(),false,false);
//         }
//     }

//     //dichiaro le auxMap che vengono utilizzate per costruire le jointuple
//     // for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){

//     //     std::string joinTupleName=aggr.getJoinTupleName();
//     //     // std::cout<<joinTupleName<<std::endl;
//     //     std::set<string> varAlreadyAdded;
//     //     std::vector<std::vector<unsigned>> aggregateLiteralIndexes;
//     //     int varIndex=0;
//     //     int index=0;
//     //     std::string aggrIdentifier = std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex());

//     //     for(const aspc::Literal& li: aggr.getAggregate().getAggregateLiterals()){

//     //         aggregateLiteralIndexes.push_back(std::vector<unsigned>());

//     //         //creo una mappa per ogni letterale indicizzata su tutte le variabili
//     //         std::string mapIndexedAllVars=li.getPredicateName()+"_";

//     //         std::vector<unsigned> localIndex;
//     //         for (unsigned tiIndex = 0; tiIndex < li.getAriety(); tiIndex++) {

//     //             mapIndexedAllVars+=std::to_string(tiIndex)+"_";
//     //             aggregateLiteralIndexes[index].push_back(varIndex);
//     //             localIndex.push_back(tiIndex);
//     //             varIndex++;

//     //         }

//     //         declareAuxMap(mapIndexedAllVars,localIndex,li.getPredicateName(),true,false);

//     //         //creo una mappa non indicizzata per iniziare il join
//     //         declareAuxMap(li.getPredicateName() + "_",std::vector<unsigned>(),li.getPredicateName(),true,false);

//     //         //creo una mappa per gli altri letterali indicizzata rispetto al letterale corrente
//     //         std::unordered_set<std::string> boundVariables;
//     //         li.addVariablesToSet(boundVariables);
//     //         int buildIndex=0;
//     //         for(const aspc::Literal& li_: aggr.getAggregate().getAggregateLiterals()){
//     //             std::string mapVariableName = li_.getPredicateName() + "_";
//     //             std::vector< unsigned > keyIndexes;
//     //             if(buildIndex != index){
//     //                 for (unsigned tiIndex = 0; tiIndex < li_.getAriety(); tiIndex++) {
//     //                     if ((li_.isVariableTermAt(tiIndex) && boundVariables.count(li_.getTermAt(tiIndex))) || !li_.isVariableTermAt(tiIndex)) {
//     //                         mapVariableName += std::to_string(tiIndex) + "_";
//     //                         keyIndexes.push_back(tiIndex);

//     //                     }
//     //                 }
//     //                 li_.addVariablesToSet(boundVariables);
//     //                 declareAuxMap(mapVariableName,keyIndexes,li_.getPredicateName(),true,false);
//     //             }
//     //             buildIndex++;
//     //         }
//     //         index++;
//     //     }
//     //     sharedVariablesMapForAggregateBody[joinTupleName].push_back("sharedVariables_"+std::to_string(r.getRuleId())+"_ToAggregate_"+std::to_string(aggr.getFormulaIndex()));
//     //     aggrIdentifierForAggregateBody[aggr.getJoinTupleName()].push_back({r.getRuleId(),aggr.getFormulaIndex()});
//     //     /*for(const std::string& v : aggr.getAggregate().getAggregateVariables()){
//     //         int joinTupleIndex=0;
//     //         for(const aspc::Literal& li: aggr.getAggregate().getAggregateLiterals()){
//     //             for (unsigned tiIndex = 0; tiIndex < li.getAriety(); tiIndex++) {

//     //                 if( v == li.getTermAt(tiIndex)){make
//     //                     if(!varAlreadyAdded.count(li.getTermAt(tiIndex))){
//     //                         aggregateVariablesIndex[aggrIdentifier].push_back(joinTupleIndex);
//     //                         varAlreadyAdded.insert(li.getTermAt(tiIndex));
//     //                     }
//     //                 }
//     //                 joinTupleIndex++;
//     //             }
//     //         }
//     //     }*/
//     //     //dichiaro una mappa per le joinTuple indicizzata sulle variabili di aggregazione
//     //     std::string aggregateVarsIndex="";
//     //     for(unsigned index_ : aggregateVariablesIndex[aggrIdentifier]){
//     //         aggregateVarsIndex+=std::to_string(index_)+"_";

//     //     }
//     //     declareAuxMap("_"+joinTupleName+aggregateVarsIndex,aggregateVariablesIndex[aggrIdentifier],joinTupleName,false,true);


//     //     //dichiaro una mappa per le joinTuple non indicizzata
//     //     // declareAuxMap("_"+joinTupleName,std::vector<unsigned>(),joinTupleName,false,true);


//     //     //dichiaro una mappa per le joinTuple indicizzata sulle variabili condivise con il corpo
//     //     std::string sharedVarsIndexToString="";
//     //     for(unsigned index_ : sharedVariablesIndexesMap[aggrIdentifier])
//     //         sharedVarsIndexToString+=std::to_string(index_)+"_";
//     //     std::vector<unsigned> sharedVarsIndex = sharedVariablesIndexesMap[aggrIdentifier];
//     //     declareAuxMap("_"+joinTupleName+sharedVarsIndexToString,sharedVarsIndex,joinTupleName,false,true);

//     //     //mappa indicizzata su aggrVars and sharedVars
//     //     std::vector<unsigned> sharedAndAggrVarIndex(sharedVarsIndex);
//     //     for(unsigned index_ : aggregateVariablesIndex[aggrIdentifier])
//     //         sharedAndAggrVarIndex.push_back(index_);
//     //     declareAuxMap("_"+joinTupleName+sharedVarsIndexToString+aggregateVarsIndex,sharedAndAggrVarIndex,joinTupleName,false,true);

//     //     // int totalAriety=0;
//     //     // for(const aspc::Literal& l : aggr.getAggregate().getAggregateLiterals()){
//     //     //     std::string lit_indeces="";
//     //     //     std::vector<unsigned> total_indeces(sharedVarsIndex);
//     //     //     for(int i=0;i<l.getAriety();i++){
//     //     //         lit_indeces+=std::to_string(i+totalAriety)+"_";
//     //     //         total_indeces.push_back(i+totalAriety);
//     //     //     }
//     //     //     declareAuxMap("_"+joinTupleName+sharedVarsIndexToString+lit_indeces,total_indeces,joinTupleName,false,true);
//     //     //     totalAriety+=l.getAriety();
//     //     // }
//     //     std::string sharedVariables = sharedVariablesMap[aggrIdentifier];

//     //     //dichiaro una mappa per le join tuples indicizzata sull variabili di ogni letterale nell'aggregato
//     //     index=0;
//     //     for(std::vector<unsigned>& indexes : aggregateLiteralIndexes){
//     //         std::string literalTermIndex="";
//     //         for(unsigned var : indexes)
//     //             literalTermIndex = literalTermIndex + std::to_string(var) + "_";
//     //         //salvo per ogni letterale il nome dell'AuxMap delle join tuple indicizzata secondo il letterale
//     //         // aggregateLiteralToAuxiliaryMap[aggr.getAggregate().getAggregateLiterals()[index].getPredicateName()+"_"+std::to_string(index)+"_"+aggrIdentifier]=std::string("_"+joinTupleName+literalTermIndex);
//     //         // aggregateLiteralToPredicateWSet[aggr.getAggregate().getAggregateLiterals()[index].getPredicateName()+"_"+aggrIdentifier]=std::string(joinTupleName);

//     //         declareAuxMap("_"+joinTupleName+literalTermIndex,indexes,joinTupleName,false,true);
//     //         // for(unsigned var :sharedVariablesIndexesMap[aggrIdentifier])
//     //         //     indexes.push_back(var);
//     //         // if(sharedVariables!="")
//     //         //     declareAuxMap("_"+joinTupleName+literalTermIndex+sharedVarsIndexToString,indexes,joinTupleName,false,true);
//     //         // for(unsigned v : aggregateVariablesIndex[aggrIdentifier]){
//     //         //     indexes.push_back(v);
//     //         // }
//     //         // declareAuxMap("_"+joinTupleName+literalTermIndex+sharedVarsIndexToString+aggregateVarsIndex,indexes,joinTupleName,false,true);

//     //         index++;
//     //     }

//     //     if(sharedVariables!=""){

//     //         //dichiaro una mappa per ogni letterale del corpo indicizzata sulle shared variable e costanti
//     //         int literalIndex=0;
//     //         //std::cout<<"Declaring map for external predicates"<<std::endl;
//     //         for(const aspc::Literal& bodyLiteral : r.getBodyLiterals()){
//     //             //std::cout<<"Start from ";
//     //             //bodyLiteral.print();
//     //             //std::cout<<std::endl;

//     //             std::string auxMapName = bodyLiteral.getPredicateName()+"_";
//     //             std::unordered_set<std::string> boundVars;
//     //             std::vector<unsigned> indexes;
//     //             for(int i=0;i<bodyLiteral.getAriety();i++){
//     //                 if(sharedVariables.find(bodyLiteral.getTermAt(i))!=std::string::npos || !bodyLiteral.isVariableTermAt(i)){
//     //                     auxMapName+=std::to_string(i)+"_";
//     //                     indexes.push_back(i);
//     //                 }
//     //                 if(bodyLiteral.isVariableTermAt(i)){
//     //                     boundVars.insert(bodyLiteral.getTermAt(i));
//     //                 }
//     //             }

//     //             bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(bodyLiteral.getPredicateName(),bodyLiteral.getAriety()))!=0;
//     //             declareAuxMap(auxMapName,indexes,bodyLiteral.getPredicateName(),declareFalseAuxMap,false);

//     //             //join dei letterali del corpo considerando le sharedVariables bound
//     //             int bodyLiteralIndex=0;
//     //             for(const aspc::Literal& buildBodyLiteral : r.getBodyLiterals()){
//     //                 if(bodyLiteralIndex!=literalIndex){
//     //                     std::string buildAuxMapName = buildBodyLiteral.getPredicateName()+"_";
//     //                     std::vector<unsigned> buildindexes;

//     //                     for(int i=0;i<buildBodyLiteral.getAriety();i++){
//     //                         if(sharedVariables.find(buildBodyLiteral.getTermAt(i))!=std::string::npos || !buildBodyLiteral.isVariableTermAt(i) || boundVars.count(buildBodyLiteral.getTermAt(i))){
//     //                             buildAuxMapName+=std::to_string(i)+"_";
//     //                             buildindexes.push_back(i);
//     //                         }
//     //                         if(buildBodyLiteral.isVariableTermAt(i)){
//     //                             boundVars.insert(buildBodyLiteral.getTermAt(i));
//     //                         }
//     //                     }
//     //                     bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(buildBodyLiteral.getPredicateName(),buildBodyLiteral.getAriety()))!=0;
//     //                     //std::cout<<"Declare "<<buildAuxMapName<<std::endl;
//     //                     declareAuxMap(buildAuxMapName,buildindexes,buildBodyLiteral.getPredicateName(),declareFalseAuxMap,false);

//     //                 }
//     //                 bodyLiteralIndex++;
//     //             }
//     //             literalIndex++;
//     //         }
//     //         for(const aspc::ArithmeticRelationWithAggregate& aggr : r.getArithmeticRelationsWithAggregate()){
//     //             int literalIndex=0;
//     //             for(const aspc::Literal& aggrLit : aggr.getAggregate().getAggregateLiterals()){
//     //                 std::string auxMapName = aggrLit.getPredicateName()+"_";
//     //                 std::unordered_set<std::string> boundVars;
//     //                 std::vector<unsigned> indexes;
//     //                 for(int i=0;i<aggrLit.getAriety();i++){
//     //                     if(sharedVariables.find(aggrLit.getTermAt(i))!=std::string::npos || !aggrLit.isVariableTermAt(i)){
//     //                         auxMapName+=std::to_string(i)+"_";
//     //                         indexes.push_back(i);
//     //                     }
//     //                     if(aggrLit.isVariableTermAt(i)){
//     //                         boundVars.insert(aggrLit.getTermAt(i));
//     //                     }
//     //                 }

//     //                 bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(aggrLit.getPredicateName(),aggrLit.getAriety()))!=0;
//     //                 declareAuxMap(auxMapName,indexes,aggrLit.getPredicateName(),declareFalseAuxMap,false);

//     //                 //join dei letterali del corpo considerando le sharedVariables bound
//     //                 int bodyLiteralIndex=0;
//     //                 for(const aspc::Literal& buildAggrLiteral : aggr.getAggregate().getAggregateLiterals()){
//     //                     if(bodyLiteralIndex!=literalIndex){
//     //                         std::string buildAuxMapName = buildAggrLiteral.getPredicateName()+"_";
//     //                         std::vector<unsigned> buildindexes;

//     //                         for(int i=0;i<buildAggrLiteral.getAriety();i++){
//     //                             if(sharedVariables.find(buildAggrLiteral.getTermAt(i))!=std::string::npos || !buildAggrLiteral.isVariableTermAt(i) || boundVars.count(buildAggrLiteral.getTermAt(i))){
//     //                                 buildAuxMapName+=std::to_string(i)+"_";
//     //                                 buildindexes.push_back(i);
//     //                             }
//     //                             if(buildAggrLiteral.isVariableTermAt(i)){
//     //                                 boundVars.insert(buildAggrLiteral.getTermAt(i));
//     //                             }
//     //                         }
//     //                         bool declareFalseAuxMap = aggregatePredicates.count(std::pair<std::string,unsigned>(buildAggrLiteral.getPredicateName(),buildAggrLiteral.getAriety()))!=0;
//     //                         //std::cout<<"Declare "<<buildAuxMapName<<std::endl;
//     //                         declareAuxMap(buildAuxMapName,buildindexes,buildAggrLiteral.getPredicateName(),declareFalseAuxMap,false);
//     //                     }
//     //                     bodyLiteralIndex++;
//     //                 }
//     //                 literalIndex++;
//     //             }
//     //         }
//     //     }
//     // }
// }
void CompilationManager::generateStratifiedCompilableProgram(aspc::Program & program, AspCore2ProgramBuilder* builder) {

    std::cout<<"generateStratifiedCompilableProgram"<<std::endl;
    bool programHasConstraint = program.hasConstraint();

    *out << ind << "#include \"Executor.h\"\n\n";
    *out << ind << "#include \"utils/ConstantsManager.h\"\n\n";
    *out << ind << "#include \"DLV2libs/input/InputDirector.h\"\n\n";
    *out << ind << "#include \"parsing/AspCore2InstanceBuilder.h\"\n\n";
    *out << ind << "#include \"datastructures/PredicateSet.h\"\n\n";
    *out << ind << "#include \"datastructures/ReasonTable.h\"\n\n";
    *out << ind << "#include \"datastructures/PostponedReasons.h\"\n\n";

    *out << ind << "#include \"datastructures/DynamicTrie.h\"\n\n";
    *out << ind << "#include \"datastructures/VariablesMapping.h\"\n\n";
    *out << ind << "#include \"datastructures/VarsIndex.h\"\n\n";
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


        // *out << ind << "std::unordered_map<const std::string*, DynamicTrie*> sharedVariables;\n";
        // *out << ind << "std::unordered_map<const std::string*, std::unordered_map<DynamicCompilationVector*,DynamicTrie>*> sharedVarWAggr;\n";
        // *out << ind << "std::unordered_map<const std::string*, std::unordered_map<DynamicCompilationVector*,DynamicTrie>*> sharedVarUAggr;\n";
        // *out << ind << "std::unordered_map<const std::string*, std::unordered_map<DynamicCompilationVector*,DynamicTrie>*> sharedVarFAggr;\n";

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
    if(mode == EAGER_MODE){
        *out << ind << "std::unordered_map<int,int> externalLiteralsLevel;\n";
        *out << ind << "std::unordered_map<int,std::vector<int>> levelToIntLiterals;\n";
        // *out << ind << "std::map<int,std::vector<int>> levelToExtLiterals;\n";
        *out << ind << "std::unordered_map<int,UnorderedSet<int>> reasonForLiteral;\n";
        *out << ind << "int currentDecisionLevel=-1;\n";
        // *out << ind << "std::unordered_map<int,int> supportedLiterals;\n";
        *out << ind << "bool undefinedLoaded=false;\n";
        // for(auto internalPred : program.getHeadPredicates()){
        //     *out << ind << "bool loadUndef"<<internalPred<<"=false;\n";
        // }
    }
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<std::vector<int>>>> trueAggrVars;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<std::vector<int>>>> undefAggrVars;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<int>>> positiveAggrReason;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>,std::set<int>>> negativeAggrReason;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>, unsigned int>> actualSum;\n";
    // *out << ind << "std::unordered_map<std::string,std::map<std::vector<int>, unsigned int>> possibleSum;\n";

    *out << ind << "std::unordered_map<int,int> actualSum;\n";
    *out << ind << "std::unordered_map<int,int> possibleSum;\n";
    
    //REMOVING
    // *out << ind << "std::unordered_set<const std::string*> aggr_setPredicate;\n";
    // *out << ind << "std::unordered_map<const std::string*,std::vector<AuxMap*>> sumAggrIdForAggrSetAuxMap;\n";
    // *out << ind << "std::unordered_map<const std::string*,std::vector<AuxMap*>> sumAggrIdForAggrSetUAuxMap;\n";
    // *out << ind << "std::unordered_map<const std::string*,std::vector<AuxMap*>> sumAggrIdForAggrSetFAuxMap;\n";
    //dichiaro predicateWSet per joinTuple
    std::unordered_set<std::string> declaredJoinTupleSet;

    // for(aspc::Rule & r : program.getRules()){
        // if(r.isConstraint() && r.containsAggregate()){
        //     for(const aspc::ArithmeticRelationWithAggregate& ar : r.getArithmeticRelationsWithAggregate()){

        //         std::string joinTupleName =ar.getJoinTupleName();

        //         //contains variable index inside jointuple
        //         std::vector<pair<std::string,int>> bodyAggregateVars;
        //         std::unordered_set<std::string> vars;
        //         int arity=0;
        //         for(const aspc::Literal& l : ar.getAggregate().getAggregateLiterals()){
        //             for(unsigned i=0;i<l.getAriety();i++){
        //                 if(l.isVariableTermAt(i) && l.getTermAt(i)!="_"){
        //                     bodyAggregateVars.push_back(std::pair<std::string,int>(l.getTermAt(i),arity+i));
        //                     vars.insert(l.getTermAt(i));
        //                 }
        //             }
        //             arity+=l.getAriety();
        //         }
        //         std::vector<pair<std::string,int>> inequalityAggregateVars;
        //         for(const aspc::ArithmeticRelation& inequality : ar.getAggregate().getAggregateInequalities()){
        //             if(inequality.isBoundedValueAssignment(vars)){
        //                 std::string v = inequality.getAssignedVariable(vars);
        //                 inequalityAggregateVars.push_back(std::pair<std::string,int>({v,arity}));
        //                 vars.insert(v);
        //                 arity++;
        //             }
        //         }
        //         for(auto pair : inequalityAggregateVars){
        //             bool found = false;
        //             for(const aspc::Literal& l : r.getBodyLiterals()){
        //                 if(l.getVariables().count(pair.first)!=0){
        //                     found=true;
        //                     break;
        //                 }
        //             }
        //             bodyAggregateVars.push_back(pair);
        //             joinTupleName+=pair.first+"_";
        //         }
        //         //dichiaro le shared variables per l'aggregato formulaIndex e la regola
        //         std::string key(std::to_string(r.getRuleId())+":"+std::to_string(ar.getFormulaIndex()));
        //         std::unordered_set<std::string> sharedVars;
        //         for(std::string v: ar.getAggregate().getAggregateVariables()){
        //             if(isVariable(v)){
        //                 for(auto pair : bodyAggregateVars)
        //                     if(v==pair.first){
        //                         aggregateVariablesIndex[key].push_back(pair.second);
        //                         break;
        //                     }
        //             }else{
        //                 std::cout<<v<<std::endl;
        //             }
        //         }
        //         bool firstVarAdded=false;
        //         for(auto pair : bodyAggregateVars){
        //             bool found=false;
        //             std::unordered_set<std::string> boundVars;
        //             for(const aspc::Literal& l : r.getBodyLiterals()){
        //                 l.addVariablesToSet(boundVars);
        //                 if(l.getVariables().count(pair.first)!=0){
        //                     found=true;
        //                     if (firstVarAdded){
        //                         sharedVariablesMap[key]+=",";
        //                     }
        //                     firstVarAdded=true;
        //                     sharedVariablesMap[key]+=pair.first;
        //                     sharedVariablesIndexesMap[key].push_back(pair.second);
        //                     //variable founded in at least one body literal
        //                     break;
        //                 }
        //             }
        //             if(!found){
        //                 for(const aspc::ArithmeticRelation& inequality : r.getArithmeticRelations()){
        //                     if(inequality.isBoundedValueAssignment(boundVars)){
        //                         if(pair.first == inequality.getAssignedVariable(boundVars)){
        //                             found=true;
        //                             if (firstVarAdded){
        //                                 sharedVariablesMap[key]+=",";
        //                             }
        //                             firstVarAdded=true;
        //                             sharedVariablesMap[key]+=pair.first;
        //                             sharedVariablesIndexesMap[key].push_back(pair.second);
        //                             //variable founded in at least one body literal
        //                             break;
        //                         }
        //                     }
        //                 }
        //             }
        //         }


        //         r.updateJoinTupleName(ar.getFormulaIndex(),joinTupleName);
        //         if(!declaredJoinTupleSet.count(joinTupleName)){
        //             *out << ind << "const std::string _" << joinTupleName << " = \"" << joinTupleName << "\";\n";
        //             *out << ind << "PredicateWSet w"<<joinTupleName<<"("<<arity<<");\n";
        //             *out << ind << "PredicateWSet u"<<joinTupleName<<"("<<arity<<");\n";
        //             *out << ind << "PredicateWSet nw"<<joinTupleName<<"("<<arity<<");\n";
        //             *out << ind << "PredicateWSet nu"<<joinTupleName<<"("<<arity<<");\n";
        //             declaredJoinTupleSet.insert(joinTupleName);
        //         }

        //         aggregateToStructure.insert({joinTupleName+sharedVariablesMap[key]+ar.getAggrVarAsString(),aggregateToStructure.size()});
        //         // std::cout << joinTupleName<<sharedVariablesMap[key]<<ar.getAggrVarAsString()<<" "<<aggregateToStructure[joinTupleName+sharedVariablesMap[key]+ar.getAggrVarAsString()]<<std::endl;
        //         // *out << ind << "std::set<std::vector<int>> sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<";\n";
        //         // *out << ind << "std::map<std::vector<int>, std::pair< AuxMap*,AuxMap*>*> sharedVariables_"<<r.getRuleId()<<"_ToAggregate_"<<ar.getFormulaIndex()<<";\n";
        //     }
        // }
    // }
    // *out << ind << "std::unordered_map < unsigned int, std::set < VarsIndex > > trueAggrVars["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, std::set < VarsIndex > > undefAggrVars["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, std::set < VarsIndex > > trueNegativeAggrVars["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, std::set < VarsIndex > > undefNegativeAggrVars["<<aggregateToStructure.size()<<"];\n";


    // *out << ind << "DynamicTrie aggrVariable["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "DynamicTrie sharedVariable["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "VariablesMapping sharedVariable["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "VariablesMapping aggrVariable["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map < unsigned int, ReasonTable > positiveAggrReason["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, ReasonTable > negativeAggrReason["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map < unsigned int, int > actualSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, int > possibleSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, int > actualNegativeSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map < unsigned int, int > possibleNegativeSum["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map < unsigned int, int > maxPossibleNegativeSum["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueAggrVars["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefAggrVars["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> trueNegativeAggrVars["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>,std::set<std::vector<int>>,TuplesHash> undefNegativeAggrVars["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> positiveAggrReason["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>,ReasonTable,TuplesHash> negativeAggrReason["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> actualSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> possibleSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> actualNegativeSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> possibleNegativeSum["<<aggregateToStructure.size()<<"];\n";

    // *out << ind << "std::unordered_map<std::vector<int>, int,TuplesHash> maxPossibleNegativeSum["<<aggregateToStructure.size()<<"];\n";
    // *out << ind << "int currentReasonLevel=0;\n";
    // *out << ind << "PostponedReasons reasonMapping;\n";
    *out << ind << "bool unRoll=false;\n";

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
    // std::cout<<"sccs size: "<<sccs.size()<<std::endl;
    // for(unsigned int i=0; i<sccs.size(); i++){
    //     std::cout<<"Printing sccs["<<i<<"]"<<std::endl;
    //     for(unsigned int j=0;j<sccs[i].size();j++){
    //         std::cout<<sccs[i][j]<<" ";
    //     }
    //     std::cout<<std::endl;
    // }
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

    std::vector< std::map<std::string, std::vector<unsigned>>> starterToExitRulesByComponent(sccsSize);
    std::vector < std::unordered_map < std::string, std::vector<pair<unsigned, unsigned> > >> starterToRecursiveRulesByComponent(sccsSize);
    std::vector<bool> exitRules(program.getRulesSize(), false);
    const std::unordered_map<std::string, int>& predicateIDs = builder->getPredicateIDsMap();
    // std::cout << "Rules size: "<<program.getRules().size()<<std::endl;
    for(const auto& auxPred : builder->getAuxPredicateBody()){
        std::unordered_set<unsigned> visitedLiterals;
        std::unordered_set<std::string> boundVariables;
        while(visitedLiterals.size() < auxPred.second.size()){
            const aspc::Literal* lit = NULL;
            unsigned litIndex=0;
            for(unsigned k=0;k<auxPred.second.size();k++){
                if(visitedLiterals.count(k)==0){
                    if(auxPred.second[k].isBoundedLiteral(boundVariables)){
                        lit=&auxPred.second[k];
                        litIndex=k;
                    }else if(lit == NULL && auxPred.second[k].isPositiveLiteral()){
                        lit=&auxPred.second[k];
                        litIndex=k;
                    }
                }
            }
            if(lit != NULL)
                visitedLiterals.insert(litIndex);

            if(lit != NULL && !lit->isBoundedLiteral(boundVariables)){
                std::string auxMapName = lit->getPredicateName()+"_";
                std::vector<unsigned> boundIndices;
                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(!lit->isVariableTermAt(k) || boundVariables.count(lit->getTermAt(k))!=0){
                        auxMapName+=std::to_string(k)+"_";
                        boundIndices.push_back(k);
                    }
                }
                // std::cout<<"Declearing map "<<lit->getPredicateName()<<std::endl;

                if (!declaredMaps.count(auxMapName)) {
                    *out << ind << "AuxMap p" << auxMapName << "({";
                    for (unsigned k = 0; k < boundIndices.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << boundIndices[k];
                    }
                    *out << "});\n";

                    //TODO remove duplication
                    *out << ind << "AuxMap u" << auxMapName << "({";
                    for (unsigned k = 0; k < boundIndices.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << boundIndices[k];
                    }
                    *out << "});\n";

                    //TODO remove duplication
                    *out << ind << "AuxMap f" << auxMapName << "({";
                    for (unsigned k = 0; k < boundIndices.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << boundIndices[k];
                    }
                    *out << "});\n";
                    std::string predName = lit->getPredicateName();
                    predicateToAuxiliaryMaps[predName].insert(auxMapName);
                    predicateToUndefAuxiliaryMaps[predName].insert(auxMapName);
                    predicateToFalseAuxiliaryMaps[predName].insert(auxMapName);
                    declaredMaps.insert(auxMapName);
                }
                lit->addVariablesToSet(boundVariables);
            }
        }
    }
    for (aspc::Rule& r : program.getRules()) {
        // std::cout<<std::endl;
        // r.print();
        // std::cout<<std::endl;

        //r is a constraint
        bool exitRule = true;
        unsigned lIndex = 0;
        unsigned headLevel = sccs.size();
        if(mode == EAGER_MODE){
            std::unordered_set<std::string> internal;
            std::unordered_set<std::string> ext;

            // std::cout<<"ordering rule "<<r.getRuleId()<<std::endl;
            // r.print();
            std::vector<unsigned> starters;
            starters.push_back(r.getBodySize());
            for (const aspc::Formula* f : r.getFormulas()) {
                if(f->isLiteral()){
                    const aspc::Literal* l = (aspc::Literal*)f;
                    starters.push_back(lIndex);
                }
                lIndex++;
            }
            if(!r.isConstraint()){
                starters.push_back(lIndex+1);
                headPreds.insert({r.getHead()[0].getPredicateName(),&r});
            }
            declareRuleEagerStructures(r);

            r.bodyReordering(starters);

            for(unsigned starter : starters){
                // std::cout<<"starter "<<starter<<std::endl;
                // r.print();
                if(starter <= r.getBodySize()){
                    declareDataStructures(r,starter,aggregatePredicates);
                }
            }
            // std::cout<<"End body reordering"<<std::endl;
        }
        else if (!r.isConstraint()) {
            if(mode == EAGER_MODE){

            }else{
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

        }
        else if (exitRule || r.isConstraint()) {
            if (mode == LAZY_MODE) {
                r.bodyReordering();
                unsigned starter = r.getStarters()[0];
                aspc::Literal* starterL = (aspc::Literal*) r.getFormulas()[starter];
                starterToExitRulesByComponent[headLevel][starterL->getPredicateName()].push_back(r.getRuleId());

            } else {
                //mode == EAGER

            //     vector<unsigned> starters;
            //     for (unsigned i = 0; i < r.getBodySize(); i++) {

            //         if (r.getFormulas()[i]->isLiteral() || r.getFormulas()[i]->containsAggregate()) {
            //             starters.push_back(i);
            //         }
            //     }
            //     if (r.isConstraint()) {
            //         starters.push_back(r.getBodySize());
            //     }
            //     r.bodyReordering(starters);

            //     for (unsigned i = 0; i < starters.size(); i++) {
            //         unsigned starter = r.getStarters()[i];
            //         if (starter != r.getBodySize()) {
            //             string pred_name;

            //             if(r.getFormulas()[starter]->isLiteral()){
            //                 aspc::Literal* starterL = (aspc::Literal*) r.getFormulas()[starter];
            //                 pred_name=starterL->getPredicateName();
            //             }else if(r.getFormulas()[starter]->containsAggregate()){
            //                 aspc::ArithmeticRelationWithAggregate* starterAggr = (aspc::ArithmeticRelationWithAggregate*) r.getFormulas()[starter];
            //                 pred_name="#"+std::to_string(r.getRuleId())+":"+std::to_string(starter);
            //             }
            //             auto & rules = starterToExitRulesByComponent[headLevel][pred_name];
            //             bool alreadyAdded = false;
            //             for (unsigned rule : rules) {
            //                 alreadyAdded = alreadyAdded | (rule == r.getRuleId());
            //             }
            //             if (!alreadyAdded) {
            //                 rules.push_back(r.getRuleId());
            //             }


            //         }
            //     }

            }
            // exitRules[r.getRuleId()] = true;
        }
        // if(r.containsAggregate()){
        //     declareDataStructureForAggregate(r,aggregatePredicates);
        // }

        // for (unsigned starter : r.getStarters()) {
        // declareDataStructures(r, starter,aggregatePredicates);
        // }

    }

    // std::vector< std::unordered_map<std::string, std::vector<unsigned>>> starterToExitRulesByComponent(sccsSize);
    // declareDataStructuresForReasonsOfNegative(program);
    // std::cout<<"End reordering"<<std::endl;

    for (const std::string & predicate : modelGeneratorPredicatesInNegativeReasons) {
        //*out << ind << "const std::string & "<< predicate.first << " = ConstantsManager::getInstance().getPredicateName("<< predicate.first <<");\n";
        *out << ind << "PredicateWSet neg_w" << predicate << "(" << predicateArieties[predicate] << ");\n";
    }

    // *out << ind++ << "void explainAggrLiteral(int var){\n";
    *out << ind++ << "void Executor::handleConflict(int literal){\n";
        *out << ind++ << "if(currentDecisionLevel == -1){\n";
            *out << ind << "propagatedLiterals.insert(-1);\n";
            *out << ind << "return;\n";
        *out << --ind << "}\n\n";
        *out << ind << "std::unordered_set<int> visitedLiterals;\n";
        *out << ind << "explainExternalLiteral(literal,conflictReason,visitedLiterals);\n";
        *out << ind << "explainExternalLiteral(-literal,conflictReason,visitedLiterals);\n";
        *out << ind << "propagatedLiterals.insert(-1);\n";
        *out << ind << "reasonForLiteral.erase(literal);\n";
        // *out << ind++ << "for(unsigned i =0; i<conflictReason.size();i++){\n";
        //     *out << ind << "Tuple var = conflictReason[i] > 0 ?atomsTable[conflictReason[i]] : atomsTable[-conflictReason[i]];\n";
        //     *out << ind++ << "if(conflictReason[i]<0)\n";
        //         *out << ind-- << "std::cout<<\"~\";\n";
        //     *out << ind << "var.print();\n";
        //     *out << ind << "std::cout<<std::endl;\n";
        // *out << --ind << "}\n";
    *out << --ind << "}\n";

    *out << ind++ << "int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,std::unordered_set<int>& visitedLiteral){\n";
        // *out << ind << "std::unordered_set<int> visitedLiteral;\n";
        *out << ind << "std::vector<int> stack;\n";
        *out << ind << "stack.push_back(var);\n";


        *out << ind++ << "while(!stack.empty()){\n";
            *out << ind << "int lit = stack.back();\n";
            *out << ind << "stack.pop_back();\n";
            // *out << ind << "std::cout<<\"Explaining \"<<lit<<std::endl;\n";
            // *out << ind << "Tuple starter = lit>0 ? atomsTable[lit]:atomsTable[-lit];\n";
            // *out << ind << "starter.print();std::cout<<std::endl;\n";

            *out << ind++ << "for(unsigned i = 0; i<reasonForLiteral[lit].size(); i++){\n";
                *out << ind << "int reasonLiteral=reasonForLiteral[lit][i];\n";
                // *out << ind++ << "if(getExternalLit){\n";
                //     *out << ind++ << "if(externalLiteralsLevel.count(reasonLiteral)!=0){\n";
                //         *out << ind++ << "if(externalLiteralsLevel[reasonLiteral] == currentDecisionLevel)\n";
                //             *out << ind-- << "currentLit = reasonLiteral;\n";
                //     *out << --ind << "}\n";
                // *out << --ind << "}\n";

                *out << ind << "Tuple literal = reasonLiteral>0 ? atomsTable[reasonLiteral]:atomsTable[-reasonLiteral];\n";
                // *out << ind << "std::cout<<\"Reason Literal \";literal.print();std::cout<<std::endl;\n";
                *out << ind++ << "if(visitedLiteral.count(reasonLiteral) == 0){\n";
                    *out << ind << "visitedLiteral.insert(reasonLiteral);\n";
                    *out << ind++ << "if(externalLiteralsLevel.count(reasonLiteral)==0){\n";
                        *out << ind << "stack.push_back(reasonLiteral);\n";
                        // *out << ind << "std::cout<<\"Internal lit\"<<std::endl;\n";
                    *out << --ind << "}else{\n";
                    ind++;
                        // *out << ind << "std::cout<<\"External literal\"<<std::endl;\n";
                        *out << ind << "reas.insert(reasonLiteral);\n";
                    *out << --ind << "}\n";

                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        // *out << ind++ << "for(unsigned i=0; i<reas.size(); i++){\n";
        //     *out << ind << "Tuple t = reas[i]>0 ? atomsTable[reas[i]] : atomsTable[-reas[i]];\n";
        //     *out << ind << "std::cout<<reas[i]<<\" \";t.print();std::cout<<std::endl;\n";
        // *out << --ind << "}\n";
        // *out << ind << "std::cout<<\"End explaining\"<<std::endl;\n";
        *out << ind << "return 0;\n";
    *out << --ind << "}\n";
    *out << ind++ << "void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){\n";
        // *out << ind << "int v = var==-1?var:-var;\n";
        // // *out << ind << "std::cout << \"Explain \" << v << std::endl;\n";

        // *out << ind << "PostponedReasonData* data = reasonMapping.getAt(v);\n";
        // *out << ind << "if(data == nullptr || data->getPropagationLevel() == -1) return;\n";
        // *out << ind << "const std::vector<int>* aggregates_id = &data->getAggregateId();\n";
        // *out << ind++ << "for(int i=0; i < aggregates_id->size();i++){\n";
        //     *out << ind << "int aggr_index=aggregates_id->at(i);\n";
        //     *out << ind << "std::vector<int> sharedVars(data->getSharedVariables());\n";
        //     *out << ind << "unsigned int  varsIndex=sharedVariable[aggr_index].addElements(sharedVars)->getId();\n";
        //     // *out << ind << "std::cout << \"Collecting reason from aggr \" <<aggr_index<<std::endl;\n";
        //     *out << ind++ << "if(data->isPositive(i)){\n";
        //         // *out << ind << "std::cout<<\"Positive\"<<std::endl;\n";
        //         *out << ind << "positiveAggrReason[aggr_index][varsIndex].getLiteralUntil(data->getPropagationLevel(),reas);\n";
        //             // *out << ind << "int uLit= lit>=0 ? lit : -1*lit;\n";
        //             // *out << ind << "std::string m= lit>=0 ? \"\" : \"-\";\n";
        //             // *out << ind << "std::cout << m; atomsTable[uLit].print(); std::cout<<std::endl;\n";
        //             // *out << ind << "std::cout << lit << std::endl;\n";
        //     *out << --ind << "}else{\n";
        //         ind++;
        //         // *out << ind << "std::cout << \"Negative\" <<std::endl;\n";
        //         *out << ind << "negativeAggrReason[aggr_index][varsIndex].getLiteralUntil(data->getPropagationLevel(),reas);\n";
        //             // *out << ind << "int uLit= lit>=0 ? lit : -1*lit;\n";
        //             // *out << ind << "std::string m= lit>=0 ? \"\" : \"-\";\n";
        //             // *out << ind << "std::cout << m; atomsTable[uLit].print(); std::cout<<std::endl;\n";
        //             // *out << ind << "std::cout << lit << std::endl;\n";
        //     *out << --ind << "}\n";
        // *out << --ind << "}\n";
        // // *out << ind << "std::cout << \"Collecting reason from constraint body \" <<std::endl;\n";
        // *out << ind << "const UnorderedSet<int>* body = &data->getBodyReason();\n";
        // *out << ind++ << "for(unsigned i=0;i<body->size();i++){\n";
        //     // *out << ind << "int uLit= l>=0 ? l : -1*l;\n";
        //     // *out << ind << "std::string m= l>=0 ? \"\" : \"-\";\n";
        //     // *out << ind << "std::cout << m; atomsTable[uLit].print(); std::cout<<std::endl;\n";
        //     // *out << ind << "std::cout << l << std::endl;\n";

        //     *out << ind << "reas.insert(body->at(i));\n";
        // *out << --ind << "}\n";
        // // *out << ind << "std::cout << \"reason computed\" <<std::endl;\n";

        *out << ind << "return;\n";
    *out << --ind << "}\n";

    if (programHasConstraint) {
        *out << ind++ << "void explainPositiveLiteral(const Tuple * tuple, std::unordered_set<std::string> & open_set, std::vector<const Tuple*> & outputReasons) {\n";
        //*out << ind << "const std::vector<const Tuple*> & tupleReasons = predicateReasonsMap.at(*tuple->getPredicateName())->at(tuple->getId());\n";
        // *out << ind << "std::cout << \"explainPositiveLiteral\" <<std::endl;\n";
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

    // COMMENTED FOR INCOMPATIBILITIES
    // if (program.hasConstraint()) {
    //     writeNegativeReasonsFunctionsPrototypes(program);
    //     // *out << ind << "void explainPositiveLiteral(const Tuple *, std::unordered_set<std::string> &, std::vector<const Tuple*> &);\n";
    //     writeNegativeReasonsFunctions(program);
    // }

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
        *out << ind << "unRoll=false;\n";

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

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple.getPredicateName());\n";
        *out << ind++ << "if (fSetIt == predicateFSetMap.end()) {\n";
        *out << ind << "} else {\n";
            *out << ind++ << "if (var < 0) {\n";

                *out << ind << "const auto& insertResult = fSetIt->second->insert(Tuple(tuple));\n";
                *out << ind++ << "if (insertResult.second) {\n";

                    *out << ind++ << "for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[fSetIt->first]) {\n";
                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

        for(const auto& aggrSetPred : aggrSetToRule){
            for(unsigned ruleId : aggrSetPred.second){
                const aspc::Rule* rule = &program.getRules()[ruleId];
                const aspc::Atom* aggrId = &rule->getHead()[0];
                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                unsigned sumVar = 0;
                if(!aggregateRelation->getAggregate().isSum() || builder->isAggrSetPredicate(aggrSetPred.first))
                    continue;
                if(!builder->isAggrSetPredicate(aggrSetPred.first)){
                    std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                    for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                        if(aggrSetLit->getTermAt(i)==var){
                            sumVar=i;
                            break;
                        }
                    }
                }
                *out << ind++ << "if(tuple.getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                    if(aggrId->getAriety() == 0){
                        *out << ind << "auto itAggrId = tupleToVar.find(Tuple({},&_"<<aggrId->getPredicateName()<<"));\n";
                        *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                            *out << ind++ << "if(var>0)\n";
                                *out << ind-- << "actualSum[itAggrId->second]+=tuple["<<sumVar<<"];\n";
                            *out << ind << "possibleSum[itAggrId->second]-=tuple["<<sumVar<<"];\n";
                        *out << --ind << "}\n";
                    }else{
                        std::string terms = "";
                        unsigned varIndex = 0;
                        for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                            if(varIndex>0){
                                terms+=",";
                            }
                            terms+="tuple["+std::to_string(var)+"]";
                            varIndex++;
                        }
                        std::string mapName = aggrId->getPredicateName()+"_";
                        for(unsigned var : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                            mapName+=std::to_string(var)+"_";
                        }
                        for(std::string sign : {"p","u","f"}){
                            *out << ind++ << "{\n";
                                *out << ind << "const std::vector<const Tuple*>* aggrIds = &"<<sign<<mapName<<".getValues({"<<terms<<"});\n";
                                *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                    *out << ind << "auto itAggrId = tupleToVar.find(*aggrIds->at(i));\n";
                                    *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                        *out << ind++ << "if(var>0)\n";
                                            *out << ind-- << "actualSum[itAggrId->second]+=tuple["<<sumVar<<"];\n";
                                        *out << ind << "possibleSum[itAggrId->second]-=tuple["<<sumVar<<"];\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";            
                            *out << --ind << "}\n";
                        }
                    }                                
                *out << --ind << "}\n";
            }
        }
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
        *out << ind << "reasonForLiteral.erase(var);\n";
        *out << ind << "externalLiteralsLevel.erase(var);\n";

        *out << ind << "\n//Only for debug\n";
        *out << ind << "reasonForLiteral.erase(-var);\n\n";
        *out << ind << "unRoll=true;\n";

        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "const Tuple & tuple = atomsTable[uVar];\n";

        *out << ind << "std::unordered_map<const std::string*,int>::iterator sum_it;\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";
        // *out << ind << "std::cout<<\"Undef \"<<minus;tuple.print();std::cout<<std::endl;\n";

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

        *out << ind++ << "if (var < 0) {\n";
            *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple.getPredicateName());\n";
            *out << ind++ << "if (fSetIt != predicateWSetMap.end()) {\n";
                // *out << ind << "std::cout<<\"Erase from true\"<<std::endl;\n";
                *out << ind << "fSetIt->second->erase(tuple);\n";
                // *out << ind << "if(wSetIt->second->find(tuple)!=NULL) std::cout<<\"Tuple not erased from true for \"<<tuple.getPredicateName()<<std::endl;\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

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

        for(const auto& aggrSetPred : aggrSetToRule){
            for(unsigned ruleId : aggrSetPred.second){
                const aspc::Rule* rule = &program.getRules()[ruleId];
                const aspc::Atom* aggrId = &rule->getHead()[0];
                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                unsigned sumVar = 0;
                if(!aggregateRelation->getAggregate().isSum() || builder->isAggrSetPredicate(aggrSetPred.first))
                    continue;
                if(!builder->isAggrSetPredicate(aggrSetPred.first)){
                    std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                    for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                        if(aggrSetLit->getTermAt(i)==var){
                            sumVar=i;
                            break;
                        }
                    }
                }
                *out << ind++ << "if(tuple.getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                    if(aggrId->getAriety() == 0){
                        *out << ind << "auto itAggrId = tupleToVar.find(Tuple({},&_"<<aggrId->getPredicateName()<<"));\n";
                        *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                            *out << ind++ << "if(var>0)\n";
                                *out << ind-- << "actualSum[itAggrId->second]-=tuple["<<sumVar<<"];\n";
                            *out << ind << "possibleSum[itAggrId->second]+=tuple["<<sumVar<<"];\n";
                        *out << --ind << "}\n";
                    }else{
                        std::string terms = "";
                        unsigned varIndex = 0;

                        for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                            if(varIndex > 0){
                                terms+=",";
                            }
                            terms+="tuple["+std::to_string(var)+"]";
                            varIndex++;
                        }
                        std::string mapName = aggrId->getPredicateName()+"_";
                        for(unsigned var : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                            mapName+=std::to_string(var)+"_";
                        }
                        for(std::string sign : {"p","u","f"}){
                            *out << ind++ << "{\n";
                                *out << ind << "const std::vector<const Tuple*>* aggrIds = &"<<sign<<mapName<<".getValues({"<<terms<<"});\n";
                                *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                    *out << ind << "auto itAggrId = tupleToVar.find(*aggrIds->at(i));\n";
                                    *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                        *out << ind++ << "if(var>0)\n";
                                            *out << ind-- << "actualSum[itAggrId->second]-=tuple["<<sumVar<<"];\n";
                                        *out << ind << "possibleSum[itAggrId->second]+=tuple["<<sumVar<<"];\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";            
                            *out << --ind << "}\n";
                        }
                    }                                
                *out << --ind << "}\n";
            }
        }
        //--------------------------------------------------Aggregate structure update--------------------------------------------------

        // *out << ind++ << "for(auto& reasonMap:positiveAggrReason){\n";
        //     *out << ind++ << "for(auto& pair :reasonMap){\n";
        //         *out << ind << "pair.second.eraseCurrentLevel();\n";
        //     *out << --ind << "}\n";
        // *out << --ind << "}\n";
        // *out << ind++ << "for(auto& reasonMap:negativeAggrReason){\n";
        //     *out << ind++ << "for(auto& pair :reasonMap){\n";
        //         *out << ind << "pair.second.eraseCurrentLevel();\n";
        //     *out << --ind << "}\n";
        // *out << --ind << "}\n";
        // *out << ind++ << "if(currentReasonLevel>0)\n";
        //     *out << ind-- << "currentReasonLevel--;\n";

        // for(const auto& pair: aggrIdentifierForAggregateBody){
        //     const aspc::ArithmeticRelationWithAggregate* aggr = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[pair.second[0].first].getFormulas()[pair.second[0].second];
        //     int startingLiteral=0;
        //     for(const aspc::Literal& starter : aggr->getAggregate().getAggregateLiterals()){
        //         *out << ind++ << "if(tuple.getPredicateName() == &_"<<starter.getPredicateName()<<" && tuple.size()=="<<starter.getAriety()<<"){\n";
        //         bool checkFormat = checkTupleFormat(starter,"",false);
        //         std::unordered_set<std::string> boundVars;

        //         for(int i=0;i<starter.getAriety();i++){
        //             if(starter.isVariableTermAt(i)&&boundVars.count(starter.getTermAt(i))==0){
        //                 *out << ind << "int "<<starter.getTermAt(i)<<" = tuple["<<i<<"];\n";
        //                 boundVars.insert(starter.getTermAt(i));
        //             }
        //         }
        //         if(!starter.isNegated())
        //             *out << ind++ << "if(var > 0){\n";
        //         else
        //             *out << ind++ << "if(var < 0){\n";

        //                 //letterale vero diventa indefinito
        //                 *out << ind << "const std::vector<const Tuple*>& tuples = p_"<<aggr->getJoinTupleName()<<aggr->getAggrLitProj(startingLiteral)<<".getValues({";
        //                 for(int i=0;i<starter.getAriety();i++){
        //                     if(i>0)
        //                         *out << ",";
        //                     std::string mapStringConstant =  !isVariable(starter.getTermAt(i)) &&!isInteger(starter.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(starter.getTermAt(i)) + "\")" : starter.getTermAt(i);
        //                     *out << mapStringConstant;
        //                 }
        //                 *out << "});\n";

        //                 *out << ind++ << "while(!tuples.empty()){\n";

        //                     *out << ind << "Tuple t(*tuples.back());\n";
        //                     //--------------------------EREASING TRUE--------------------------
        //                     *out << ind << "w"<<aggr->getJoinTupleName()<<".erase(*tuples.back());\n";
        //                     //--------------------------END EREASING TRUE--------------------------
        //                     // *out << ind << "std::cout<<\"Erasing from true \"<<w"<<aggr->getJoinTupleName()<<".getTuples().size()<<\" \"<<p_"<<aggr->getJoinTupleName()<<".getValues({}).size()<<std::endl;\n";

        //                     *out << ind++ << "if(u"<<aggr->getJoinTupleName()<<".find(Tuple(t)) == NULL){\n";
        //                         //--------------------------INSERT UNDEF--------------------------
        //                         *out << ind << "const auto& insertResult = u" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
        //                         *out << ind++ << "if (insertResult.second) {\n";
        //                             *out << ind++ << "for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
        //                                 *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        //                             *out << --ind << "}\n";
        //                             // *out << ind << "std::cout<<\"Insert in undef \"<<u"<<aggr->getJoinTupleName()<<".getTuples().size()<<std::endl;\n";
        //                         *out << --ind << "}\n";

        //                         //--------------------------END INSERT UNDEF--------------------------


        //                         for(const auto& aggrIdentifier: pair.second){
        //                             const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
        //                             int ruleId = aggrIdentifier.first;
        //                             int aggrIndex = aggrIdentifier.second;
        //                             std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);
        //                             *out << ind++ << "{\n";
        //                                 boundVars.clear();
        //                                 for(int i=0;i<starter.getAriety();i++){
        //                                     if(starter.isVariableTermAt(i))
        //                                         boundVars.insert(starter.getTermAt(i));
        //                                 }
        //                                 for(unsigned v : sharedVariablesIndexesMap[key]){
        //                                     if(boundVars.count(aggregate->getAggregate().getTermAt(v))<=0){
        //                                         boundVars.insert(aggregate->getAggregate().getTermAt(v));
        //                                         *out << ind << "int "<<aggregate->getAggregate().getTermAt(v)<<" = t["<<v<<"];\n";
        //                                     }
        //                                 }

        //                                 //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------

        //                                 *out << ind << "std::vector<int> aggrKey({";
        //                                 bool first=true;
        //                                 std::string aggrVarProj;
        //                                 std::string aggrVarTuple;
        //                                 for(unsigned v: aggregateVariablesIndex[key]){
        //                                     if(!first){
        //                                         *out << ",";
        //                                         aggrVarTuple+=",";
        //                                     }
        //                                     *out << "t["<<v<<"]";
        //                                     aggrVarTuple+="t["+std::to_string(v)+"]";
        //                                     aggrVarProj+=std::to_string(v)+"_";
        //                                     first=false;
        //                                 }
        //                                 *out << "});\n";
        //                                 std::string sharedVarProj;
        //                                 for(unsigned v: sharedVariablesIndexesMap[key]){
        //                                     sharedVarProj+=std::to_string(v)+"_";
        //                                 }
        //                                 *out << ind << "unsigned int  aggrKeyIndex = aggrVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(aggrKey)->getId();\n";
        //                                 *out << ind << "int firstVar = aggrVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].get(aggrKeyIndex)->at(0);\n";
        //                                 *out << ind << "VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);\n";
        //                                 *out << ind << "std::vector<int>sharedBodyVars({"<<sharedVariablesMap[key]<<"});\n";

        //                                 *out << ind << "unsigned int  varsIndex = sharedVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(sharedBodyVars)->getId();\n";
        //                                 *out << ind << "auto& trueSet = trueAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";
        //                                 *out << ind << "auto& undefSet = undefAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";

        //                                 if(sharedVariablesMap[key]!=""){
        //                                     *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
        //                                 }else{
        //                                     *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({"<<aggrVarTuple<<"}).size()<=0){\n";
        //                                 }
        //                                     *out << ind++ << "if(trueSet.find(aggrVarsIndex)!=trueSet.end()){\n";
        //                                         *out << ind << "trueSet.erase(aggrVarsIndex);\n";
        //                                         if(aggregate->getAggregate().isSum()){
        //                                             *out << ind << "actualSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]-=firstVar;\n";
        //                                         }
        //                                     *out << --ind << "}\n";
        //                                 *out << --ind << "}\n";
        //                                 *out << ind++ << "if(undefSet.find(aggrVarsIndex)==undefSet.end()){\n";
        //                                     *out << ind++ << "if(trueSet.find(aggrVarsIndex)==trueSet.end()){\n";
        //                                         *out << ind << "undefSet.insert(aggrVarsIndex);\n";
        //                                         if(aggregate->getAggregate().isSum()){
        //                                             *out << ind << "possibleSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]+=firstVar;\n";
        //                                         }
        //                                     *out << --ind << "}\n";
        //                                 *out << --ind << "}\n";
        //                                 //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
        //                             *out << --ind << "}\n";
        //                         }
        //                     *out << --ind << "}\n";

        //                 *out << --ind << "}\n";

        //                 *out << ind << "const std::vector<const Tuple*>& tuplesN = np_"<<aggr->getJoinTupleName()<<aggr->getAggrLitProj(startingLiteral)<<".getValues({";
        //                 for(int i=0;i<starter.getAriety();i++){
        //                     if(i>0)
        //                         *out << ",";
        //                     std::string mapStringConstant =  !isVariable(starter.getTermAt(i)) &&!isInteger(starter.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(starter.getTermAt(i)) + "\")" : starter.getTermAt(i);
        //                     *out << mapStringConstant;
        //                 }
        //                 *out << "});\n";

        //                 *out << ind++ << "while(!tuplesN.empty()){\n";

        //                     *out << ind << "Tuple t(*tuplesN.back());\n";
        //                     //--------------------------EREASING TRUE--------------------------
        //                     *out << ind << "nw"<<aggr->getJoinTupleName()<<".erase(*tuplesN.back());\n";
        //                     //--------------------------END EREASING TRUE--------------------------
        //                     *out << ind++ << "if(nu"<<aggr->getJoinTupleName()<<".find(Tuple(t)) == NULL){\n";
        //                         *out << ind << "const auto& insertResult = nu" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
        //                         *out << ind++ << "if (insertResult.second) {\n";
        //                             *out << ind++ << "for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
        //                                 *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        //                             *out << --ind << "}\n";
        //                         *out << --ind << "}\n";
        //                         for(const auto& aggrIdentifier: pair.second){
        //                             const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
        //                             int ruleId = aggrIdentifier.first;
        //                             int aggrIndex = aggrIdentifier.second;
        //                             std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);
        //                             *out << ind++ << "{\n";
        //                                 boundVars.clear();
        //                                 for(int i=0;i<starter.getAriety();i++){
        //                                     if(starter.isVariableTermAt(i))
        //                                         boundVars.insert(starter.getTermAt(i));
        //                                 }
        //                                 for(unsigned v : sharedVariablesIndexesMap[key]){
        //                                     if(boundVars.count(aggregate->getAggregate().getTermAt(v))<=0){
        //                                         boundVars.insert(aggregate->getAggregate().getTermAt(v));
        //                                         *out << ind << "int "<<aggregate->getAggregate().getTermAt(v)<<" = t["<<v<<"];\n";
        //                                     }
        //                                 }

        //                                 //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------

        //                                 *out << ind << "std::vector<int> aggrKey({";
        //                                 bool first=true;
        //                                 std::string aggrVarProj;
        //                                 std::string aggrVarTuple;
        //                                 for(unsigned v: aggregateVariablesIndex[key]){
        //                                     if(!first){
        //                                         *out << ",";
        //                                         aggrVarTuple+=",";
        //                                     }
        //                                     *out << "t["<<v<<"]";
        //                                     aggrVarTuple+="t["+std::to_string(v)+"]";
        //                                     aggrVarProj+=std::to_string(v)+"_";
        //                                     first=false;
        //                                 }
        //                                 *out << "});\n";
        //                                 *out << ind << "unsigned int  aggrKeyIndex = aggrVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(aggrKey)->getId();\n";
        //                                 *out << ind << "int firstVar = aggrVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].get(aggrKeyIndex)->at(0);\n";
        //                                 *out << ind << "VarsIndex aggrVarsIndex(firstVar,aggrKeyIndex);\n";
        //                                 std::string sharedVarProj;
        //                                 for(unsigned v: sharedVariablesIndexesMap[key]){
        //                                     sharedVarProj+=std::to_string(v)+"_";
        //                                 }
        //                                 if(sharedVariablesMap[key]!=""){
        //                                     *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
        //                                 }else{
        //                                     *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({"<<aggrVarTuple<<"}).size()<=0){\n";
        //                                 }

        //                                     *out << ind << "std::vector<int>sharedBodyVars({"<<sharedVariablesMap[key]<<"});\n";
        //                                     *out << ind << "unsigned int  varsIndex = sharedVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(sharedBodyVars)->getId();\n";
        //                                     *out << ind << "auto& undefSet = undefNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";
        //                                     *out << ind << "auto& trueSet = trueNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";

        //                                     if(aggregate->getAggregate().isSum()){
        //                                         *out << ind++ << "if(undefSet.find(aggrVarsIndex)==undefSet.end()){\n";
        //                                             *out << ind++ << "if(trueSet.find(aggrVarsIndex)==trueSet.end()){\n";
        //                                                 *out << ind << "undefSet.insert(aggrVarsIndex);\n";
        //                                                 if(aggregate->getAggregate().isSum()){
        //                                                     //sub negative key to possible sum
        //                                                     *out << ind << "possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]-=firstVar;\n";
        //                                                 }
        //                                             *out << --ind << "}\n";
        //                                         *out << --ind << "}\n";
        //                                     }else{
        //                                         *out << ind++ << "if(trueSet.find(aggrVarsIndex) != trueSet.end()){\n";
        //                                             *out << ind << "trueSet.erase(aggrVarsIndex);\n";
        //                                         *out << --ind << "}\n";
        //                                         *out << ind++ << "if(undefSet.find(aggrVarsIndex) == undefSet.end()){\n";
        //                                             *out << ind++ << "if(trueSet.find(aggrVarsIndex) == trueSet.end()){\n";
        //                                                 *out << ind << "undefSet.insert(aggrVarsIndex);\n";
        //                                             *out << --ind << "}\n";
        //                                         *out << --ind << "}\n";
        //                                     }


        //                                 *out << --ind << "}\n";
        //                             *out << --ind << "}\n";
        //                         }
        //                     *out << --ind << "}\n";
        //                 *out << --ind << "}\n";
        //             *out << --ind << "}\n";

        //                 boundVars.clear();
        //                 for(int i=0;i<starter.getAriety();i++){
        //                     if(starter.isVariableTermAt(i)&&boundVars.count(starter.getTermAt(i))==0){
        //                         boundVars.insert(starter.getTermAt(i));
        //                     }
        //                 }
        //                 int closingPars=0;
        //                 int buildIndex=0;
        //                 std::string jointuple;
        //                 std::vector<std::vector<std::string>> previousLit;
        //                 previousLit.push_back({starter.getPredicateName(),std::to_string(starter.isNegated()),std::to_string(startingLiteral)});
        //                 for(const aspc::Literal& li : aggr->getAggregate().getAggregateLiterals()){
        //                     for(int i=0;i<li.getAriety();i++){
        //                         std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
        //                         jointuple+=mapStringConstant+",";
        //                     }
        //                     if(buildIndex!=startingLiteral){
        //                         if(li.isBoundedLiteral(boundVars)){
        //                             std::string literalTerms;
        //                             for(int i=0;i<li.getAriety();i++){
        //                                 if(i>0)
        //                                     literalTerms+=",";
        //                                 std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
        //                                 literalTerms+=mapStringConstant;
        //                             }

        //                             if(li.isPositiveLiteral()){
        //                                 *out << ind << "const Tuple* tuple"<<buildIndex<<" = w"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
        //                                 *out << ind << "bool undef"<<buildIndex<<" = false;\n";
        //                                 *out << ind++ << "if(tuple"<<buildIndex<<"==NULL){\n";
        //                                     *out << ind << "tuple"<<buildIndex<<" = u"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
        //                                     *out << ind << "undef"<<buildIndex<<" = true;\n";
        //                                 *out << --ind << "}\n";
        //                             }else{
        //                                 *out << ind << "const Tuple negativeTuple"<<buildIndex<<"({"<<literalTerms<<"},&_"<<li.getPredicateName()<<",true);\n";
        //                                 *out << ind << "const Tuple* tuple"<<buildIndex<<" = u"<<li.getPredicateName()<<".find(Tuple({"<<literalTerms<<"},&_"<<li.getPredicateName()<<"));\n";
        //                                 *out << ind << "bool undef"<<buildIndex<<" = false;\n";
        //                                 *out << ind++ << "if(tuple"<<buildIndex<<"!=NULL){\n";
        //                                     *out << ind << "undef"<<buildIndex<<" = true;\n";
        //                                 *out << --ind << "}else if(w"<<li.getPredicateName()<<".find(negativeTuple"<<buildIndex<<")==NULL){\n";
        //                                     *out << ++ind << "tuple"<<buildIndex<<"=&negativeTuple"<<buildIndex<<";\n";
        //                                 *out << --ind << "}\n";
        //                             }
        //                             *out << ind++ << "if(tuple"<<buildIndex<<"!=NULL){\n";
        //                                 for(auto & pair:previousLit){
        //                                     if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
        //                                         std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
        //                                         *out << ind++ << "if(";
        //                                         for(int i=0;i<li.getAriety();i++){
        //                                             if (i>0){
        //                                                 *out << " || ";
        //                                             }
        //                                             *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
        //                                         }
        //                                         *out << "){\n";

        //                                         closingPars++;
        //                                     }
        //                                 }
        //                             closingPars++;
        //                             previousLit.push_back({li.getPredicateName(),std::to_string(li.isNegated()),std::to_string(buildIndex)});
        //                         }else{
        //                             std::string literalTerms;
        //                             std::string boundTermsIndex;
        //                             bool first=true;
        //                             for(int i=0;i<li.getAriety();i++){
        //                                 if(!li.isVariableTermAt(i) || boundVars.count(li.getTermAt(i))>0){
        //                                     if(!first)
        //                                         literalTerms+=",";
        //                                     std::string mapStringConstant =  !isVariable(li.getTermAt(i)) &&!isInteger(li.getTermAt(i)) ? "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(li.getTermAt(i)) + "\")" : li.getTermAt(i);
        //                                     literalTerms+=mapStringConstant;
        //                                     first=false;
        //                                     boundTermsIndex+= std::to_string(i)+"_";
        //                                 }
        //                             }

        //                             *out << ind << "const std::vector<const Tuple*>& tuples"<<buildIndex<<" = p"<<li.getPredicateName()<<"_"<<boundTermsIndex<<".getValues({"<<literalTerms<<"});\n";
        //                             *out << ind << "const std::vector<const Tuple*>& tuplesU"<<buildIndex<<" = u"<<li.getPredicateName()<<"_"<<boundTermsIndex<<".getValues({"<<literalTerms<<"});\n";
        //                             *out << ind++ << "for(int i_"<<buildIndex<<"=0;i_"<<buildIndex<<"<tuples"<<buildIndex<<".size()+tuplesU"<<buildIndex<<".size();i_"<<buildIndex<<"++){\n";
        //                             closingPars++;
        //                                 *out << ind << "const Tuple* tuple"<<buildIndex<<";\n";
        //                                 *out << ind << "bool undef"<<buildIndex<<"=false;\n";
        //                                 *out << ind++ << "if(i_"<<buildIndex<<"<tuples"<<buildIndex<<".size())";
        //                                     *out << ind-- << "tuple"<<buildIndex<<"=tuples"<<buildIndex<<"[i_"<<buildIndex<<"];\n";
        //                                 *out << ind++ << "else{\n";
        //                                     *out << ind << "tuple"<<buildIndex<<"=tuplesU"<<buildIndex<<"[i_"<<buildIndex<<"-tuples"<<buildIndex<<".size()];\n";
        //                                     *out << ind << "undef"<<buildIndex<<"=true;\n";
        //                                 *out << --ind << "}\n";
        //                             if(checkTupleFormat(li,std::to_string(buildIndex),true))
        //                                 closingPars++;
        //                                 for(auto & pair:previousLit){
        //                                     if(pair[0] == li.getPredicateName() && pair[1]!=std::to_string(li.isNegated())){
        //                                         std::string previousIndex = pair[2]==std::to_string(startingLiteral) ? "tuple":"(*tuple"+pair[2]+")";
        //                                         *out << ind++ << "if(";
        //                                         for(int i=0;i<li.getAriety();i++){
        //                                             if (i>0){
        //                                                 *out << " || ";
        //                                             }
        //                                             *out << "(*tuple"<<buildIndex<<")["<<i<<"]!="<<previousIndex<<"["<<i<<"]";
        //                                         }
        //                                         *out << "){\n";

        //                                         closingPars++;
        //                                     }
        //                                 }
        //                             for(int i=0;i<li.getAriety();i++){
        //                                 if(li.isVariableTermAt(i)&&boundVars.count(li.getTermAt(i))==0){
        //                                     *out << ind << "int "<<li.getTermAt(i)<<" = tuple"<<buildIndex<<"->at("<<i<<");\n";
        //                                     boundVars.insert(li.getTermAt(i));
        //                                 }
        //                             }

        //                             previousLit.push_back({li.getPredicateName(),std::to_string(li.isNegated()),std::to_string(buildIndex)});

        //                         }
        //                     }
        //                     buildIndex++;
        //                 }
        //                 for(const aspc::ArithmeticRelation& inequality : aggr->getAggregate().getAggregateInequalities()){
        //                     if(inequality.isBoundedRelation(boundVars)){
        //                         *out << ind++ << "if("<<inequality.getStringRep()<<"){\n";
        //                         closingPars++;
        //                     }else if(inequality.isBoundedValueAssignment(boundVars)){
        //                         *out << ind << "int "<<inequality.getAssignmentStringRep(boundVars)<<";\n";
        //                         jointuple+=inequality.getAssignedVariable(boundVars)+",";
        //                         boundVars.insert(inequality.getAssignedVariable(boundVars));
        //                     }
        //                 }
        //                     //--------------------------SAVING NEW UNDEF--------------------------
        //                     *out << ind << "Tuple t({"<<jointuple.substr(0,jointuple.length()-1)<<"},&_"<<aggr->getJoinTupleName()<<");\n";


        //                     //--------------------------END SAVING NEW UNDEF--------------------------

        //                     for(const auto& aggrIdentifier: pair.second){
        //                         const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) program.getRules()[aggrIdentifier.first].getFormulas()[aggrIdentifier.second];
        //                         int ruleId = aggrIdentifier.first;
        //                         int aggrIndex = aggrIdentifier.second;
        //                         std::string key = std::to_string(ruleId)+":"+std::to_string(aggrIndex);

        //                         *out << ind++ << "{\n";
        //                             //--------------------------UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------

        //                             *out << ind << "std::vector<int> aggrKey({";
        //                             bool first=true;
        //                             std::string aggrVarProj;
        //                             std::string aggrVarTuple;
        //                             for(unsigned v: aggregateVariablesIndex[key]){
        //                                 if(!first){
        //                                     *out << ",";
        //                                     aggrVarTuple+=",";
        //                                 }
        //                                 *out << "t["<<v<<"]";
        //                                 aggrVarTuple+="t["+std::to_string(v)+"]";
        //                                 aggrVarProj+=std::to_string(v)+"_";
        //                                 first=false;

        //                             }
        //                             *out << "});\n";
        //                             *out << ind << "unsigned int  aggrKeyIndex = aggrVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(aggrKey)->getId();\n";
        //                             *out << ind << "int firstVar=aggrVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].get(aggrKeyIndex)->at(0);\n";
        //                             *out << ind << "VarsIndex aggVarsIndex(firstVar,aggrKeyIndex);\n";

        //                             *out << ind++ << "if(firstVar>=0){\n";
        //                                 {
        //                                     *out << ind++ << "if(u"<<aggr->getJoinTupleName()<<".find(Tuple(t))==NULL){\n";
        //                                         *out << ind++ << "if(w" << aggr->getJoinTupleName() <<".find(t))\n";
        //                                         *out << ind-- << "w" << aggr->getJoinTupleName() <<".erase(t);\n";

        //                                         *out << ind << "const auto& insertResult = u" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
        //                                         *out << ind++ << "if (insertResult.second) {\n";
        //                                             *out << ind++ << "for(AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
        //                                                 *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        //                                             *out << --ind << "}\n";
        //                                         *out << --ind << "}\n";
        //                                     *out << --ind << "}\n";
        //                                     std::string sharedVarProj;
        //                                     for(unsigned v: sharedVariablesIndexesMap[key]){
        //                                         sharedVarProj+=std::to_string(v)+"_";
        //                                     }
        //                                     *out << ind << "std::vector<int>sharedBodyVars({"<<sharedVariablesMap[key]<<"});\n";
        //                                     *out << ind << "unsigned int  varsIndex = sharedVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(sharedBodyVars)->getId();\n";
        //                                     *out << ind << "auto& trueSet = trueAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";
        //                                     *out << ind << "auto& undefSet = undefAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";

        //                                     if(sharedVariablesMap[key]!=""){
        //                                         // *out << ind++ << "if(sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariablesMap[key]<<"})>0 && sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<"[{"<<sharedVariablesMap[key]<<"}]->first->getValues(aggrKey).size()<=0){\n";
        //                                         *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
        //                                     }else{
        //                                         *out << ind++ << "if(p_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({"<<aggrVarTuple<<"}).size()<=0){\n";
        //                                     }
        //                                         *out << ind++ << "if(trueSet.find(aggVarsIndex)!=trueSet.end()){\n";
        //                                             *out << ind << "trueSet.erase(aggVarsIndex);\n";
        //                                             if(aggregate->getAggregate().isSum()){
        //                                                 *out << ind << "actualSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]-=firstVar;\n";
        //                                             }
        //                                         *out << --ind << "}\n";
        //                                         *out << ind++ << "if(undefSet.find(aggVarsIndex)==undefSet.end()){\n";
        //                                             *out << ind++ << "if(trueSet.find(aggVarsIndex)==trueSet.end()){\n";
        //                                                 *out << ind << "undefSet.insert(aggVarsIndex);\n";
        //                                                 if(aggregate->getAggregate().isSum()){
        //                                                     *out << ind << "possibleSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]+=firstVar;\n";
        //                                                 }
        //                                             *out << --ind << "}\n";
        //                                         *out << --ind << "}\n";
        //                                     *out << --ind << "}\n";
        //                                     //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
        //                                 }
        //                             *out << --ind << "}else{\n";
        //                                 ind++;
        //                                 {
        //                                     *out << ind++ << "if(nu"<<aggr->getJoinTupleName()<<".find(Tuple(t))==NULL){\n";
        //                                         *out << ind++ << "if(nw" << aggr->getJoinTupleName() <<".find(t))\n";
        //                                         *out << ind-- << "nw" << aggr->getJoinTupleName() <<".erase(t);\n";

        //                                         *out << ind << "const auto& insertResult = nu" << aggr->getJoinTupleName() <<".insert(Tuple(t));\n";
        //                                         *out << ind++ << "if (insertResult.second) {\n";
        //                                             *out << ind++ << "for(AuxMap* auxMap : predicateToNegativeUndefAuxiliaryMaps[&_"<<aggr->getJoinTupleName()<<"]){\n";
        //                                                 *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        //                                             *out << --ind << "}\n";
        //                                         *out << --ind << "}\n";
        //                                     *out << --ind << "}\n";
        //                                     std::string sharedVarProj;
        //                                     for(unsigned v: sharedVariablesIndexesMap[key]){
        //                                         sharedVarProj+=std::to_string(v)+"_";
        //                                     }

        //                                     *out << ind << "std::vector<int>sharedBodyVars({"<<sharedVariablesMap[key]<<"});\n";
        //                                     *out << ind << "unsigned int  varsIndex = sharedVariable["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"].addElements(sharedBodyVars)->getId();\n";
        //                                     *out << ind << "auto& trueSet = trueNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";
        //                                     *out << ind << "auto& undefSet = undefNegativeAggrVars["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";

        //                                     if(sharedVariablesMap[key]!=""){
        //                                         // *out << ind++ << "if(sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<".count({"<<sharedVariablesMap[key]<<"})>0 && sharedVariables_"<<ruleId<<"_ToAggregate_"<<aggrIndex<<"[{"<<sharedVariablesMap[key]<<"}]->first->getValues(aggrKey).size()<=0){\n";
        //                                         *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<sharedVarProj<<aggrVarProj<<".getValues({"<<sharedVariablesMap[key]<<","<<aggrVarTuple<<"}).size()<=0){\n";
        //                                     }else{
        //                                         *out << ind++ << "if(np_"<<aggregate->getJoinTupleName()<<aggrVarProj<<".getValues({"<<aggrVarTuple<<"}).size()<=0){\n";
        //                                     }
        //                                         *out << ind++ << "if(trueSet.find(aggVarsIndex)!=trueSet.end()){\n";
        //                                             *out << ind << "trueSet.erase(aggVarsIndex);\n";
        //                                             if(aggregate->getAggregate().isSum()){
        //                                                 *out << ind << "actualNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]+=firstVar;\n";
        //                                             }
        //                                         *out << --ind << "}\n";
        //                                         *out << ind++ << "if(undefSet.find(aggVarsIndex)==undefSet.end()){\n";
        //                                             *out << ind++ << "if(trueSet.find(aggVarsIndex)==trueSet.end()){\n";
        //                                                 *out << ind << "undefSet.insert(aggVarsIndex);\n";
        //                                                 if(aggregate->getAggregate().isSum()){
        //                                                     *out << ind << "possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]-=firstVar;\n";
        //                                                     *out << ind << "int possSum = possibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex];\n";

        //                                                     *out << ind++ << "if(maxPossibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]<possSum)\n";
        //                                                         *out << ind-- << "maxPossibleNegativeSum["<<aggregateToStructure[aggregate->getJoinTupleName()+sharedVariablesMap[key]+aggregate->getAggrVarAsString()]<<"][varsIndex]=possSum;\n";
        //                                                 }
        //                                             *out << --ind << "}\n";
        //                                         *out << --ind << "}\n";
        //                                     *out << --ind << "}\n";

        //                                     //--------------------------END UPDATE AGGREGATE VARIABLE STRUCTURE--------------------------
        //                                 }
        //                             *out << --ind << "}\n";
        //                         *out << --ind << "}\n";
        //                     }
        //                 while(closingPars>0){
        //                     closingPars--;
        //                     *out << --ind << "}\n";
        //                 }

        //             if(checkFormat)
        //                     *out << --ind << "}\n";
        //         *out << --ind << "}\n";
        //         startingLiteral++;
        //     }
        // }
        // for(const aspc::Rule& r : program.getRules()){
        //     //aggiungo alla mappa delle shared variables le tuple di shared variables indefinite
        //     for(int i=0;i<r.getBodyLiterals().size();i++){
        //         bool hasSharedVar = false;
        //         for(const aspc::ArithmeticRelationWithAggregate& aggr:r.getArithmeticRelationsWithAggregate()){
        //             if(sharedVariablesMap[std::to_string(r.getRuleId())+":"+std::to_string(aggr.getFormulaIndex())]!="")
        //                 hasSharedVar=true;

        //         }
        //         if(hasSharedVar){
        //             *out << ind++ << "if(tuple.getPredicateName() == &_" << r.getBodyLiterals()[i].getPredicateName()<<"){\n";
        //             updateUndefinedSharedVariablesMap(r,i);
        //             *out << --ind <<"}\n";
        //         }
        //     }
        // }
        // *out << ind << "std::vector<int> emptyA;\n";
        // *out << ind << "unsigned int  v = aggrVariable[0].addElements(emptyA)->getId();\n";
        // *out << ind << "std::cout<<\"Actual Sum \"<<actualSum[0][v]<<std::endl;\n";
        // *out << ind << "std::cout<<\"Possible Sum \"<<possibleSum[0][v]<<std::endl;\n";
        // *out << ind << "for(auto& it : undefAggrVars[0][v]){ for(int i=0;i<it.getIndex()->size();i++){std::cout<<it.getIndex()->operator[](i)<<\" \";}std::cout<<endl;\n}";
        // *out << ind << "for(const Tuple* t: wb.getTuples()) t->print();\n";
        // *out << ind << "std::cout<<std::endl;\n";
        // *out << ind << "for(const Tuple* t: ub.getTuples()) t->print();\n";
        // *out << ind << "std::cout<<std::endl;\n";
        // *out << ind << "for(const Tuple* t: fb.getTuples()) t->print();\n";
        // *out << ind << "std::cout<<std::endl;\n";


    }
    *out << --ind << "}\n";


    // ---------------------- end onLiteralTrue(int var) --------------------------------------//
    // ---------------------- addedVarName(int var, const std::string & atom) --------------------------------------//
    // std::cout<<"Printing aux generation"<<std::endl;
    *out << ind++ << "void Executor::undefLiteralsReceived()const{\n";
        // *out << ind << "std::cout<<\"Undef received\"<<std::endl;\n";

        *out << ind++ << "if(undefinedLoaded)\n";
            *out << ind-- << "return;\n";
        *out << ind << "undefinedLoaded=true;\n";
        // *out << ind << "std::cout<<\"Undef generation\"<<std::endl;\n";

        std::vector<std::string> orderedAuxPredicate;
        std::unordered_map<std::string,std::string> headToAux;
        std::unordered_map<std::string,std::vector<aspc::Literal>> auxToBody(builder->getAuxPredicateBody());
        std::unordered_map<std::string,std::vector<aspc::ArithmeticRelation>> auxToInequality(builder->getAuxPredicateInequalities());

        while(!auxToBody.empty()){

            std::string auxPred="";
            for(const auto& auxBody : auxToBody){
                bool canBeEvaluated=true;
                for(unsigned i=0; i< auxBody.second.size(); i++){
                    if(!auxBody.second[i].isNegated()){
                        std::string predName=auxBody.second[i].getPredicateName();
                        if(headPreds.count(predName)!=0 && headToAux.count(predName)==0){
                            canBeEvaluated=false;
                            break;
                        }
                    }
                }
                if(canBeEvaluated){
                    auxPred=auxBody.first;
                    break;
                }
            }
            if(auxPred==""){
                // std::cout<<"Error during aux ordering"<<std::endl;
                exit(180);
            }
            for(const aspc::Rule& r :program.getRules()){
                if(!r.isConstraint() && !r.getBodyLiterals().empty() && r.getBodyLiterals()[0].getPredicateName() == auxPred)
                    headToAux[r.getHead()[0].getPredicateName()]=auxPred;

            }
            auxToBody.erase(auxPred);
            *out << ind++ << "{//Generating "<<auxPred<<"\n";
            std::unordered_set<unsigned> visitedLiterals;
            std::unordered_set<std::string> boundVariables;
            std::unordered_map<std::string,std::vector<std::pair<bool,unsigned>>> predicateSigns;
            unsigned closingPars=0;
            const auto& auxBody = builder->getAuxPredicateBody().find(auxPred);
            unordered_set<unsigned> visitedRelations;
            unsigned ineqIndex=0;
            for(const aspc::ArithmeticRelation& ineq : auxToInequality[auxPred]){
                if(ineq.isBoundedValueAssignment(boundVariables)){
                    *out << ind << "int "<<ineq.getAssignmentStringRep(boundVariables)<<";\n";
                    boundVariables.insert(ineq.getAssignedVariable(boundVariables));
                    visitedRelations.insert(ineqIndex);
                }
                ineqIndex++;
            }
            while(visitedLiterals.size()<auxBody->second.size()){
                const aspc::Literal* l=NULL;
                unsigned litIndex = 0;
                ineqIndex=0;
                for(const aspc::ArithmeticRelation& ineq : auxToInequality[auxPred]){
                    if(ineq.isBoundedValueAssignment(boundVariables) && visitedRelations.count(ineqIndex)==0){
                        *out << ind << "int "<<ineq.getAssignedVariable(boundVariables)<<" = "<<ineq.getAssignmentStringRep(boundVariables)<<";\n";
                        boundVariables.insert(ineq.getAssignedVariable(boundVariables));
                        visitedRelations.insert(ineqIndex);

                    }else if(ineq.isBoundedRelation(boundVariables) && visitedRelations.count(ineqIndex)==0){
                        *out << ind++ << "if("<<ineq.getStringRep()<<"){\n";
                        closingPars++;
                        visitedRelations.insert(ineqIndex);
                    }
                    ineqIndex++;
                }
                for(unsigned i=0; i<auxBody->second.size();i++){
                    if(visitedLiterals.count(i)==0){
                        if(auxBody->second[i].isBoundedLiteral(boundVariables)){
                            l=&auxBody->second[i];
                            litIndex=i;
                        }else if(auxBody->second[i].isPositiveLiteral() && l==NULL){
                            l=&auxBody->second[i];
                            litIndex=i;
                        }
                    }
                }
                if(l!=NULL){
                    visitedLiterals.insert(litIndex);

                    if(l->isBoundedLiteral(boundVariables)){
                        std::string boundTerms;
                        for(int k=0;k<l->getAriety();k++){
                            if((l->isVariableTermAt(k) && boundVariables.count(l->getTermAt(k))!=0)||!l->isVariableTermAt(k)){
                                if(boundTerms!="")
                                    boundTerms+=",";
                                boundTerms+=l->getTermAt(k);
                            }
                        }

                        if(l->isPositiveLiteral()){

                            *out << ind << "bool undef"<<litIndex<<"=false;\n";
                            *out << ind << "const Tuple* tuple"<<litIndex<<"=w"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                            *out << ind++ << "if(tuple"<<litIndex<<" == NULL){\n";
                                *out << ind << "tuple"<<litIndex<<"=u"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                                *out << ind++ << "if(tuple"<<litIndex<<" != NULL){\n";
                                    *out << ind << "undef"<<litIndex<<"=true;\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(tuple"<<litIndex<<" != NULL){\n";
                            // if(checkTupleFormat(*l,"tuple"+std::to_string(litIndex),true))
                            //     closingPars++;
                            if(predicateSigns.count(l->getPredicateName())!=0){
                                for(auto negatedLit : predicateSigns[l->getPredicateName()]){
                                    if(negatedLit.first != l->isNegated()){
                                        const aspc::Literal* ll = &auxBody->second[negatedLit.second];
                                        *out << ind++ << "if(";
                                        if(ll->getAriety() > 0 && ll->getAriety() == l->getAriety()){
                                            for(unsigned k=0;k<l->getAriety();k++){
                                                if(k>0)
                                                    *out << " || ";
                                                if(!ll->isNegated())
                                                    *out << "tuple"<<litIndex<<"->at("<<k<<") != tuple"<<negatedLit.second<<"->at("<<k<<")";
                                                else
                                                    *out << "tuple"<<litIndex<<"->at("<<k<<") != negativeTuple"<<negatedLit.second<<".at("<<k<<")";
                                            }
                                        }else if(ll->getAriety() == l->getAriety()){
                                            *out << "false";
                                        }
                                        *out << "){\n";
                                            closingPars++;
                                    }
                                }
                            }
                        }else{

                            *out << ind << "bool undef"<<litIndex<<"=false;\n";
                            *out << ind << "const Tuple negativeTuple"<<litIndex<<"({"<<boundTerms<<"},&_"<<l->getPredicateName()<<");\n";
                            *out << ind++ << "if(u"<<l->getPredicateName()<<".find(negativeTuple"<<litIndex<<")!=NULL){\n";
                                *out << ind << "undef"<<litIndex<<"=true;\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(undef"<<litIndex<<" || w"<<l->getPredicateName()<<".find(negativeTuple"<<litIndex<<")== NULL){\n";
                            // if(checkTupleFormat(*l,"negativeTuple",false))
                            //     closingPars++;
                            if(predicateSigns.count(l->getPredicateName())!=0){
                                for(auto negatedLit : predicateSigns[l->getPredicateName()]){
                                    if(negatedLit.first != l->isNegated()){
                                        const aspc::Literal* ll = &auxBody->second[negatedLit.second];
                                        *out << ind++ << "if(";
                                        if(ll->getAriety() > 0 && ll->getAriety() == l->getAriety()){
                                            for(unsigned k=0;k<l->getAriety();k++){
                                                if(k>0)
                                                    *out << " || ";
                                                *out << "negativeTuple"<<litIndex<<".at("<<k<<") != tuple"<<negatedLit.second<<"->at("<<k<<")";
                                            }
                                        }else if(ll->getAriety() == l->getAriety()){
                                            *out << "false";
                                        }
                                        *out << "){\n";
                                            closingPars++;
                                    }
                                }
                            }
                        }
                        closingPars++;

                    }else{
                        std::string boundTerms;
                        std::vector<unsigned> boundIndexes;
                        for(int k=0;k<l->getAriety();k++){
                            if((l->isVariableTermAt(k) && boundVariables.count(l->getTermAt(k))!=0)||!l->isVariableTermAt(k)){
                                if(boundTerms!="")
                                    boundTerms+=",";
                                boundTerms+=l->getTermAt(k);
                                boundIndexes.push_back(k);
                            }
                        }

                        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                        for(unsigned k : boundIndexes){
                            *out << k << "_";
                        }
                        *out << ".getValues({"<<boundTerms<<"});\n";

                        *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<l->getPredicateName()<<"_";
                        for(unsigned k : boundIndexes){
                            *out << k << "_";
                        }
                        *out << ".getValues({"<<boundTerms<<"});\n";
                        *out << ind << "bool undef"<<litIndex<<"=false;\n";
                        *out << ind++ << "for(int i=0;i<tuples->size()+tuplesU->size();i++){\n";
                            *out << ind << "const Tuple* tuple"<<litIndex<<"=NULL;\n";
                            *out << ind++ << "if(i<tuples->size()){\n";
                                *out << ind << "tuple"<<litIndex<<"=tuples->at(i);\n";
                            *out << --ind << "}else{\n";
                                *out << ++ind << "tuple"<<litIndex<<"=tuplesU->at(i-tuples->size());\n";
                                *out << ind << "undef"<<litIndex<<"=true;\n";
                            *out << --ind << "}\n";
                            for(unsigned k=0;k<l->getAriety();k++){
                                if(l->isVariableTermAt(k) && boundVariables.count(l->getTermAt(k))==0){
                                    *out << ind << "int "<<l->getTermAt(k)<<" = tuple"<<litIndex<<"->at("<<k<<");\n";
                                    boundVariables.insert(l->getTermAt(k));
                                }
                            }
                            if(checkTupleFormat(*l,"tuple"+std::to_string(litIndex),true))
                                closingPars++;
                            if(predicateSigns.count(l->getPredicateName())!=0){
                                for(auto negatedLit : predicateSigns[l->getPredicateName()]){
                                    if(negatedLit.first != l->isNegated()){
                                        const aspc::Literal* ll = &auxBody->second[negatedLit.second];
                                        *out << ind++ << "if(";
                                        if(ll->getAriety() > 0 && ll->getAriety() == l->getAriety()){
                                            for(unsigned k=0;k<l->getAriety();k++){
                                                if(k>0)
                                                    *out << " || ";
                                                if(!ll->isNegated())
                                                    *out << "tuple"<<litIndex<<"->at("<<k<<") != tuple"<<negatedLit.second<<"->at("<<k<<")";
                                                else
                                                    *out << "tuple"<<litIndex<<"->at("<<k<<") != negativeTuple"<<negatedLit.second<<".at("<<k<<")";
                                            }
                                        }else if(ll->getAriety() == l->getAriety()){
                                            *out << "false";
                                        }
                                        *out << "){\n";
                                            closingPars++;
                                    }
                                }
                            }
                            closingPars++;

                    }
                    predicateSigns[l->getPredicateName()].push_back({l->isNegated(),litIndex});
                }
            }
            if(visitedLiterals.size()>0){
                if(visitedRelations.size()<auxToInequality[auxPred].size()){
                    ineqIndex=0;
                    for(const aspc::ArithmeticRelation& ineq : auxToInequality[auxPred]){
                        if(ineq.isBoundedRelation(boundVariables) && visitedRelations.count(ineqIndex)==0){
                            *out << ind++ << "if("<<ineq.getStringRep()<<"){\n";
                            visitedRelations.insert(ineqIndex);
                            closingPars++;

                        }else if(ineq.isBoundedValueAssignment(boundVariables) && visitedRelations.count(ineqIndex)==0){
                            *out << ind << "int "<<ineq.getAssignedVariable(boundVariables)<<" = "<<ineq.getAssignmentStringRep(boundVariables)<<";\n";
                            boundVariables.insert(ineq.getAssignedVariable(boundVariables));
                            visitedRelations.insert(ineqIndex);
                        }
                        ineqIndex++;
                    }
                }
                aspc::Literal aux(false,aspc::Atom(auxBody->first,builder->getAuxPredicateTerms(auxBody->first)));
                std::string auxTerms;
                // std::cout << "bound literal "<<aux.getAriety()<<std::endl;
                for(unsigned k=0;k<aux.getAriety();k++){
                    if(k>0)
                        auxTerms += ",";
                    auxTerms += aux.getTermAt(k);
                }
                *out << ind << "Tuple aux({"<<auxTerms<< "}, &_"<<aux.getPredicateName()<<");\n";

                // *out << ind++ << "if(";
                // for(unsigned litIndex=0;litIndex<visitedLiterals.size();litIndex++){
                //     if(litIndex>0)
                //         *out << " || ";
                //     *out << "undef"<<litIndex;
                // }
                // *out << "){\n";

                    *out << ind++ << "if(u"<<aux.getPredicateName()<<".find(aux) == NULL){\n";
                        *out << ind << "const auto& insertResult = u"<<aux.getPredicateName()<<".insert(Tuple({"<<auxTerms<<"},&_"<<aux.getPredicateName()<<"));\n";
                        *out << ind++ << "if (insertResult.second) {\n";
                            *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aux.getPredicateName()<<"]) {\n";
                                *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                            *out << --ind << "}\n";
                            *out << ind << "atomsTable.push_back(aux);\n";
                            *out << ind << "tupleToVar[aux]=atomsTable.size()-1;\n";
                            // *out << ind << "aux.print();std::cout<<\" \"<<tupleToVar[aux]<<std::endl;\n";
                            for(const aspc::Rule& r : program.getRules()){
                                if(!r.isConstraint() && !r.getBodyLiterals().empty() && r.getBodyLiterals()[0].getPredicateName()==auxPred){
                                    const aspc::Atom* head = &r.getHead()[0];
                                    std::string headTerms="";
                                    for(unsigned k=0; k<head->getAriety();k++){
                                        if(headTerms!="")
                                            headTerms+=",";
                                        headTerms+=head->getTermAt(k);
                                    }
                                    *out << ind++ << "{\n";
                                        *out << ind << "Tuple head({"<<headTerms<<"},&_"<<head->getPredicateName()<<");\n";
                                        *out << ind++ << "if(u"<<head->getPredicateName()<<".find(head)==NULL){\n";
                                            *out << ind << "const auto& headInsertResult = u"<<head->getPredicateName()<<".insert(Tuple({"<<headTerms<<"},&_"<<head->getPredicateName()<<"));\n";
                                            *out << ind++ << "if (headInsertResult.second) {\n";
                                                *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                                    *out << ind << "auxMap -> insert2(*headInsertResult.first);\n";
                                                *out << --ind << "}\n";
                                                *out << ind << "atomsTable.push_back(head);\n";
                                                *out << ind << "tupleToVar[head]=atomsTable.size()-1;\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        for(const aspc::Rule& aggr_r : program.getRules()){
                                            if(!aggr_r.isConstraint() && aggr_r.containsAggregate() && !aggr_r.getBodyLiterals().empty() && aggr_r.getBodyLiterals()[0].getPredicateName() == head->getPredicateName()){
                                                const aspc::Atom* aggr_id = &aggr_r.getHead()[0];
                                                std::string aggrIdTerms="";
                                                for(unsigned k=0; k<aggr_id->getAriety();k++){
                                                    if(aggrIdTerms!="")
                                                        aggrIdTerms+=",";
                                                    aggrIdTerms+=aggr_id->getTermAt(k);
                                                }

                                                *out << ind << "Tuple aggr_id"<<aggr_r.getRuleId()<<"({"<<aggrIdTerms<<"},&_"<<aggr_id->getPredicateName()<<");\n";
                                                *out << ind++ << "if(u"<<aggr_id->getPredicateName()<<".find(aggr_id"<<aggr_r.getRuleId()<<")==NULL){\n";
                                                    *out << ind << "const auto& aggrIdInsertResult = u"<<aggr_id->getPredicateName()<<".insert(Tuple({"<<aggrIdTerms<<"},&_"<<aggr_id->getPredicateName()<<"));\n";
                                                    *out << ind++ << "if (aggrIdInsertResult.second) {\n";
                                                        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr_id->getPredicateName()<<"]) {\n";
                                                            *out << ind << "auxMap -> insert2(*aggrIdInsertResult.first);\n";
                                                        *out << --ind << "}\n";
                                                        *out << ind << "atomsTable.push_back(aggr_id"<<aggr_r.getRuleId()<<");\n";
                                                        *out << ind << "tupleToVar[aggr_id"<<aggr_r.getRuleId()<<"]=atomsTable.size()-1;\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            }
                                        }
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
            *out << --ind << "}//closing aux generation\n";
        }

        for(const auto & aggrId : aggrIdToRule){
            if(program.getRule(aggrId.second).getBodyLiterals().empty()){
                *out << ind++ << "{\n";
                    *out << ind << "Tuple aggrId({},&_"<<aggrId.first<<");\n";
                    *out << ind << "const auto& insertResult = u"<<aggrId.first<<".insert(Tuple({},&_"<<aggrId.first<<"));\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggrId.first<<"]) {\n";
                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                        *out << --ind << "}\n";
                        *out << ind << "atomsTable.push_back(aggrId);\n";
                        *out << ind << "tupleToVar[aggrId]=atomsTable.size()-1;\n";
                        // *out << ind << "aggrId.print();std::cout<<\" \"<<tupleToVar[aggrId]<<std::endl;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            }else{
                const aspc::Literal* bodyLit = &program.getRule(aggrId.second).getBodyLiterals()[0];
                const aspc::Atom* head = &program.getRule(aggrId.second).getHead()[0];
                std::string terms="";
                for(unsigned i = 0; i<head->getAriety(); i++){
                    if(!head->isVariableTermAt(i)){
                        if(terms!="")
                            terms+=",";
                        terms+=head->getTermAt(i);
                        continue;
                    }
                    for(unsigned j = 0; j<bodyLit->getAriety(); j++){
                        if(bodyLit->isVariableTermAt(j) && head->getTermAt(i)==bodyLit->getTermAt(j)){
                            if(terms!="")
                                terms+=",";
                            terms+="tuple->at("+std::to_string(j)+")";
                            break;
                        }
                    }
                }

                if(!builder->isBodyPredicate(bodyLit->getPredicateName())){
                    *out << ind++ << "{\n";
                        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<bodyLit->getPredicateName()<<"_.getValues({});\n";
                        *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<bodyLit->getPredicateName()<<"_.getValues({});\n";
                        *out << ind++ << "for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){\n";
                            *out << ind << "const Tuple* tuple = NULL;\n";
                            *out << ind++ << "if(i<tuples->size()){\n";
                                *out << ind << "tuple=tuples->at(i);\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                *out << ind << "tuple=tuplesU->at(i-tuples->size());\n";
                            *out << --ind << "}\n";
                            bool checkFormat = checkTupleFormat(*bodyLit,"tuple",true);
                                *out << ind << "Tuple head({"<<terms<<"},&_"<<head->getPredicateName()<<");\n";
                                *out << ind << "const auto& insertResult = u"<<head->getPredicateName()<<".insert(Tuple({"<<terms<<"},&_"<<head->getPredicateName()<<"));\n";
                                *out << ind++ << "if (insertResult.second) {\n";
                                    *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "atomsTable.push_back(head);\n";
                                    *out << ind << "tupleToVar[head]=atomsTable.size()-1;\n";
                                    // *out << ind << "head.print();std::cout<<\" \"<<tupleToVar[head]<<std::endl;\n";
                                *out << --ind << "}\n";

                            if(checkFormat)
                                *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                }
            }
        }

        for(const aspc::Rule& r : program.getRules()){
            if(!r.isConstraint() && !r.containsAggregate() && r.getBodyLiterals().size() == 1 && !builder->isAuxPredicate(r.getBodyLiterals()[0].getPredicateName())){
                const aspc::Literal* bodyLit = &r.getBodyLiterals()[0];
                const aspc::Atom* head = &r.getHead()[0];
                std::string terms="";
                for(unsigned i = 0; i<head->getAriety(); i++){
                    if(!head->isVariableTermAt(i)){
                        if(terms!="")
                            terms+=",";
                        terms+=head->getTermAt(i);
                        continue;
                    }
                    for(unsigned j = 0; j<bodyLit->getAriety(); j++){
                        if(bodyLit->isVariableTermAt(j) && head->getTermAt(i)==bodyLit->getTermAt(j)){
                            if(terms!="")
                                terms+=",";
                            terms+="tuple->at("+std::to_string(j)+")";
                            break;
                        }
                    }
                }
                *out << ind++ << "{\n";
                    *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<bodyLit->getPredicateName()<<"_.getValues({});\n";
                    *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<bodyLit->getPredicateName()<<"_.getValues({});\n";
                    *out << ind++ << "for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){\n";
                        *out << ind << "const Tuple* tuple = NULL;\n";
                        *out << ind++ << "if(i<tuples->size()){\n";
                            *out << ind << "tuple=tuples->at(i);\n";
                            bool checkFormat = checkTupleFormat(*bodyLit,"tuple",true);
                            *out << ind << "Tuple head({"<<terms<<"},&_"<<head->getPredicateName()<<");\n";
                            *out << ind << "const auto& insertResult = w"<<head->getPredicateName()<<".insert(Tuple({"<<terms<<"},&_"<<head->getPredicateName()<<"));\n";
                            *out << ind++ << "if (insertResult.second) {\n";
                                *out << ind++ << "for (AuxMap* auxMap : predicateToAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                    *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                *out << --ind << "}\n";
                                *out << ind << "atomsTable.push_back(head);\n";
                                *out << ind << "tupleToVar[head]=atomsTable.size()-1;\n";
                                // *out << ind << "aggrId.print();std::cout<<\" \"<<tupleToVar[aggrId]<<std::endl;\n";
                            *out << --ind << "}\n";
                            if(checkFormat)
                                *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            *out << ind << "tuple=tuplesU->at(i-tuples->size());\n";
                            checkFormat = checkTupleFormat(*bodyLit,"tuple",true);
                            
                            *out << ind << "Tuple head({"<<terms<<"},&_"<<head->getPredicateName()<<");\n";
                            *out << ind << "const auto& insertResult = u"<<head->getPredicateName()<<".insert(Tuple({"<<terms<<"},&_"<<head->getPredicateName()<<"));\n";
                            *out << ind++ << "if (insertResult.second) {\n";
                                *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                    *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                *out << --ind << "}\n";
                                *out << ind << "atomsTable.push_back(head);\n";
                                *out << ind << "tupleToVar[head]=atomsTable.size()-1;\n";
                                // *out << ind << "aggrId.print();std::cout<<\" \"<<tupleToVar[aggrId]<<std::endl;\n";
                            *out << --ind << "}\n";
                            if(checkFormat)
                                *out << --ind << "}\n";
                        *out << --ind << "}\n";
                        //save aggr_id if new body is saved
                        for(const aspc::Rule& aggr_id_rule : program.getRules()){
                            if(!aggr_id_rule.isConstraint() && aggr_id_rule.containsAggregate() && !aggr_id_rule.getBodyLiterals().empty() && aggr_id_rule.getBodyLiterals()[0].getPredicateName() == head->getPredicateName()){
                                const aspc::Atom* aggr_id = &aggr_id_rule.getHead()[0];
                                *out << ind++ << "{\n";
                                checkFormat = checkTupleFormat(*bodyLit,"tuple",true);
                                    *out << ind << "Tuple aggrId({"<<terms<<"},&_"<<aggr_id->getPredicateName()<<");\n";
                                    *out << ind << "const auto& insertResult = u"<<aggr_id->getPredicateName()<<".insert(Tuple({"<<terms<<"},&_"<<aggr_id->getPredicateName()<<"));\n";
                                    *out << ind++ << "if (insertResult.second) {\n";
                                        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr_id->getPredicateName()<<"]) {\n";
                                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "atomsTable.push_back(aggrId);\n";
                                        *out << ind << "tupleToVar[aggrId]=atomsTable.size()-1;\n";
                                    *out << --ind << "}\n";
                                if(checkFormat)
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            }
                        }
                    *out << --ind << "}\n";
                *out << --ind << "}\n";

            }
        }
        for(const auto& aggrSetPred : aggrSetToRule){
            for(unsigned ruleId : aggrSetPred.second){
                const aspc::Rule* rule = &program.getRules()[ruleId];
                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                if(aggregateRelation->getAggregate().isSum()){
                    const aspc::Atom* aggrId = &rule->getHead()[0];
                    const aspc::Literal* aggrSet = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                    unsigned sumVar=0;
                    if(!builder->isAggrSetPredicate(aggrSetPred.first)){
                        std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
                        for(unsigned i=0;i<aggrSet->getAriety();i++){
                            if(aggrSet->isVariableTermAt(i) && aggrSet->getTermAt(i)==firstAggrVar){
                                sumVar=i;
                                break;
                            }
                        }
                    }
                    *out << ind++ << "{\n";
                        *out << ind << "const std::vector<const Tuple*>* aggregateIds = &u"<<aggrId->getPredicateName()<<"_.getValues({});\n";
                        *out << ind++ << "for(unsigned i=0;i<aggregateIds->size();i++){\n";
                            *out << ind << "auto it = tupleToVar.find(*aggregateIds->at(i));\n";
                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                *out << ind << "const std::vector<const Tuple*>* aggrSetTuples = &u"<<aggrSetPred.first<<"_";
                                for(unsigned k : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                                    *out << k << "_";
                                }
                                *out << ".getValues({";
                                for(unsigned k : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                                    *out << "aggregateIds->at(i)->at("<<k<<")";
                                    if(k != sharedVarAggrIdAggrSet[aggrId->getPredicateName()].back()){
                                        *out << ",";
                                    }
                                }
                                *out << "});\n";
                                *out << ind++ << "for(unsigned j=0; j<aggrSetTuples->size(); j++)\n";
                                    *out << ind-- << "possibleSum[it->second]+=aggrSetTuples->at(j)->at("<<sumVar<<");\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";

                }
            }
        }
        // *out << ind++ << "for(auto pair : actualSum){\n";
        //     *out << ind << "atomsTable[pair.first].print();\n";
        //     *out << ind << "std::cout<<\" ActualSum \"<<pair.second<<std::endl;\n";
        // *out << --ind <<"}\n";
        // *out << ind++ << "for(auto pair : possibleSum){\n";
        //     *out << ind << "atomsTable[pair.first].print();\n";
        // *out << ind << "std::cout<<\"PossibleSum \"<<pair.second<<std::endl;\n";
        // *out << --ind <<"}\n";
    *out << --ind << "}\n";

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
    // *out << ind << "propagatedLiterals.clear();\n";
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
                *out << ind << "f" << auxSet << ".clear();\n";
            }
        }
    }

    *out << --ind << "}\n";

    // ---------------------- end clear() --------------------------------------//

    // ---------------------- init() --------------------------------------//
    *out << ind++ << "void Executor::init() {\n";
    // *out << ind << "std::cout<<\"Init\"<<std::endl;\n";
    // COMMENTED FOR INCOMPATIBILITIES
    // if (program.hasConstraint()) {
    //     *out << ind << "createFunctionsMap();\n";
    // }
    string reference = (mode == EAGER_MODE) ? "&" : "";

    for (const pair<std::string, unsigned>& predicate : predicates) {

        *out << ind << "predicateWSetMap[" << reference << "_" << predicate.first << "]=&w" << predicate.first << ";\n";
        if (mode == EAGER_MODE) {
            *out << ind << "predicateUSetMap[&_" << predicate.first << "]=&u" << predicate.first << ";\n";
            *out << ind << "predicateFSetMap[&_" << predicate.first << "]=&f" << predicate.first << ";\n";
        }
        *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = &_" << predicate.first << ";\n";
    }
    for (const pair<std::string, unsigned>& predicate : aggregatePredicates) {
        if(predicates.count(predicate)==0){
            *out << ind << "predicateWSetMap[" << reference << "_" << predicate.first << "]=&w" << predicate.first << ";\n";
            if (mode == EAGER_MODE) {
                *out << ind << "predicateUSetMap[&_" << predicate.first << "]=&u" << predicate.first << ";\n";
                *out << ind << "predicateFSetMap[&_" << predicate.first << "]=&f" << predicate.first << ";\n";
            }
            *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = &_" << predicate.first << ";\n";
        }
    }
    // for(aspc::Rule& r :program.getRules()){
    //     if(!r.isConstraint() && r.containsAggregate()){
    //         std::string predName = r.getBodyLiterals()[0].getPredicateName();
    //         *out << ind << "sharedVariables[&_"<<predName<<"]=&"<<sharedVarToAggr[predName]<<";\n";
    //         *out << ind << "sharedVarWAggr[&_"<<predName<<"]=&w"<<sharedVarToAggr[predName]<<";\n";
    //         *out << ind << "sharedVarUAggr[&_"<<predName<<"]=&u"<<sharedVarToAggr[predName]<<";\n";
    //         *out << ind << "sharedVarFAggr[&_"<<predName<<"]=&f"<<sharedVarToAggr[predName]<<";\n";
    //     }
    // }



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
    // for(std::string aggrSetPred : sumAggrSetPredicate){
    //     // *out << ind << "aggr_setPredicate.insert(&_"<<aggrSetPred<<");\n";
    //     for(auto mapName : sumAggrSetPredicateToAggrId[aggrSetPred]){
    //         if(mapName.first!=""){
    //             // *out << ind << "sumAggrIdForAggrSetAuxMap[&_"<<aggrSetPred<<"].push_back(&p"<<mapName.first<<");\n";
    //             // *out << ind << "sumAggrIdForAggrSetUAuxMap[&_"<<aggrSetPred<<"].push_back(&u"<<mapName.first<<");\n";
    //             // *out << ind << "sumAggrIdForAggrSetFAuxMap[&_"<<aggrSetPred<<"].push_back(&f"<<mapName.first<<");\n";
    //         }
    //         // else{
    //         //     *out << ind << "sumAggrIdForAggrSet[&_"<<aggrSetPred<<"].push_back(&w"<<mapName.second<<");\n";
    //         //     *out << ind << "sumAggrIdForAggrSetU[&_"<<aggrSetPred<<"].push_back(&u"<<mapName.second<<");\n";
    //         // }
    //     }
    // }
    *out << --ind << "}\n";
    // ---------------------- end init() --------------------------------------//
    *out << ind++ << "bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,UnorderedSet<int> & propagatedLiterals){\n";
        std::string internalIf;
        for(const auto& predId : predicateIDs){
            if(builder->isAuxPredicate(predId.first) || headPreds.count(predId.first)!=0){
                if(internalIf!="")
                    internalIf+=" || ";
                internalIf += "tupleU->getPredicateName() == &_"+predId.first;

            }
        }
        if(internalIf=="")
            internalIf="false";
        *out << ind++ << "if("<<internalIf<<"){\n";
            *out << ind << "bool propagated=false;\n";
            *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator falseSet = predicateFSetMap.find(tupleU->getPredicateName());\n";
            *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator undefSet = predicateUSetMap.find(tupleU->getPredicateName());\n";
            *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator trueSet = predicateWSetMap.find(tupleU->getPredicateName());\n";

            *out << ind++ << "if(falseSet==predicateFSetMap.end()){\n";
                *out << ind << "std::cout<<\"Unable to find false set for: \"<<tupleU->getPredicateName()<<std::endl;\n";
                *out << ind << "exit(180);\n";
            *out << -- ind << "}\n";

            *out << ind++ << "if(undefSet==predicateUSetMap.end()){\n";
                *out << ind << "std::cout<<\"Unable to find undef set for: \"<<tupleU->getPredicateName()<<std::endl;\n";
                *out << ind << "exit(180);\n";
            *out << -- ind << "}\n";

            *out << ind++ << "if(trueSet==predicateWSetMap.end()){\n";
                *out << ind << "std::cout<<\"Unable to find true set for: \"<<tupleU->getPredicateName()<<std::endl;\n";
                *out << ind << "exit(180);\n";
            *out << -- ind << "}\n";
            *out << ind++ << "if(isNegated == asNegative){\n";
                *out << ind++ << "if(falseSet->second->find(*tupleU)!=NULL){\n";
                    // *out << ind << "std::cout<<\"Conflict: Literal is already false\"<<std::endl;\n";
                    *out << ind << "return true;\n";
                *out << --ind << "}else if(undefSet->second->find(*tupleU)!=NULL){\n";
                ind++;
                    *out << ind << "const auto& insertResult = trueSet->second->insert(Tuple(*tupleU));\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        *out << ind++ << "for (AuxMap* auxMap : predicateToAuxiliaryMaps[trueSet->first]) {\n";
                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                        *out << --ind << "}\n";
                    
                        for(const auto& aggrSetPred : aggrSetToRule){
                            for(unsigned ruleId : aggrSetPred.second){
                                const aspc::Rule* rule = &program.getRules()[ruleId];
                                const aspc::Atom* aggrId = &rule->getHead()[0];
                                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                                const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                                unsigned sumVar = 0;
                                if(!aggregateRelation->getAggregate().isSum())
                                    continue;
                                if(!builder->isAggrSetPredicate(aggrSetPred.first)){
                                    std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                                    for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                                        if(aggrSetLit->getTermAt(i)==var){
                                            sumVar=i;
                                            break;
                                        }
                                    }
                                }
                                *out << ind++ << "if(tupleU->getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                                    if(aggrId->getAriety() == 0){
                                        *out << ind << "auto itAggrId = tupleToVar.find(Tuple({},&_"<<aggrId->getPredicateName()<<"));\n";
                                        *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                            *out << ind << "actualSum[itAggrId->second]+=tupleU->at("<<sumVar<<");\n";
                                            *out << ind << "possibleSum[itAggrId->second]-=tupleU->at("<<sumVar<<");\n";
                                        *out << --ind << "}\n";
                                    }else{
                                        std::string terms = "";
                                        unsigned varIndex = 0;
                                        for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                                            if(varIndex>0){
                                                terms+=",";
                                            }
                                            terms+="tupleU->at("+std::to_string(var)+")";
                                            varIndex++;
                                        }
                                        std::string mapName = aggrId->getPredicateName()+"_";
                                        for(unsigned var : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                                            mapName+=std::to_string(var)+"_";
                                        }
                                        for(std::string sign : {"p","u","f"}){
                                            *out << ind++ << "{\n";
                                                *out << ind << "const std::vector<const Tuple*>* aggrIds = &"<<sign<<mapName<<".getValues({"<<terms<<"});\n";
                                                *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                                    *out << ind << "auto itAggrId = tupleToVar.find(*aggrIds->at(i));\n";
                                                    *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                                        *out << ind << "actualSum[itAggrId->second]+=tupleU->at("<<sumVar<<");\n";
                                                        *out << ind << "possibleSum[itAggrId->second]-=tupleU->at("<<sumVar<<");\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";            
                                            *out << --ind << "}\n";
                                        }
                                    }                                
                                *out << --ind << "}\n";
                            }
                        }
                        // *out << ind << "std::cout<<\"Literal propagated as True\";";
                        // *out << ind << "tupleU->print();\n";
                        // *out << ind << "std::cout<<std::endl;\n";
                        *out << ind << "propagated = true;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}else{\n";
            ind++;
                *out << ind++ << "if(trueSet->second->find(*tupleU)!=NULL){\n";
                    // *out << ind << "std::cout<<\"Conflict: Literal is already true \";tupleU->print();std::cout<<std::endl;\n";
                    *out << ind << "return true;\n";
                *out << --ind << "}else if(undefSet->second->find(*tupleU)!=NULL){\n";
                ind++;
                    *out << ind << "const auto& insertResult = falseSet->second->insert(Tuple(*tupleU));\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        *out << ind++ << "for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[falseSet->first]) {\n";
                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                        *out << --ind << "}\n";
                        for(const auto& aggrSetPred : aggrSetToRule){
                            for(unsigned ruleId : aggrSetPred.second){
                                const aspc::Rule* rule = &program.getRules()[ruleId];
                                const aspc::Atom* aggrId = &rule->getHead()[0];
                                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                                const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                                unsigned sumVar = 0;
                                if(!aggregateRelation->getAggregate().isSum())
                                    continue;
                                
                                if(!builder->isAggrSetPredicate(aggrSetPred.first)){
                                    std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                                    for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                                        if(aggrSetLit->getTermAt(i)==var){
                                            sumVar=i;
                                            break;
                                        }
                                    }
                                }
                                *out << ind++ << "if(tupleU->getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                                    if(aggrId->getAriety() == 0){
                                        *out << ind << "auto itAggrId = tupleToVar.find(Tuple({},&_"<<aggrId->getPredicateName()<<"));\n";
                                        *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                            *out << ind << "possibleSum[itAggrId->second]-=tupleU->at("<<sumVar<<");\n";
                                        *out << --ind << "}\n";
                                    }else{
                                        std::string terms = "";
                                        unsigned varIndex = 0;
                                        for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                                            if(varIndex>0){
                                                terms+=",";
                                            }
                                            terms+="tupleU->at("+std::to_string(var)+")";
                                            varIndex++;
                                        }
                                        std::string mapName = aggrId->getPredicateName()+"_";
                                        for(unsigned var : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                                            mapName+=std::to_string(var)+"_";
                                        }
                                        for(std::string sign : {"p","u","f"}){
                                            *out << ind++ << "{\n";
                                                *out << ind << "const std::vector<const Tuple*>* aggrIds = &"<<sign<<mapName<<".getValues({"<<terms<<"});\n";
                                                *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                                    *out << ind << "auto itAggrId = tupleToVar.find(*aggrIds->at(i));\n";
                                                    *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                                        *out << ind << "possibleSum[itAggrId->second]-=tupleU->at("<<sumVar<<");\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";            
                                            *out << --ind << "}\n";
                                        }
                                    }                                
                                *out << --ind << "}\n";
                            }
                        }
                        // *out << ind << "std::cout<<\"Literal propagated as False\";";
                        // *out << ind << "tupleU->print();\n";
                        // *out << ind << "std::cout<<std::endl;\n";
                        *out << ind << "propagated = true;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
            *out << ind++ << "if(propagated){\n";
                *out << ind << "auto it = tupleToVar.find(*tupleU);\n";
                *out << ind << "int sign = isNegated != asNegative ? -1 : 1;\n";
                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                    *out << ind << "stack.push_back(sign*it->second);\n";
                    *out << ind << "levelToIntLiterals[currentDecisionLevel].push_back(sign*it->second);\n";
                *out << --ind << "}\n";
                *out << ind << "undefSet->second->erase(*tupleU);\n";
            *out << --ind << "}\n";
        *out << --ind << "}else{\n";
        ind++;
            *out << ind << "auto it = tupleToVar.find(*tupleU);\n";
            *out << ind << "int sign = isNegated == asNegative ? -1 : 1;\n";
            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                // *out << ind << "std::cout<<\"Propagating external literal: \";\n";
                // *out << ind << "tupleU->print();\n";
                // *out << ind << "std::cout <<\" \"<<sign*it->second<<std::endl;\n";
                *out << ind << "propagatedLiterals.insert(it->second*sign);\n";
            *out << --ind << "}\n";

        *out << --ind << "}\n";
        *out << ind << "return false;\n";
    *out << --ind << "}\n";

    *out << ind++ << "void Executor::printInternalLiterals(){\n";
        for(std::string pred : builder->getPrintingPredicates()){
            *out << ind++ << "for(const Tuple* t : w"<<pred<<".getTuples()){\n";
                *out << ind << "t->print();\n";
                *out << ind << "std::cout<<std::endl;\n";
            *out << --ind << "}\n";
        }
    *out << --ind << "}\n";
    *out << ind++ << "void Executor::unRollToLevel(int decisionLevel){\n";
        // *out << ind << "std::cout<<\"Unrolling to level: \"<<decisionLevel << \" \" <<currentDecisionLevel<<std::endl;\n";
        *out << ind++ << "for(unsigned i = 0; i<propagatedLiterals.size(); i++)\n";
            *out << ind-- << "reasonForLiteral.erase(-propagatedLiterals[i]);\n";
        *out << ind << "propagatedLiterals.clear();\n";
        *out << ind++ << "while(currentDecisionLevel > decisionLevel){\n";
            // *out << ind << "std::cout<<\"clear level: \"<<currentDecisionLevel<<std::endl;\n";
            // *out << ind << "levelToExtLiterals.erase(currentDecisionLevel);\n";
            *out << ind++ << "while(!levelToIntLiterals[currentDecisionLevel].empty()){\n";
                *out << ind << "int var = levelToIntLiterals[currentDecisionLevel].back();\n";
                *out << ind << "levelToIntLiterals[currentDecisionLevel].pop_back();\n";
                *out << ind << "reasonForLiteral.erase(var);\n";
                // *out << ind++ << "if(supportedLiterals[var] >= currentDecisionLevel)\n";
                //     *out << ind-- << "supportedLiterals.erase(var);\n";
                *out << ind << "int uVar = var>0 ? var : -var;\n";
                *out << ind << "Tuple tuple = atomsTable[uVar];\n";

                *out << ind++ << "if (var > 0) {\n";
                    *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple.getPredicateName());\n";
                    *out << ind++ << "if (wSetIt != predicateWSetMap.end()) {\n";
                        // *out << ind << "std::cout<<\"Removing true literal\"<<std::endl;\n";
                        *out << ind << "wSetIt->second->erase(tuple);\n";
                    *out << --ind << "}\n";
                *out << --ind << "} //true removing\n";

                *out << ind++ << "if (var < 0) {\n";
                    *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple.getPredicateName());\n";
                    *out << ind++ << "if (fSetIt != predicateFSetMap.end()) {\n";
                        // *out << ind << "std::cout<<\"Removing false literal\"<<std::endl;\n";
                        *out << ind << "fSetIt->second->erase(tuple);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}//false removing\n";

                *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple.getPredicateName());\n";
                *out << ind++ << "if (it == predicateUSetMap.end()) {\n";
                *out << ind << "} else {\n";
                    *out << ind << "const auto& insertResult = it->second->insert(Tuple(tuple));\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                    // *out << ind << "std::cout<<\"Saving undef literal\"<<std::endl;\n";
                        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[it->first]) {\n";
                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                *out << --ind << "} // close undef insert \n";
                for(const auto& aggrSetPred : aggrSetToRule){
                    for(unsigned ruleId : aggrSetPred.second){
                        const aspc::Rule* rule = &program.getRules()[ruleId];
                        const aspc::Atom* aggrId = &rule->getHead()[0];
                        const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                        const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                        unsigned sumVar = 0;
                        if(!aggregateRelation->getAggregate().isSum())
                            continue;
                        if(!builder->isAggrSetPredicate(aggrSetPred.first)){
                            std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                            for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                                if(aggrSetLit->getTermAt(i)==var){
                                    sumVar=i;
                                    break;
                                }
                            }
                        }
                        *out << ind++ << "if(tuple.getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                            if(aggrId->getAriety() == 0){
                                *out << ind << "auto itAggrId = tupleToVar.find(Tuple({},&_"<<aggrId->getPredicateName()<<"));\n";
                                *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                    *out << ind++ << "if(var>0)\n";
                                        *out << ind-- << "actualSum[itAggrId->second]-=tuple["<<sumVar<<"];\n";
                                    *out << ind << "possibleSum[itAggrId->second]+=tuple["<<sumVar<<"];\n";
                                *out << --ind << "}\n";
                            }else{
                                std::string terms = "";
                                unsigned varIndex = 0;

                                for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                                    if(varIndex > 0){
                                        terms+=",";
                                    }
                                    terms+="tuple["+std::to_string(var)+"]";
                                    varIndex++;
                                }
                                std::string mapName = aggrId->getPredicateName()+"_";
                                for(unsigned var : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                                    mapName+=std::to_string(var)+"_";
                                }
                                for(std::string sign : {"p","u","f"}){
                                    *out << ind++ << "{\n";
                                        *out << ind << "const std::vector<const Tuple*>* aggrIds = &"<<sign<<mapName<<".getValues({"<<terms<<"});\n";
                                        *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                            *out << ind << "auto itAggrId = tupleToVar.find(*aggrIds->at(i));\n";
                                            *out << ind++ << "if(itAggrId != tupleToVar.end()){\n";
                                                *out << ind++ << "if(var>0)\n";
                                                    *out << ind-- << "actualSum[itAggrId->second]-=tuple["<<sumVar<<"];\n";
                                                *out << ind << "possibleSum[itAggrId->second]+=tuple["<<sumVar<<"];\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";            
                                    *out << --ind << "}\n";
                                }
                            }                                
                        *out << --ind << "}\n";
                    }
                }
            *out << --ind << "}\n";
            *out << ind << "levelToIntLiterals.erase(currentDecisionLevel);\n";
            *out << ind << "currentDecisionLevel--;\n";

        *out << --ind << "}\n";
        *out << ind << "clearConflictReason();\n";
        // *out << ind << "std::cout<<\"End unroll\"<<std::endl;\n";
        // *out << ind << "for(const Tuple* t :waux0.getTuples()){std::cout<<\"True aux: \";t->print();std::cout<<std::endl;}\n";
        // *out << ind << "for(const Tuple* t :faux0.getTuples()){std::cout<<\"False aux: \";t->print();std::cout<<std::endl;}\n";
        // *out << ind << "for(const Tuple* t :uaux0.getTuples()){std::cout<<\"Undef aux: \";t->print();std::cout<<std::endl;}\n";

    *out << --ind << "}\n";
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
        // *out << ind++ << "if(currentDecisionLevel > decisionLevel || unRoll)\n";
        //     *out << ind-- << "unRollToLevel(decisionLevel);\n";
        *out << ind << "currentDecisionLevel=decisionLevel;\n";
        // *out << ind << "std::cout<<\"Current Decision Level: \"<<currentDecisionLevel<<std::endl;\n";
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
        *out << ind << "std::vector<int> propagationStack;\n";
        *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
            // *out << ind << "std::cout<<\"facts: \"<<facts[i]<<std::endl;\n";
            *out << ind << "onLiteralTrue(facts[i]);\n";
            *out << ind << "propagationStack.push_back(facts[i]);\n";
            *out << ind << "externalLiteralsLevel[facts[i]]=currentDecisionLevel;\n";
            *out << ind << "if(propagatedLiterals.contains(-facts[i])) propagatedLiterals.erase(-facts[i]);\n";
            // *out << ind << "std::cout<<\"current level size \"<<levelToExtLiterals[currentDecisionLevel].size()<<std::endl;\n";
            // *out << ind << "levelToExtLiterals[currentDecisionLevel].push_back(facts[i]);\n";

        *out << --ind << "}\n";
    }

    if (mode == LAZY_MODE) {
        //declare iterators
        for (const pair<std::string, unsigned>& predicate : predicates) {
            *out << ind << "unsigned index_" << predicate.first << "=0;\n";
        }

        for (unsigned i = 0; i < sccsSize; i++) {
            const std::map<std::string, std::vector<unsigned>>&startersExitRules = starterToExitRulesByComponent[i];
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
        *out << ind << "if(decisionLevel>-1) {\n";
            // *out << ind++ << "for(auto pair : actualSum){\n";
            //     *out << ind << "atomsTable[pair.first].print();\n";
            //     *out << ind << "std::cout<<\" ActualSum \"<<pair.second<<std::endl;\n";
            //     // *out << ind << "if(pair.second>6 || pair.second<0)exit(0);\n";
            // *out << --ind <<"}\n";
            // *out << ind++ << "for(auto pair : possibleSum){\n";
            //     *out << ind << "atomsTable[pair.first].print();\n";
            //     *out << ind << "std::cout<<\"PossibleSum \"<<pair.second<<std::endl;\n";
            //     // *out << ind << "if(pair.second>6 || pair.second<0)exit(0);\n";
            // *out << --ind <<"}\n";
        *out << ind << "}\n";
        *out << ind++ << "if(decisionLevel==-1) {\n";
            *out << ind++ << "if(!undefinedLoaded)\n";
                *out << ind-- << "undefLiteralsReceived();\n";
            std::unordered_set<unsigned> compiledRuleIndices;
            while(compiledRuleIndices.size()<program.getRulesSize()){
                const aspc::Rule* rule = NULL;
                for (const aspc::Rule& r : program.getRules()) {
                    if(compiledRuleIndices.count(r.getRuleId())==0){
                        bool noInternalLiteral = true;
                        for(const aspc::Literal& l : r.getBodyLiterals()){
                            if(builder->isAuxPredicate(l.getPredicateName()) || headPreds.count(l.getPredicateName())!=0){
                                noInternalLiteral=false;
                                break;
                            }
                        }
                        if(noInternalLiteral){
                            rule=&r;
                            break;
                        }else if(r.isConstraint()){
                            rule=&r;
                        }else if(rule==NULL){
                            rule=&r;
                        }
                    }
                }
                compiledRuleIndices.insert(rule->getRuleId());
                compileEagerRule(*rule,false);
            }
        *out << --ind << "}//close decision level == -1\n";
        // *out << ind << "std::cout<<\"outOfDecisionLevel\"<<std::endl;\n";

        // *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
        //     *out << ind << "propagationStack.push_back(facts[i]);\n";
        // *out << --ind << "}\n";
        // *out << ind << "std::cout<<propagatedLiterals.size()<<std::endl;\n";
        *out << ind++ << "while(!propagationStack.empty()){\n";
            *out << ind << "int startVar = propagationStack.back();\n";
            *out << ind << "int uStartVar = startVar<0 ? -startVar : startVar;\n";
            *out << ind << "Tuple starter = atomsTable[uStartVar];\n";
            *out << ind << "starter.setNegated(startVar<0);\n";
            // *out << ind << "starter.print();std::cout<<\" Starter\"<<std::endl;\n";
            *out << ind << "propagationStack.pop_back();\n";
            for(const aspc::Rule& r: program.getRules()){
                compileEagerRule(r,true);
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
    if (start < r.getBodySize()) {
        r.getFormulas().at(start)->addVariablesToSet(boundVariables);

    }else{
        if(start > r.getFormulas().size()){
            for(unsigned k = 0; k < r.getHead()[0].getAriety(); k++){
                if(r.getHead()[0].isVariableTermAt(k)){
                    boundVariables.insert(r.getHead()[0].getTermAt(k));
                }
            }
        }
    }

    const std::vector<unsigned> & joinOrder = r.getOrderedBodyIndexesByStarter(start);
    unsigned i = 1;
    if (start >= r.getBodySize()) {
        i = 0;
    }else{
        const aspc::Literal* li = (aspc::Literal*)r.getFormulas()[joinOrder[0]];
        std::string mapVariableName=li->getPredicateName()+"_";
        std::vector<unsigned> keyIndexes;
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


            *out << ind << "AuxMap f" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";
            predicateToFalseAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);


            predicateToAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);
            if (mode == EAGER_MODE) {
                predicateToUndefAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);
            }
            declaredMaps.insert(mapVariableName);
        }
    }
    for (; i < r.getFormulas().size(); i++) {
        const aspc::Formula* f = r.getFormulas()[joinOrder[i]];
        if (f->isLiteral()) {
            const aspc::Literal * li = (aspc::Literal *) f;
            if (li->isPositiveLiteral() && !li->isBoundedLiteral(boundVariables)) {
                // std::cout<<"Declare map for: ";
                // li->print();
                // std::cout<<std::endl;
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


                    *out << ind << "AuxMap f" << mapVariableName << "({";
                    for (unsigned k = 0; k < keyIndexes.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << keyIndexes[k];
                    }
                    *out << "});\n";


                    predicateToAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);
                    predicateToFalseAuxiliaryMaps[li->getPredicateName()].insert(mapVariableName);
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
void CompilationManager::declareRuleEagerStructures(const aspc::Rule& r){

    if(mode == EAGER_MODE){
        std::unordered_map<std::string,std::pair<std::vector<unsigned>,unsigned>> declaringMaps;
        std::unordered_map<std::string,std::string> mapNames;
        if(!r.isConstraint()){
            if(r.containsAggregate()){

                std::unordered_set<std::string> bodyVars;
                const aspc::Literal* domBody = !r.getBodyLiterals().empty() ?  &r.getBodyLiterals()[0] : NULL;
                const aspc::Literal* aggregate = &r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0];
                const aspc::Atom* aggrId = &r.getHead()[0];
                
                aggrIdToRule[aggrId->getPredicateName()]=r.getRuleId();
                aggrSetToRule[aggregate->getPredicateName()].push_back(r.getRuleId());

                if(r.getArithmeticRelationsWithAggregate()[0].getAggregate().isSum()){
                    sumAggrSetPredicate.insert(aggregate->getPredicateName());
                }
                if(domBody!=NULL){
                    for(unsigned i = 0; i<aggrId->getAriety(); i++){
                        bool found=false;
                        for(unsigned j=0; j<aggregate->getAriety();j++){
                            if(aggregate->getTermAt(j)==aggrId->getTermAt(i)){
                                sharedVarAggrIDToBodyIndices[aggrId->getPredicateName()].push_back(i);
                                sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()].push_back(j);
                                found=true;
                                break;
                            }
                        }
                        if(found){
                            sharedVarAggrIdAggrSet[aggrId->getPredicateName()].push_back(i);
                        }
                    }
                    std::cout<<aggrId->getPredicateName()<<std::endl;
                    for(unsigned v : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                        std::cout<<v << " ";
                    }
                    std::cout<<std::endl;
                }

                for(std::string aggrVar : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateVariables()){
                    for(unsigned j=0; j<aggregate->getAriety();j++){
                        if(aggrVar == aggregate->getTermAt(j)){
                            aggrVarToAggrSetIndices[aggregate->getPredicateName()].push_back(j);
                            break;
                        }
                    }
                }
                std::string mapName = aggrId->getPredicateName()+"_";
                if (!declaredMaps.count(mapName)){
                    *out << ind << "AuxMap p" << mapName << "({});\n";
                    *out << ind << "AuxMap u" << mapName << "({});\n";
                    *out << ind << "AuxMap f" << mapName << "({});\n";
                    predicateToAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                    predicateToUndefAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                    predicateToFalseAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                    declaredMaps.insert(mapName);
                }
                // if(domBody!=NULL && domBody->getAriety() != sharedVarAggrIDToBodyIndices[aggrId->getPredicateName()].size()){
                if(domBody!=NULL){
                    std::string indices="";
                    for(unsigned k = 0; k<aggrId->getAriety(); k++){
                        bool found=false;
                        for(unsigned v: sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                            if(aggregate->isVariableTermAt(v) && aggregate->getTermAt(v)==aggrId->getTermAt(k)){
                                found = true;
                                break;
                            }
                        }
                        if(found){
                            mapName+=std::to_string(k)+"_";
                            if(indices!="")
                                indices+=",";
                            indices+=std::to_string(k);
                        }
                    }
                    sumAggrSetPredicateToAggrId[aggregate->getPredicateName()].insert({mapName,aggrId->getPredicateName()});
                    if (!declaredMaps.count(mapName)){
                        *out << ind << "AuxMap p" << mapName << "({"<<indices<<"});\n";
                        *out << ind << "AuxMap u" << mapName << "({"<<indices<<"});\n";
                        *out << ind << "AuxMap f" << mapName << "({"<<indices<<"});\n";
                        predicateToAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                        predicateToUndefAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                        predicateToFalseAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                        declaredMaps.insert(mapName);
                    }

                }else{
                    sumAggrSetPredicateToAggrId[aggregate->getPredicateName()].insert({"",aggrId->getPredicateName()});
                    
                }

                //declare map for aggr_set on shared variables
                mapName = aggregate->getPredicateName()+"_";
                std::string indices="";
                for(unsigned index : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                    mapName+=std::to_string(index)+"_";
                    if(indices!="")
                        indices+=",";
                    indices+=std::to_string(index);
                }
                if (!declaredMaps.count(mapName)){
                    *out << ind << "AuxMap p" << mapName << "({"<<indices<<"});\n";
                    *out << ind << "AuxMap u" << mapName << "({"<<indices<<"});\n";
                    *out << ind << "AuxMap f" << mapName << "({"<<indices<<"});\n";
                    predicateToAuxiliaryMaps[aggregate->getPredicateName()].insert(mapName);
                    predicateToUndefAuxiliaryMaps[aggregate->getPredicateName()].insert(mapName);
                    predicateToFalseAuxiliaryMaps[aggregate->getPredicateName()].insert(mapName);
                    declaredMaps.insert(mapName);
                }
                return;
            }
            const aspc::Atom* head = &r.getHead()[0];
            const aspc::Literal* lit = &r.getBodyLiterals()[0];

            std::vector<unsigned> indices;
            std::string mapName=head->getPredicateName()+"_";
            if(declaringMaps.find(mapName)==declaringMaps.end()){
                declaringMaps[mapName]={indices,head->getAriety()};
                mapNames[mapName]=head->getPredicateName();
            }

            std::string mapNameBody=lit->getPredicateName()+"_";
            if(declaringMaps.find(mapName)==declaringMaps.end()){
                declaringMaps[mapName]={indices,lit->getAriety()};
                mapNames[mapName]=lit->getPredicateName();
            }

            std::unordered_set<std::string> bodyVars;
            lit->addVariablesToSet(bodyVars);

            for(unsigned k=0; k<head->getAriety(); k++){
                if(!head->isVariableTermAt(k) || bodyVars.count(head->getTermAt(k))!=0){
                    mapName+=std::to_string(k)+"_";
                    indices.push_back(k);
                }
            }

            if(declaringMaps.find(mapName)==declaringMaps.end()){
                declaringMaps[mapName]={indices,head->getAriety()};
                mapNames[mapName]=head->getPredicateName();
            }


            std::unordered_set<std::string> headVars;
            aspc::Literal headLit(false,*head);
            headLit.addVariablesToSet(headVars);
            mapName=lit->getPredicateName()+"_";
            indices.clear();
            for(unsigned k=0; k<lit->getAriety(); k++){
                if(!lit->isVariableTermAt(k) || headVars.count(lit->getTermAt(k))!=0){
                    mapName+=std::to_string(k)+"_";
                    indices.push_back(k);
                }
            }

            if(declaringMaps.find(mapName)==declaringMaps.end()){
                declaringMaps[mapName]={indices,lit->getAriety()};
                mapNames[mapName]=lit->getPredicateName();

            }

        }
        for(auto declareMap : declaringMaps){
            // std::cout<<declareMap.first<<std::endl;
            if (!declaredMaps.count(declareMap.first) && (declareMap.second.first.size()<declareMap.second.second ||declareMap.second.first.size()==0)) {
                *out << ind << "AuxMap p" << declareMap.first << "({";
                for (unsigned k = 0; k < declareMap.second.first.size(); k++) {
                    if (k > 0) {
                        *out << ",";
                    }
                    *out << declareMap.second.first[k];
                }
                *out << "});\n";

                //TODO remove duplication
                *out << ind << "AuxMap u" << declareMap.first << "({";
                for (unsigned k = 0; k < declareMap.second.first.size(); k++) {
                    if (k > 0) {
                        *out << ",";
                    }
                    *out << declareMap.second.first[k];
                }
                *out << "});\n";


                //TODO remove duplication
                *out << ind << "AuxMap f" << declareMap.first << "({";
                for (unsigned k = 0; k < declareMap.second.first.size(); k++) {
                    if (k > 0) {
                        *out << ",";
                    }
                    *out << declareMap.second.first[k];
                }
                *out << "});\n";


                std::string predName = mapNames[declareMap.first];
                // std::cout<<predName<<std::endl;
                predicateToAuxiliaryMaps[predName].insert(declareMap.first);
                predicateToUndefAuxiliaryMaps[predName].insert(declareMap.first);
                predicateToFalseAuxiliaryMaps[predName].insert(declareMap.first);
                declaredMaps.insert(declareMap.first);
            }
        }
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

unsigned CompilationManager::compileRuleBody(const std::vector<unsigned> body,unsigned start,const aspc::Rule& r,std::unordered_set<std::string>boundVars,bool searchOneUndef){
    *out << ind << "const Tuple* tupleU=NULL;\n";
    *out << ind << "bool tupleUNegated=false;\n";
    *out << ind << "bool boundTupleU=false;\n";
    unsigned closingPars = 0;
    std::vector<unsigned> literalsNotBound;

    bool first=true;
    for(unsigned i : body){
        if(start == 1 && first){
            first=false;
            continue;
        }
        const aspc::Formula* f =r.getFormulas()[i];
        std::vector<unsigned> boundIndices;
        if(f->isLiteral()){
            const aspc::Literal* lit = (aspc::Literal*) f;
            if(lit->isBoundedLiteral(boundVars)){
                std::string terms;
                for(int termI=0;termI<lit->getAriety();termI++){
                    if(termI>0)
                        terms+=",";
                    terms+=lit->getTermAt(termI);
                    // TODO: Handle alfanumeric constant
                }
                *out << ind << "bool undef"<<i<<"=false;\n";
                if(lit->isNegated()){
                    *out << ind << "Tuple negativeTuple({"<<terms<<"},&_"<<lit->getPredicateName()<<");\n";

                    *out << ind << "const Tuple* tuple"<<i<<"=NULL;\n";
                    *out << ind++ << "if(w"<<lit->getPredicateName()<<".find(negativeTuple) == NULL && u"<<lit->getPredicateName()<<".find(negativeTuple) == NULL)\n";
                        *out << ind << "tuple"<<i<<"=&negativeTuple;\n";
                    if(searchOneUndef)
                        *out << --ind << "else if(tupleU==NULL && u"<<lit->getPredicateName()<<".find(negativeTuple)!=NULL){\n";
                    else
                        *out << --ind << "else if(u"<<lit->getPredicateName()<<".find(negativeTuple)!=NULL){\n";
                        *out << ++ind << "tuple"<<i<<"= tupleU = &negativeTuple;\n";
                        *out << ind << "tupleUNegated=true;\n";
                        *out << ind << "boundTupleU=true;\n";
                        *out << ind << "undef"<<i<<"=true;\n";
                    *out << --ind << "}\n";
                    *out << ind++ << "if(tuple"<<i<<"!=NULL){\n";
                }else{
                    *out << ind << "Tuple positiveTuple({"<<terms<<"},&_"<<lit->getPredicateName()<<");\n";
                    *out << ind << "const Tuple* tuple"<<i<<"=w"<<lit->getPredicateName()<<".find(positiveTuple);\n";
                    if(searchOneUndef)
                        *out << ind++ << "if(tuple"<<i<<"==NULL && tupleU==NULL){\n";
                    else
                        *out << ind++ << "if(tuple"<<i<<"==NULL){\n";

                        *out << ind << "tupleU = tuple"<<i<<" = u"<<lit->getPredicateName()<<".find(positiveTuple);\n";
                        *out << ind << "tupleUNegated=false;\n";
                        *out << ind << "boundTupleU=true;\n";
                        *out << ind << "undef"<<i<<"=true;\n";
                    *out << --ind << "}\n";
                    *out << ind++ << "if(tuple"<<i<<"!=NULL){\n";
                }
                closingPars++;
            }else{
                literalsNotBound.push_back(i);
                std::vector<unsigned> boundTerms;
                for(unsigned termI=0;termI<lit->getAriety();termI++){
                    if((lit->isVariableTermAt(termI) && boundVars.count(lit->getTermAt(termI)) != 0)|| !lit->isVariableTermAt(termI)){
                        boundTerms.push_back(termI);
                    }
                }

                *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<lit->getPredicateName()<<"_";
                for(unsigned term: boundTerms){
                    *out << term << "_";
                }
                *out << ".getValues({";
                for(unsigned index = 0;index<boundTerms.size();index++){
                    if(index > 0){
                        *out << ",";
                    }

                    if(lit->isVariableTermAt(boundTerms[index]) || isInteger(lit->getTermAt(i))){
                        *out << lit->getTermAt(boundTerms[index]);
                    }else{
                        //ConstantManager
                    }
                }
                *out << "});\n";
                *out << ind << "const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;\n";
                if(searchOneUndef)
                    *out << ind++ << "if(tupleU==NULL)\n";
                    *out << ind << "tuplesU = &u"<<lit->getPredicateName()<<"_";
                    for(unsigned term: boundTerms){
                        *out << term << "_";
                    }
                    *out << ".getValues({";
                    for(unsigned index = 0;index<boundTerms.size();index++){
                        if(index > 0){
                            *out << ",";
                        }

                        if(lit->isVariableTermAt(boundTerms[index]) || isInteger(lit->getTermAt(i))){
                            *out << lit->getTermAt(boundTerms[index]);
                        }else{
                            //ConstantManager
                        }
                    }
                    *out << "});\n";
                if(searchOneUndef)
                    --ind;
                *out << ind++ << "for(int i=0;i<tuples->size()+tuplesU->size();i++){\n";
                closingPars++;
                    if(searchOneUndef){
                        *out << ind++ << "if(tuplesU != &EMPTY_TUPLES)\n";
                        *out << ind-- << "tupleU = NULL;\n";
                    }
                    *out << ind << "const Tuple* tuple"<<i<<"=NULL;\n";
                    *out << ind << "bool undef"<<i<<"=false;\n";
                    *out << ind++ << "if(i<tuples->size())\n";
                        *out << ind << "tuple"<<i<<"=tuples->at(i);\n";
                    *out << --ind << "else{\n";
                        *out << ++ind << "tupleU = tuple"<<i<<" = tuplesU->at(i-tuples->size());\n";
                        *out << ind << "tupleUNegated=false;\n";
                        *out << ind << "boundTupleU=false;\n";
                        *out << ind << "undef"<<i<<"=true;\n";
                    *out << --ind << "}\n";
                    *out << ind++ << "if(tuple"<<i<<"!= NULL){\n";
                    closingPars++;
                    for(unsigned termI=0;termI<lit->getAriety();termI++){
                        if(lit->isVariableTermAt(termI) && boundVars.count(lit->getTermAt(termI))==0){
                            *out << ind << "int "<<lit->getTermAt(termI)<<" = tuple"<<i<<"->at("<<termI<<");\n";
                            boundVars.insert(lit->getTermAt(termI));
                        }
                    }
            }

        }
    }
    return closingPars;
}
unsigned CompilationManager::exploreLiteral(const aspc::Literal* lit,std::unordered_set<std::string>& boundVariables,unsigned currentLitIndex){
    unsigned pars=0;
    // std::cout<<"Explore literal ";
    // lit->print();
    // std::cout<<std::endl;
    std::string boundTerms;
    std::vector<unsigned> boundIndices;
    for(unsigned k=0; k<lit->getAriety();k++){
        if(!lit->isVariableTermAt(k) || boundVariables.count(lit->getTermAt(k))!=0){
            boundIndices.push_back(k);
            if(boundTerms != "")
                boundTerms+=",";
            boundTerms+=lit->getTermAt(k);
        }
    }
    if(lit->isBoundedLiteral(boundVariables)){
        if(lit->isNegated()){
            *out << ind << "Tuple negativeTuple({"<<boundTerms<<"},&_"<<lit->getPredicateName()<<");\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = w"<<lit->getPredicateName()<<".find(negativeTuple);\n";
            *out << ind << "const Tuple* tupleUndef"<<currentLitIndex<<" = u"<<lit->getPredicateName()<<".find(negativeTuple);\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<" == tupleUndef"<<currentLitIndex<<" && tupleUndef"<<currentLitIndex<<" == NULL)\n";
                *out << ind-- << "tuple"<<currentLitIndex<<" = &negativeTuple;\n";
            *out << ind++ << "else if(tupleU == NULL & tupleUndef"<<currentLitIndex<<" != NULL){\n";
                *out << ind << "tupleU = tuple"<<currentLitIndex<<" = tupleUndef"<<currentLitIndex<<";\n";
                *out << ind << "tupleUNegated=true;\n";
            *out << --ind << "}else if(tupleU!=NULL && tupleU->getPredicateName() == &_"<<lit->getPredicateName()<<" && tupleUNegated && tupleU==tupleUndef"<<currentLitIndex<<"){\n";
            ind++;
                *out << ind << "tuple"<<currentLitIndex<<"=tupleU;\n";
            *out << --ind << "}else if(tuple"<<currentLitIndex<<"!=NULL){\n";
            ind++;
                *out << ind << "tuple"<<currentLitIndex<<"=NULL;\n";
            *out << --ind << "}\n";

        }else{
            *out << ind << "Tuple positiveTuple({"<<boundTerms<<"},&_"<<lit->getPredicateName()<<");\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = w"<<lit->getPredicateName()<<".find(positiveTuple);\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<" == tupleU && tupleU == NULL){\n";
                *out << ind << "tuple"<<currentLitIndex<<" = tupleU = u"<<lit->getPredicateName()<<".find(positiveTuple);\n";
                *out << ind << "tupleUNegated=false;\n";
            *out << --ind << "}else if(tupleU!=NULL && tuple"<<currentLitIndex<<"==NULL && tupleU->getPredicateName() == &_"<<lit->getPredicateName()<<" && ! tupleUNegated){\n";
            ind++;
                *out << ind++ << "if(tupleU == u"<<lit->getPredicateName()<<".find(positiveTuple)){\n";
                    *out << ind << "tuple"<<currentLitIndex<<"=tupleU;\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        }
        *out << ind++ << "if(tuple"<<currentLitIndex<<"!=NULL){\n";
        pars++;
    }else{
        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<lit->getPredicateName()<<"_";
        for(unsigned k: boundIndices){
            *out << k << "_";
        }
        *out << ".getValues({"<<boundTerms<<"});\n";
        *out << ind << "const std::vector<const Tuple*>* tuplesU = &EMPTY_TUPLES;\n";
        *out << ind << "std::vector<const Tuple*> undeRepeated;\n";
        *out << ind++ << "if(tupleU == NULL)\n";
            *out << ind-- << "tuplesU = &u"<<lit->getPredicateName()<<"_";
            for(unsigned k: boundIndices){
                *out << k << "_";
            }
            *out << ".getValues({"<<boundTerms<<"});\n";
        *out << ind++ << "else if(tupleU->getPredicateName() == &_"<<lit->getPredicateName()<<" && !tupleUNegated)\n";
            *out << ind-- << "undeRepeated.push_back(tupleU);\n";

        *out << ind << "unsigned totalSize=tuples->size()+tuplesU->size()+undeRepeated.size();\n";
        *out << ind++ << "for(unsigned i = 0; i<totalSize; i++){\n";
        pars++;
            *out << ind << "unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();\n";
            *out << ind++ << "if(totalSize>currentSize){\n";
                *out << ind << "i-=totalSize-currentSize;\n";
                *out << ind << "totalSize=currentSize;\n";
            *out << --ind << "}\n";
            *out << ind++ << "if(tuplesU!=&EMPTY_TUPLES)\n";
                *out << ind-- << "tupleU = NULL;\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = NULL;\n";
            *out << ind++ << "if(i<tuples->size())\n";
                *out << ind-- << "tuple"<<currentLitIndex<<" = tuples->at(i);\n";
            *out << ind++ << "else if(i<tuples->size()+tuplesU->size()){\n";
                *out << ind << "tupleU = tuple"<<currentLitIndex<<" = tuplesU->at(i-tuples->size());\n";
                *out << ind << "tupleUNegated=false;\n";
            *out << --ind << "}else if(!undeRepeated.empty()){\n";
            ind++;
                std::string conditions="";
                for(unsigned k: boundIndices){
                    if(conditions!="")
                        conditions+=" && ";
                    conditions+="tupleU->at("+std::to_string(k)+") == "+lit->getTermAt(k);
                }
                if(conditions!="")
                    *out << ind++ << "if("<<conditions<<")\n";

                *out << ind << "tuple"<<currentLitIndex<<" = tupleU;\n";

                if(conditions!="")
                    ind--;
            *out << --ind << "}\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<"!=NULL){\n";
            pars++;
            if(checkTupleFormat(*lit,"tuple"+std::to_string(currentLitIndex),true))
                pars++;
            for(unsigned k = 0; k < lit->getAriety(); k++){
                if(lit->isVariableTermAt(k) && boundVariables.count(lit->getTermAt(k))==0){
                    *out << ind << "int "<<lit->getTermAt(k)<<" = tuple"<<currentLitIndex<<"->at("<<k<<");\n";
                    boundVariables.insert(lit->getTermAt(k));
                }
            }
    }
    return pars;
}
void CompilationManager::compileEagerRuleWithAggregate(const aspc::Rule& r,bool fromStarter){

    const aspc::Literal* bodyPred = !r.getBodyLiterals().empty() ? &r.getBodyLiterals()[0] : NULL;
    const aspc::Literal* aggrSetPred = &r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0];
    const aspc::Atom* aggrIdAtom = &r.getHead()[0];
    const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &r.getArithmeticRelationsWithAggregate()[0];

    // std::cout<<"Compile eager rule with aggr"<<std::endl;
    if(fromStarter){
        {

            *out << ind++ << "if(starter.getPredicateName() == &_"<<aggrIdAtom->getPredicateName()<<"){\n";
            std::unordered_set<std::string> boundVariables;
            for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                    *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = starter["<<i<<"];\n";
                    boundVariables.insert(aggrIdAtom->getTermAt(i));
                }
            }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";

                        *out << "starter["<<i<<"]";
                    }
                }

                *out << "});\n";

                std::string mapName=aggrSetPred->getPredicateName()+"_";
                for(unsigned i : sharedVarAggrIDToAggrSetIndices[aggrIdAtom->getPredicateName()]){
                    mapName+=std::to_string(i)+"_";
                }
                std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
                std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;
                *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<mapName<<".getValues(sharedVar);\n";
                string bodyTerms = "";
                if(bodyPred!=NULL){
                    for(unsigned i = 0; i<bodyPred->getAriety();i++){
                        if(bodyTerms!="")
                            bodyTerms+=",";
                        bodyTerms+=bodyPred->getTermAt(i);
                    }
                }

                *out << ind++ << "if(starter.isNegated()){\n";

                    if(aggregateRelation->getAggregate().isSum())
                        *out << ind++ << "if(actualSum[uStartVar]>="<<guard<<"){\n";
                    else
                       *out << ind++ << "if(tuples->size()>="<<guard<<"){\n";
                    
                        *out << ind << "std::cout<<\"Conflitct on aggregate start from aggrId false\"<<std::endl;\n";
                        *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                            *out << ind << "auto it = tupleToVar.find(*tuples->at(i));\n";
                            *out << ind++ << "if(it != tupleToVar.end()){\n";
                                *out << ind << "reasonForLiteral[-startVar].insert(it->second);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                        *out << ind << "handleConflict(-startVar);\n";
                        *out << ind << "return;\n";
                    if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind << "std::vector<int> reason;\n";
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "for(int index=0; index<tuplesU->size();){\n";
                                *out << ind++ << "if(actualSum[uStartVar]+tuplesU->at(index)->at(0) >= "<<guard<<"){\n";
                                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(index));\n";
                                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-itProp->second)==0){\n";
                                            *out << ind++ << "if(reason.empty()){\n";
                                                *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                                    *out << ind << "auto it = tupleToVar.find(*tuples->at(i));\n";
                                                    *out << ind++ << "if(it != tupleToVar.end()){\n";
                                                        *out << ind << "reason.push_back(it->second);\n";
                                                        *out << ind << "reasonForLiteral[-itProp->second].insert(it->second);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                                *out << ind << "reason.push_back(startVar);\n";
                                                *out << ind << "reasonForLiteral[-itProp->second].insert(startVar);\n";
                                            *out << --ind << "}else{\n";
                                            ind++;
                                                *out << ind++ << "for(int reasonLit : reason)\n";
                                                    *out << ind-- << "reasonForLiteral[-itProp->second].insert(reasonLit);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,true,propagatedLiterals);\n";
                                *out << --ind << "}else index++;\n";
                            *out << --ind << "}\n";
                        }else{
                            std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
                            unsigned varIndex = 0;
                            for(unsigned var = 0; var<aggrSetPred->getAriety(); var++){
                                if(firstAggrVar == aggrSetPred->getTermAt(var)){
                                    varIndex = var;
                                    break;
                                }
                            }
                            *out << ind++ << "for(unsigned index =0; index<tuplesU->size(); index++){\n";
                                *out << ind++ << "if(actualSum[uStartVar]+tuplesU->at(index)->at("<<varIndex<<") >= "<<guard<<"){\n";
                                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(index));\n";
                                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-itProp->second)==0){\n";
                                            *out << ind++ << "if(reason.empty()){\n";
                                                *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                                    *out << ind << "auto it = tupleToVar.find(*tuples->at(i));\n";
                                                    *out << ind++ << "if(it != tupleToVar.end()){\n";
                                                        *out << ind << "reason.push_back(it->second);\n";
                                                        *out << ind << "reasonForLiteral[-itProp->second].insert(it->second);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                                *out << ind << "reason.push_back(startVar);\n";
                                                *out << ind << "reasonForLiteral[-itProp->second].insert(startVar);\n";
                                            *out << --ind << "}else{\n";
                                            ind++;
                                                *out << ind++ << "for(int reasonLit : reason)\n";
                                                    *out << ind-- << "reasonForLiteral[-itProp->second].insert(reasonLit);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,true,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                    *out << --ind << "}\n";
                    }else{
                        *out << --ind << "}else if(tuples->size() == "<<guard<<" -1){\n";
                        ind++;
                            *out << ind << "std::vector<int> reason;\n";
                            *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                *out << ind << "auto it = tupleToVar.find(*tuples->at(i));\n";
                                *out << ind++ << "if(it != tupleToVar.end()){\n";
                                    *out << ind << "reason.push_back(it->second);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind << "reason.push_back(startVar);\n";
                            if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                                *out << ind++ << "while(!tuplesU->empty()){\n";
                                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(0));\n";
                                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-itProp->second)==0){\n";
                                            *out << ind++ << "for(int reasonLit : reason)\n";
                                                *out << ind-- << "reasonForLiteral[-itProp->second].insert(reasonLit);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            }else{
                                *out << ind++ << "for(unsigned i =0; i<tuplesU->size(); i++){\n";
                                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(i));\n";
                                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-itProp->second)==0){\n";
                                            *out << ind++ << "for(int reasonLit : reason)\n";
                                                *out << ind-- << "reasonForLiteral[-itProp->second].insert(reasonLit);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            }
                            
                        *out << --ind << "}\n";
                    }
                    
                *out << --ind << "}else{\n";
                ind++;
                    if(aggregateRelation->getAggregate().isSum())
                        *out << ind++ << "if(actualSum[uStartVar]+possibleSum[uStartVar] < "<<guard<<"){\n";
                    else
                        *out << ind++ << "if(tuples->size()+tuplesU->size() < "<<guard<<"){\n";
                        *out << ind << "std::cout<<\"Conflitct on aggregate starting from aggrId true\"<<std::endl;\n";
                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                        *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                            *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                *out << ind << "reasonForLiteral[-startVar].insert(-it->second);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                        *out << ind << "handleConflict(-startVar);\n";
                        *out << ind << "return;\n";
                    if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "for(unsigned index=0;index<tuplesU->size();){\n";
                                *out << ind++ << "if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at(0) < "<<guard<<"){\n";
                                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(index));\n";
                                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0){\n";
                                            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                            *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                                *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                    *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(startVar);\n";
                                        *out << --ind << "}\n";
                                        // reason contains aggr_id and all aggr_set false
                                        *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else index++;\n";
                            *out << --ind << "}\n";
                        }else{
                            std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
                            unsigned varIndex = 0;
                            for(unsigned var = 0; var<aggrSetPred->getAriety(); var++){
                                if(firstAggrVar == aggrSetPred->getTermAt(var)){
                                    varIndex = var;
                                    break;
                                }
                            }
                            *out << ind++ << "for(unsigned index=0;index<tuplesU->size();index++){\n";
                                *out << ind++ << "if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at("<<varIndex<<") < "<<guard<<"){\n";
                                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(index));\n";
                                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0){\n";
                                            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                            *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                                *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                    *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(startVar);\n";
                                        *out << --ind << "}\n";
                                        // reason contains aggr_id and all aggr_set false
                                        *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                    *out << --ind << "}\n";
                    }else{
                        *out << --ind << "}else if(tuples->size() + tuplesU->size() == "<<guard<<"){\n";
                        ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "while(tuplesU->size()>0){\n";
                                *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(0));\n";
                                *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                    *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0){\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                        *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                            *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "reasonForLiteral[itProp->second].insert(startVar);\n";
                                    *out << --ind << "}\n";
                                    // reason contains aggr_id and all aggr_set false
                                    *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }else{
                            *out << ind++ << "for(unsigned index=0;index<tuplesU->size();index++){\n";
                                *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(index));\n";
                                *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                    *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0){\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                        *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                            *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "reasonForLiteral[itProp->second].insert(startVar);\n";
                                    *out << --ind << "}\n";
                                    // reason contains aggr_id and all aggr_set false
                                    *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                        *out << --ind << "}\n";
                    }
                *out << --ind << "}\n";
            *out << --ind << "}//close aggr id starter\n";
            // std::cout<<"Compiled starter aggr id"<<std::endl;

        }
    }
    {
        if(fromStarter)
            *out << ind++ << "if(starter.getPredicateName() == &_"<<aggrSetPred->getPredicateName()<<"){\n";
        else *out << ind++ << "{\n";
        std::string mapName=aggrSetPred->getPredicateName()+"_";
        for(unsigned i : sharedVarAggrIDToAggrSetIndices[aggrIdAtom->getPredicateName()]){
            mapName+=std::to_string(i)+"_";
        }
        std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
        std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;
        string bodyTerms = "";
        if(bodyPred!=NULL){
            for(unsigned i = 0; i<bodyPred->getAriety();i++){
                if(bodyTerms!="")
                    bodyTerms+=",";
                bodyTerms+=bodyPred->getTermAt(i);
            }
        }

            *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<aggrIdAtom->getPredicateName()<<"_.getValues({});\n";
            *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<aggrIdAtom->getPredicateName()<<"_.getValues({});\n";
            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<aggrIdAtom->getPredicateName()<<"_.getValues({});\n";
            //OPTIMIZATION Add if starter.isNegated
            // *out << ind << "std::cout<<\"Prop for true head\"<<std::endl;\n";
            *out << ind++ << "for(unsigned i = 0; i<tuples->size(); i++){\n";
            {
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = tuples->at(i)->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }
                }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";

                        *out << "tuples->at(i)->at("<<i<<")";
                    }
                }
                *out << "});\n";

                *out << ind << "const std::vector<const Tuple*>* joinTuples = &p"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "const std::vector<const Tuple*>* joinTuplesU = &u"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "auto aggrIdIt=tupleToVar.find(*tuples->at(i));\n";
                *out << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << ind++ << "if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second] < "<<guard<<"){\n";
                else
                    *out << ind++ << "if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                    *out << ind << "std::cout<<\"Conflitct on aggregate starting from true aggr id \"<<std::endl;\n";
                    if(fromStarter){
                        *out << ind << "auto itProp = tupleToVar.find(*tuples->at(i));\n";
                        *out << ind++ << "if(itProp!=tupleToVar.end()){\n";
                            *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                            *out << ind++ << "for(unsigned j = 0; j < joinTuplesF->size(); j++){\n";
                                *out << ind << "auto it = tupleToVar.find(*joinTuplesF->at(j));\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    *out << ind << "reasonForLiteral[-itProp->second].insert(-it->second);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind << "handleConflict(-itProp->second);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind << "propagatedLiterals.insert(-1);\n";
                    }
                if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size();){\n";
                            *out << ind << "if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second]-joinTuplesU->at(index)->at(0) >= "<<guard<<") {index++; continue;}\n";
                            *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(index));\n";
                            *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0 ){\n";
                                    *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                        *out << ind << "auto it = tupleToVar.find(*joinTuplesF->at(i));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "auto itAggrId = tupleToVar.find(*tuples->at(i));\n";
                                    *out << ind++ << "if(itAggrId!= tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[itProp->second].insert(itAggrId->second);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                // reason contains aggr_id and all aggr_set false
                                *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }else{
                        std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
                        unsigned varIndex = 0;
                        for(unsigned var = 0; var<aggrSetPred->getAriety(); var++){
                            if(firstAggrVar == aggrSetPred->getTermAt(var)){
                                varIndex = var;
                                break;
                            }
                        }
                        *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size(); index++){\n";
                            *out << ind << "if(actualSum[aggrIdIt->second]+possibleSum[aggrIdIt->second]-joinTuplesU->at(index)->at("<<varIndex<<") >= "<<guard<<") {index++; continue;}\n";
                            *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(index));\n";
                            *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0 ){\n";
                                    *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                        *out << ind << "auto it = tupleToVar.find(*joinTuplesF->at(i));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "auto itAggrId = tupleToVar.find(*tuples->at(i));\n";
                                    *out << ind++ << "if(itAggrId!= tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[itProp->second].insert(itAggrId->second);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                // reason contains body, aggr_id and all aggr_set false
                                *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }
                    *out << --ind << "}\n";
                }else{

                    *out << --ind << "}else if(joinTuples->size() + joinTuplesU->size() == "<<guard<<"){\n";
                    ind++;
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        *out << ind++ << "while(joinTuplesU->size()>0){\n";
                            *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(0));\n";
                            *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0 ){\n";
                                    *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                        *out << ind << "auto it = tupleToVar.find(*joinTuplesF->at(i));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "auto itAggrId = tupleToVar.find(*tuples->at(i));\n";
                                    *out << ind++ << "if(itAggrId!= tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[itProp->second].insert(itAggrId->second);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                // reason contains body, aggr_id and all aggr_set false
                                *out << ind << "propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size(); index++){\n";
                            *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(index));\n";
                            *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0 ){\n";
                                    *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                        *out << ind << "auto it = tupleToVar.find(*joinTuplesF->at(i));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "auto itAggrId = tupleToVar.find(*tuples->at(i));\n";
                                    *out << ind++ << "if(itAggrId!= tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[itProp->second].insert(itAggrId->second);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                                // reason contains body, aggr_id and all aggr_set false
                                *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }
                        
                    *out << --ind << "}\n";
                }
            }
            *out << --ind << "}//close true for\n";
            //OPTIMIZATION Add if !starter.isNegated

            // *out << ind << "std::cout<<\"Prop for false head\"<<std::endl;\n";
            *out << ind++ << "for(unsigned i = 0; i<tuplesF->size(); i++){\n";
            {
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = tuplesF->at(i)->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }
                }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred != NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";

                        *out << "tuplesF->at(i)->at("<<i<<")";
                    }
                }
                *out << "});\n";

                *out << ind << "const std::vector<const Tuple*>* joinTuples = &p"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "const std::vector<const Tuple*>* joinTuplesU = &u"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "auto aggrIdIt=tupleToVar.find(*tuplesF->at(i));\n";
                *out << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << ind++ << "if(actualSum[aggrIdIt->second] >= "<<guard<<"){\n";
                else
                    *out << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";
                    *out << ind << "std::cout<<\"Conflitct on aggregate starting from false aggr id \"<<actualSum[aggrIdIt->second]<<std::endl;\n";
                    if(fromStarter){
                        *out << ind << "auto itProp = tupleToVar.find(*tuplesF->at(i));\n";
                        *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                            *out << ind++ << "for(unsigned j =0; j< joinTuples->size(); j++){\n";
                                *out << ind << "auto it = tupleToVar.find(*joinTuples->at(j));\n";
                                *out << ind++ << "if(it != tupleToVar.end()){\n";
                                    *out << ind << "reasonForLiteral[itProp->second].insert(it->second);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind << "handleConflict(itProp->second);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind << "propagatedLiterals.insert(-1);\n";
                    }
                if(aggregateRelation->getAggregate().isSum())
                    *out << --ind << "}else{\n";
                else
                    *out << -- ind << "}else if(joinTuples->size() == "<<guard<<" -1){\n";
                ind++;
                    //*out << ind << "std::cout << \"aggr propagation\"<<std::endl;\n";
                    *out << ind << "std::vector<int> reason;\n";
                    
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        if(aggregateRelation->getAggregate().isSum()){
                            *out << ind++ << "for(unsigned index=0;index<joinTuplesU->size();){\n";
                                *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(index));\n";
                                *out << ind++ << "if(actualSum[aggrIdIt->second]+joinTuplesU->at(index)->at(0) >= "<<guard<<"){\n";
                                
                        }else{
                            *out << ind++ << "while(!joinTuplesU->empty()){\n";
                                *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(0));\n";
                        }

                            *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                *out << ind++ << "if(reasonForLiteral.count(-itProp->second) == 0 ){\n";
                                    *out << ind++ << "if(reason.empty()){\n";
                                        *out << ind++ << "for(unsigned i =0; i< joinTuples->size(); i++){\n";
                                            *out << ind << "auto it = tupleToVar.find(*joinTuples->at(i));\n";
                                            *out << ind++ << "if(it != tupleToVar.end()){\n";
                                                *out << ind << "reason.push_back(it->second);\n";
                                                *out << ind << "reasonForLiteral[-itProp->second].insert(it->second);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                                        *out << ind++ << "if(it!= tupleToVar.end()){\n";
                                            *out << ind << "reason.push_back(-it->second);\n";
                                            *out << ind << "reasonForLiteral[-itProp->second].insert(-it->second);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}else{\n";
                                        *out << ind++ << "for(int reasonLit : reason)\n";
                                            *out << ind-- << "reasonForLiteral[-itProp->second].insert(reasonLit);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            if(aggregateRelation->getAggregate().isSum()){
                                *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);\n";
                                *out << --ind << "}else index++;\n";
                            }
                            else
                                *out << ind << "propUndefined(joinTuplesU->at(0),false,propagationStack,true,propagatedLiterals);\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size(); index++){\n";
                        if(aggregateRelation->getAggregate().isSum()){
                            std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
                            unsigned varIndex = 0;
                            for(unsigned var = 0; var<aggrSetPred->getAriety(); var++){
                                if(firstAggrVar == aggrSetPred->getTermAt(var)){
                                    varIndex = var;
                                    break;
                                }
                            }
                            *out << ind++ << "if(actualSum[aggrIdIt->second]+joinTuplesU->at(index)->at("<<varIndex<<") >= "<<guard<<"){\n";
                        }
                            *out << ind << "auto itProp = tupleToVar.find(*joinTuplesU->at(index));\n";
                            *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                                *out << ind++ << "if(reasonForLiteral.count(-itProp->second) == 0 ){\n";
                                    *out << ind++ << "if(reason.empty()){\n";
                                        *out << ind++ << "for(unsigned i =0; i< joinTuples->size(); i++){\n";
                                            *out << ind << "auto it = tupleToVar.find(*joinTuples->at(i));\n";
                                            *out << ind++ << "if(it != tupleToVar.end()){\n";
                                                *out << ind << "reason.push_back(it->second);\n";
                                                *out << ind << "reasonForLiteral[-itProp->second].insert(it->second);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "auto it = tupleToVar.find(*tuplesF->at(i));\n";
                                        *out << ind++ << "if(it!= tupleToVar.end()){\n";
                                            *out << ind << "reason.push_back(-it->second);\n";
                                            *out << ind << "reasonForLiteral[-itProp->second].insert(-it->second);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}else{\n";
                                    ind++;
                                        *out << ind++ << "for(int reasonLit : reason)\n";
                                            *out << ind-- << "reasonForLiteral[-itProp->second].insert(reasonLit);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                            *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,true,propagatedLiterals);\n";
                        *out << --ind << "}\n";
                        if(aggregateRelation->getAggregate().isSum()){
                            *out << --ind << "}\n";
                        }
                    }
                    
                *out << --ind << "}\n";
            }
            *out << --ind << "}//close false for\n";

            *out << ind++ << "for(unsigned i = 0; i<tuplesU->size();){\n";
            {
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = tuplesU->at(i)->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }
                }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";
                        *out << "tuplesU->at(i)->at("<<i<<")";
                    }
                }
                *out << "});\n";

                *out << ind << "const std::vector<const Tuple*>* joinTuples = &p"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "const std::vector<const Tuple*>* joinTuplesU = &u"<<mapName<<".getValues(sharedVar);\n";
                *out << ind << "auto aggrIdIt=tupleToVar.find(*tuplesU->at(i));\n";
                *out << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << ind++ << "if(actualSum[aggrIdIt->second] >= "<<guard<<"){\n";
                else
                    *out << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";
                    
                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(i));\n";
                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                        *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0 ){\n";
                            *out << ind++ << "for(unsigned j = 0; j < joinTuples->size(); j++){\n";
                                *out << ind << "auto it = tupleToVar.find(*joinTuples->at(j));\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    *out << ind << "reasonForLiteral[itProp->second].insert(it->second);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                        *out << ind << "propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);\n";
                    *out << --ind << "}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << --ind << "}else if(actualSum[aggrIdIt->second] + possibleSum[aggrIdIt->second] < "<<guard<<"){\n";
                else
                    *out << --ind << "}else if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                ind++;
                    *out << ind << "auto itProp = tupleToVar.find(*tuplesU->at(i));\n";
                    *out << ind++ << "if(itProp != tupleToVar.end()){\n";
                        *out << ind++ << "if(reasonForLiteral.count(-itProp->second) == 0 ){\n";
                            *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                            *out << ind++ << "for(unsigned j = 0; j < joinTuplesF->size(); j++){\n";
                                *out << ind << "auto it = tupleToVar.find(*joinTuplesF->at(j));\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    *out << ind << "reasonForLiteral[-itProp->second].insert(-it->second);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                        *out << ind << "propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}else{\n";
                ind++;
                    *out << ind << "i++;\n";
                *out << --ind << "}\n";
            }
            *out << --ind << "}//close undef for\n";
        *out << --ind << "}//close aggr set starter\n";
    }
}
void CompilationManager::compileEagerRule(const aspc::Rule& r,bool fromStarter){

    // std::cout<<"Compiling Eager rule ";
    // r.print();
    if(r.containsAggregate()){
        compileEagerRuleWithAggregate(r,fromStarter);
        // std::cout<<"compiled"<<std::endl;
        return;
    }
    if(!r.isConstraint()){
        if(fromStarter){
            for(unsigned starterIndex:r.getStarters()){
                if(starterIndex < r.getBodySize()){
                    const aspc::Literal* l = &r.getBodyLiterals()[0];
                    *out << ind++ << "if(starter.getPredicateName() == &_"<<l->getPredicateName()<<"){\n";
                        std::unordered_set<std::string> boundVariables;
                        for(unsigned k=0; k<l->getAriety(); k++){
                            if(l->isVariableTermAt(k) && boundVariables.count(l->getTermAt(k))==0){
                                *out << ind << "int "<<l->getTermAt(k)<<" = starter["<<k<<"];\n";
                                boundVariables.insert(l->getTermAt(k));
                            }
                        }
                        bool checkFormat = checkTupleFormat(*l,"starter",false);
                        *out << ind++ << "if(!starter.isNegated()){\n";
                            const aspc::Atom* head = &r.getHead()[0];
                            *out << ind << "Tuple head({";
                            for(unsigned k=0; k<head->getAriety(); k++){
                                if(k>0)
                                    *out << ",";
                                *out << head->getTermAt(k);
                            }
                            *out << "}, &_"<<head->getPredicateName()<<");\n";
                            *out << ind << "const Tuple* tupleU = u"<<head->getPredicateName()<<".find(head);\n";
                            *out << ind++ << "if(w"<<head->getPredicateName()<<".find(head) == tupleU && tupleU==NULL){\n";
                                // *out << ind << "std::cout<<\"Conflict: exists support for false head\"<<std::endl;\n";
                                *out << ind << "const auto& it = tupleToVar.find(head);\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    *out << ind << "reasonForLiteral[it->second].insert(startVar);\n";
                                    *out << ind << "handleConflict(it->second);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}else if(tupleU != NULL){\n";
                            ind++;
                                *out << ind << "const auto& it = tupleToVar.find(head);\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    *out << ind++ << "if(reasonForLiteral.count(it->second) == 0 )\n";
                                        *out << ind-- << "reasonForLiteral[it->second].insert(startVar);\n";
                                    *out << ind << "propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            std::unordered_set<std::string> headVariables;
                            for(unsigned k=0; k<head->getAriety(); k++){
                                if(head->isVariableTermAt(k)){
                                    headVariables.insert(head->getTermAt(k));
                                }
                            }
                            std::vector<unsigned>boundIndices;
                            std::string boundTerms;
                            for(unsigned k=0; k<l->getAriety(); k++){
                                if(!l->isVariableTermAt(k) || headVariables.count(l->getTermAt(k))!=0){
                                    boundIndices.push_back(k);
                                    if(boundTerms!="")
                                        boundTerms+=",";
                                    boundTerms+=l->getTermAt(k);
                                }
                            }
                            *out << ind << "Tuple head({";
                            for(unsigned k=0; k<head->getAriety(); k++){
                                if(k>0)
                                    *out << ",";
                                *out << head->getTermAt(k);
                            }
                            *out << "}, &_"<<head->getPredicateName()<<");\n";
                            if(l->isBoundedLiteral(headVariables)){
                                *out << ind++ << "if(w"<<head->getPredicateName()<<".find(head) != NULL){\n";
                                    // *out << ind << "std::cout<<\"Conflict: unsupported head atom\"<<std::endl;\n";
                                    *out << ind << "const auto it = tupleToVar.find(head);\n";
                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[-it->second].insert(startVar);\n";
                                        *out << ind << "handleConflict(-it->second);\n";
                                        *out << ind << "return;\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind << "const Tuple* tupleU = u"<<head->getPredicateName()<<".find(head);\n";
                                    *out << ind++ << "if(tupleU!=NULL){\n";
                                        *out << ind << "const auto it = tupleToVar.find(head);\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind++ << "if(reasonForLiteral.count(-it->second) == 0 )\n";
                                                *out << ind-- << "reasonForLiteral[-it->second].insert(startVar);\n";
                                            *out << ind << "propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            }else{
                                *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                                for(unsigned k : boundIndices){
                                    *out << k << "_";
                                }
                                *out << ".getValues({"<<boundTerms<<"});\n";
                                *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<l->getPredicateName()<<"_";
                                for(unsigned k : boundIndices){
                                    *out << k << "_";
                                }
                                *out << ".getValues({"<<boundTerms<<"});\n";
                                *out << ind++ << "if(w"<<head->getPredicateName()<<".find(head) != NULL){\n";
                                    *out << ind++ << "if(tuples->size()==0 && tuplesU->size()==0){\n";
                                        // *out << ind << "std::cout<<\"Conflict: unable to find support for true head\"<<std::endl;\n";
                                        *out << ind << "const auto itHead = tupleToVar.find(head);\n";
                                        *out << ind++ << "if(itHead!=tupleToVar.end()){\n";
                                            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                            for(unsigned k : boundIndices){
                                                *out << k << "_";
                                            }
                                            *out << ".getValues({"<<boundTerms<<"});\n";
                                            *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                                *out << ind << "const auto& it = tupleToVar.find(*tuplesF->at(i));\n";
                                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                    *out << ind << "reasonForLiteral[-itHead->second].insert(-it->second);\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "handleConflict(-itHead->second);\n";
                                            *out << ind << "return;\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}else if(tuples->size() == 0 && tuplesU->size() == 1){\n";
                                    ind++;
                                        *out << ind << "const auto itProp = tupleToVar.find(*tuplesU->at(0));\n";
                                        *out << ind++ << "if(itProp!=tupleToVar.end()){\n";

                                            *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0 ){\n";
                                                *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                                for(unsigned k : boundIndices){
                                                    *out << k << "_";
                                                }
                                                *out << ".getValues({"<<boundTerms<<"});\n";
                                                *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                                    *out << ind << "const auto& it = tupleToVar.find(*tuplesF->at(i));\n";
                                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                        *out << ind << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                                *out << ind << "const auto& it = tupleToVar.find(head);\n";
                                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                    *out << ind << "reasonForLiteral[itProp->second].insert(it->second);\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind << "const Tuple* tupleU = u"<<head->getPredicateName()<<".find(head);\n";
                                    *out << ind++ << "if(tupleU != NULL && tuples->size() == 0 && tuplesU->size() == 0){\n";
                                        *out << ind << "const auto itHead = tupleToVar.find(head);\n";
                                        *out << ind++ << "if(itHead!=tupleToVar.end()){\n";
                                            *out << ind++ << "if(reasonForLiteral.count(-itHead->second) == 0 ){\n";
                                                *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                                for(unsigned k : boundIndices){
                                                    *out << k << "_";
                                                }
                                                *out << ".getValues({"<<boundTerms<<"});\n";
                                                *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                                    *out << ind << "const auto& it = tupleToVar.find(*tuplesF->at(i));\n";
                                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                                        *out << ind << "reasonForLiteral[-itHead->second].insert(-it->second);\n";
                                                    *out << --ind << "}\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            }
                        *out << --ind << "}\n";
                        if(checkFormat)
                            *out << --ind << "}\n";
                    *out << --ind << "}\n";
                }else{
                    std::unordered_set<std::string> boundVariables;
                    const aspc::Atom* head = &r.getHead()[0];
                    *out << ind++ << "if(starter.getPredicateName() == &_"<<head->getPredicateName()<<"){\n";
                        bool checkFormat = checkTupleFormat(aspc::Literal(false,*head),"starter",false);
                        for(unsigned k=0;k<head->getAriety();k++){
                            if(head->isVariableTermAt(k) && boundVariables.count(head->getTermAt(k))==0){
                                *out << ind << "int "<<head->getTermAt(k) << " = starter["<<k<<"];\n";
                                boundVariables.insert(head->getTermAt(k));
                            }
                        }
                        std::vector<unsigned>boundIndices;
                        std::string boundTerms;  
                        const aspc::Literal* l = &r.getBodyLiterals()[0];
                        for(unsigned k=0; k<l->getAriety(); k++){
                            if(!l->isVariableTermAt(k) || boundVariables.count(l->getTermAt(k))!=0){
                                boundIndices.push_back(k);
                                if(boundTerms!="")
                                    boundTerms+=",";
                                boundTerms+=l->getTermAt(k);
                            }
                        }
                        if(l->isBoundedLiteral(boundVariables)){
                            *out << ind << "const Tuple tuple ({"<<boundTerms<<"}, &_"<<l->getPredicateName()<<");\n";
                            *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(tuple);\n";
                            *out << ind++ << "if(!starter.isNegated()){\n";
                                *out << ind++ << "if(w"<<l->getPredicateName()<<".find(tuple) == tupleU && tupleU==NULL){\n";
                                    // *out << ind << "std::cout<<\"Conflict: unable to find support for true head\"<<std::endl;\n";
                                    *out << ind << "const auto& it = tupleToVar.find(tuple);\n";
                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[it->second].insert(startVar);\n";
                                        *out << ind << "handleConflict(it->second);\n";
                                        *out << ind << "return;\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind++ << "if(tupleU!=NULL){\n";
                                        *out << ind << "const auto& it = tupleToVar.find(tuple);\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind++ << "if(reasonForLiteral.count(it->second) == 0 )\n";
                                                *out << ind-- << "reasonForLiteral[it->second].insert(startVar);\n";
                                            *out << ind << "propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                *out << ind++ << "if(w"<<l->getPredicateName()<<".find(tuple)!=NULL){\n";
                                    // *out << ind << "std::cout<<\"Conflict: support found for false head\"<<std::endl;\n";
                                    *out << ind << "const auto& it = tupleToVar.find(tuple);\n";
                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[-it->second].insert(startVar);\n";
                                        *out << ind << "handleConflict(-it->second);\n";
                                        *out << ind << "return;\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind++ << "if(tupleU!=NULL){\n";
                                        *out << ind << "const auto& it = tupleToVar.find(tuple);\n";
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            *out << ind++ << "if(reasonForLiteral.count(-it->second) == 0)\n";
                                                *out << ind-- << "reasonForLiteral[-it->second].insert(startVar);\n";
                                            *out << ind << "propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }else{
                            *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                            for(unsigned k : boundIndices){
                                *out << k << "_";
                            }
                            *out << ".getValues({"<<boundTerms<<"});\n";
                            *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<l->getPredicateName()<<"_";
                            for(unsigned k : boundIndices){
                                *out << k << "_";
                            }
                            *out << ".getValues({"<<boundTerms<<"});\n";
                            *out << ind++ << "if(!starter.isNegated()){\n";
                                *out << ind++ << "if(tuples->size() == 0 && tuplesU->size() == 0){\n";
                                    *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                    for(unsigned k : boundIndices){
                                        *out << k << "_";
                                    }
                                    *out << ".getValues({"<<boundTerms<<"});\n";
                                    *out << ind++ << "for(unsigned i=0; i<tuplesF->size(); i++){\n";
                                        *out << ind << "const auto& it = tupleToVar.find(*tuplesF->at(i));\n";
                                        *out << ind++ << "if(it!=tupleToVar.end())\n";
                                            *out << ind-- << "reasonForLiteral[-startVar].insert(-it->second);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "handleConflict(-startVar);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}else if(tuples->size() == 0 && tuplesU->size()==1){\n";
                                ind++;
                                    bool checkFormat=checkTupleFormat(*l,"tuplesU->at(0)",true);
                                    *out << ind << "const auto& itProp = tupleToVar.find(*tuplesU->at(0));\n";
                                    *out << ind++ << "if(itProp!=tupleToVar.end()){\n";
                                        *out << ind++ << "if(reasonForLiteral.count(itProp->second) == 0){\n";
                                            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                            for(unsigned k : boundIndices){
                                                *out << k << "_";
                                            }
                                            *out << ".getValues({"<<boundTerms<<"});\n";
                                            *out << ind++ << "for(unsigned i=0; i<tuplesF->size(); i++){\n";
                                                *out << ind << "const auto& it = tupleToVar.find(*tuplesF->at(i));\n";
                                                *out << ind++ << "if(it!=tupleToVar.end())\n";
                                                    *out << ind-- << "reasonForLiteral[itProp->second].insert(-it->second);\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "reasonForLiteral[itProp->second].insert(startVar);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                    *out << --ind << "}\n";
                                    if(checkFormat)
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                *out << ind++ << "if(tuples->size()>0){\n";
                                    // *out << ind << "std::cout<<\"Conflict: support found for negative head\"<<std::endl;\n";
                                    *out << ind << "const auto& it = tupleToVar.find(*tuples->at(0));\n";
                                    *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                        *out << ind << "reasonForLiteral[-it->second].insert(startVar);\n";
                                        *out << ind << "handleConflict(-it->second);\n";
                                        *out << ind << "return;\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    //NOTICE WORKS ONLY IF LITERALS WILL BE REMOVED FROM UNDEF IN PROP FUNCTION
                                    if(builder->isAuxPredicate(l->getPredicateName())){
                                        *out << ind++ << "while(!tuplesU->empty()){\n";
                                            *out << ind << "const auto& it = tupleToVar.find(*tuplesU->back());\n";

                                            //ONLY FOR DEBUG
                                            // *out << ind << "unsigned size = tuplesU->size();\n";
                                            //--------------
                                            *out << ind++ << "if(reasonForLiteral.count(-it->second) == 0 )\n";
                                                *out << ind-- << "reasonForLiteral[-it->second].insert(startVar);\n";
                                            // *out << ind << "unsigned previousSize = tuplesU->size();\n";
                                            *out << ind << "propUndefined(tuplesU->back(),false,propagationStack,true,propagatedLiterals);\n";
                                            // *out << ind << "if(presiousSize-propIndex==0) break;\n";
                                            // *out << ind++ << "if(previousSize==tupleU->size())\n";
                                            //     *out << ind-- << "propIndex++;\n";
                                            //ONLY FOR DEBUG
                                            //*out << ind << "if(size == tuplesU->size()) {std::cout<<\"loop\"<<std::endl;exit(180);}\n";
                                            //--------------
                                        *out << --ind << "}\n";
                                    }else{
                                        *out << ind++ << "for(unsigned i =0; i<tuplesU->size(); i++){\n";
                                            *out << ind << "const auto& it = tupleToVar.find(*tuplesU->at(i));\n";
                                            *out << ind++ << "if(reasonForLiteral.count(-it->second) == 0 )\n";
                                                *out << ind-- << "reasonForLiteral[-it->second].insert(startVar);\n";
                                            *out << ind << "propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);\n";
                                        *out << --ind << "}\n";
                                    }
                                    
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                        if(checkFormat)
                            *out << --ind << "}//close check format\n";
                    *out << --ind << "}//close if starter\n";

                }
            }
        }
    }
    if(!r.isConstraint()){
        if(!fromStarter){
            *out << ind++ << "{\n";

            const aspc::Literal* l = &r.getBodyLiterals()[0];
            const aspc::Atom* head = &r.getHead()[0];
            {
                //print support propagation
                std::unordered_set<std::string> boundVariables;
                *out << ind << "const std::vector<const Tuple*>* trueHeads = &p"<<head->getPredicateName()<<"_.getValues({});\n";
                *out << ind++ << "for(unsigned i = 0; i < trueHeads->size(); i++){\n";
                    *out << ind << "const Tuple* head = trueHeads->at(i);\n";
                    for(unsigned k = 0; k<head->getAriety(); k++){
                        if(head->isVariableTermAt(k) && boundVariables.count(head->getTermAt(k))==0){
                            *out << ind << "int "<<head->getTermAt(k)<<" = head->at("<<k<<");\n";
                            boundVariables.insert(head->getTermAt(k));
                        }
                    }
                    std::vector<unsigned> boundIndices;
                    std::string boundTerms;
                    for(unsigned k = 0; k<l->getAriety(); k++){
                        if(!l->isVariableTermAt(k) || boundVariables.count(l->getTermAt(k))!=0){
                            boundIndices.push_back(k);
                            if(boundTerms!="")
                                boundTerms+=",";
                            boundTerms+=l->getTermAt(k);
                        }
                    }
                    if(l->isBoundedLiteral(boundVariables)){
                        *out << ind << "const Tuple* tuple = w"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind++ << "if(tuple == NULL){\n";
                            *out << ind++ << "if(tupleU == NULL){\n";
                                *out << ind << "propagatedLiterals.insert(-1);\n";
                                //*out << ind << "std::cout<<\"Conflict at level -1: unable to find support for: \";head->print();std::cout<<std::endl;\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                *out << ind << "propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);\n";
                                *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                                *out << ind++ << "if(it != tupleToVar.end()){\n";
                                    // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                            *out << ind++ << "if(it != tupleToVar.end()){\n";
                                // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";

                    }else{

                        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                        for(unsigned k: boundIndices){
                            *out << k << "_";
                        }
                        *out << ".getValues({"<<boundTerms<<"});\n";

                        *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<l->getPredicateName()<<"_";
                        for(unsigned k: boundIndices){
                            *out << k << "_";
                        }
                        *out << ".getValues({"<<boundTerms<<"});\n";
                        *out << ind++ << "if(tuples->size() == 0){\n";

                            *out << ind++ << "if(tuplesU->size() == 0){\n";
                                *out << ind << "propagatedLiterals.insert(-1);\n";
                                //*out << ind << "std::cout<<\"Conflict at level -1: unable to find support for: \";head->print();std::cout<<std::endl;\n";
                            *out << --ind << "}else if(tuplesU->size() == 1){\n";
                            ind++;
                                *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                                *out << ind++ << "if(it != tupleToVar.end()){\n";
                                    // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}else{\n";
                        ind++;
                            *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                            *out << ind++ << "if(it != tupleToVar.end()){\n";
                                // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}\n";
                    }
                *out << --ind << "}\n";
            }
            {
                //print false head propagation
                std::unordered_set<std::string> boundVariables;
                *out << ind << "const std::vector<const Tuple*>* undefHeads = &u"<<head->getPredicateName()<<"_.getValues({});\n";
                *out << ind++ << "for(unsigned i = 0; i < undefHeads->size(); i++){\n";
                    *out << ind << "const Tuple* head = undefHeads->at(i);\n";
                    for(unsigned k = 0; k<head->getAriety(); k++){
                        if(head->isVariableTermAt(k) && boundVariables.count(head->getTermAt(k))==0){
                            *out << ind << "int "<<head->getTermAt(k)<<" = head->at("<<k<<");\n";
                            boundVariables.insert(head->getTermAt(k));
                        }
                    }
                    std::vector<unsigned> boundIndices;
                    std::string boundTerms;
                    for(unsigned k = 0; k<l->getAriety(); k++){
                        if(!l->isVariableTermAt(k) || boundVariables.count(l->getTermAt(k))!=0){
                            boundIndices.push_back(k);
                            if(boundTerms!="")
                                boundTerms+=",";
                            boundTerms+=l->getTermAt(k);
                        }
                    }
                    if(l->isBoundedLiteral(boundVariables)){
                        *out << ind << "const Tuple* tuple = w"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind++ << "if(tuple == NULL){\n";
                            *out << ind++ << "if(tupleU == NULL){\n";
                                *out << ind << "propUndefined(head,false,propagationStack,true,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            *out << ind << "propUndefined(head,false,propagationStack,false,propagatedLiterals);\n";
                            *out << ind << "const auto& it = tupleToVar.find(*head);\n";
                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                // *out << ind << "supportedLiterals[it->second]=cursrentDecisionLevel;\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";


                    }else{
                        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                        for(unsigned k: boundIndices){
                            *out << k << "_";
                        }
                        *out << ".getValues({"<<boundTerms<<"});\n";

                        *out << ind++ << "if(tuples->size() == 0){\n";

                            *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<l->getPredicateName()<<"_";
                            for(unsigned k: boundIndices){
                                *out << k << "_";
                            }
                            *out << ".getValues({"<<boundTerms<<"});\n";
                            *out << ind++ << "if(tuplesU->size() == 0){\n";
                                *out << ind << "propUndefined(head,false,propagationStack,true,propagatedLiterals);\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}else{\n";
                        ind++;
                            *out << ind << "propUndefined(head,false,propagationStack,false,propagatedLiterals);\n";
                            *out << ind << "const auto& it = tupleToVar.find(*head);\n";
                            *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}\n";

                    }
                *out << --ind << "}\n";
            }
            {
                //print false head propagation
                std::unordered_set<std::string> boundVariables;
                *out << ind << "const std::vector<const Tuple*>* falseHeads = &f"<<head->getPredicateName()<<"_.getValues({});\n";
                *out << ind++ << "for(unsigned i = 0; i < falseHeads->size(); i++){\n";
                    *out << ind << "const Tuple* head = falseHeads->at(i);\n";
                    for(unsigned k = 0; k<head->getAriety(); k++){
                        if(head->isVariableTermAt(k) && boundVariables.count(head->getTermAt(k))==0){
                            *out << ind << "int "<<head->getTermAt(k)<<" = head->at("<<k<<");\n";
                            boundVariables.insert(head->getTermAt(k));
                        }
                    }
                    std::vector<unsigned> boundIndices;
                    std::string boundTerms;
                    for(unsigned k = 0; k<l->getAriety(); k++){
                        if(!l->isVariableTermAt(k) || boundVariables.count(l->getTermAt(k))!=0){
                            boundIndices.push_back(k);
                            if(boundTerms!="")
                                boundTerms+=",";
                            boundTerms+=l->getTermAt(k);
                        }
                    }
                    if(l->isBoundedLiteral(boundVariables)){
                        *out << ind << "const Tuple* tuple = w"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(Tuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind++ << "if(tuple == NULL){\n";
                            *out << ind++ << "if(tupleU != NULL){\n";
                                *out << ind << "propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            //*out << ind << "std::cout<<\"Conflict at level -1: true body found for not \";head->print();std::cout<<std::endl;\n";
                            *out << ind << "propagatedLiterals.insert(-1);\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                        for(unsigned k: boundIndices){
                            *out << k << "_";
                        }
                        *out << ".getValues({"<<boundTerms<<"});\n";

                        *out << ind++ << "if(tuples->size() == 0){\n";

                            *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<l->getPredicateName()<<"_";
                            for(unsigned k: boundIndices){
                                *out << k << "_";
                            }
                            *out << ".getValues({"<<boundTerms<<"});\n";
                            //NOTICE WORKS ONLY IF PROP UNDEF REMOVES TUPLES FROM UNDEF
                            *out << ind++ << "for(unsigned j = 0; j < tuplesU->size();){\n";
                                *out << ind << "propUndefined(tuplesU->at(j),false,propagationStack,true,propagatedLiterals);\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}else{\n";
                        ind++;
                            //*out << ind << "std::cout<<\"Conflict at level -1: true body found for not \";head->print();std::cout<<std::endl;\n";
                            *out << ind << "propagatedLiterals.insert(-1);\n";

                        *out << --ind << "}\n";
                    }


                *out << --ind << "}\n";
            }
            *out << --ind << "}\n";

        }
    }
    if(r.isConstraint()){
        *out << ind++ << "{\n";
        std::vector<unsigned> starters;
        if(fromStarter){
            for(unsigned k: r.getStarters())
                if(k!=r.getBodySize())
                    starters.push_back(k);
        }else{
            starters.push_back(r.getBodySize());
        }

        for(unsigned i = 0; i<starters.size(); i++){
            unsigned starter = starters[i];

            // std::cout << "starter: "<< starter<<std::endl;
            std::unordered_set<std::string> boundVariables;
            unsigned closingPars=0;
            unsigned startJoining = 0;
            if(starter!=r.getBodySize()){
                const aspc::Atom* start=NULL;
                std::string sign = "!";
                if(starter < r.getBodySize()){
                    start = &((aspc::Literal*)r.getFormulas()[starter])->getAtom();
                    startJoining=1;
                    if(r.getFormulas()[starter]->isLiteral() && !r.getFormulas()[starter]->isPositiveLiteral())
                        sign="";
                }else{
                    start = &r.getHead()[0];
                }

                *out << ind++ << "if(starter.getPredicateName() == &_"<<start->getPredicateName()<<" && "<<sign<<"starter.isNegated()){\n";
                closingPars++;
                if(checkTupleFormat(aspc::Literal(sign=="",*start),"starter",false))
                    closingPars++;
                for(unsigned k = 0; k<start->getAriety(); k++){
                    if(start->isVariableTermAt(k) && boundVariables.count(start->getTermAt(k))==0){
                        *out << ind << "int "<<start->getTermAt(k)<<" = starter["<<k<<"];\n";
                        boundVariables.insert(start->getTermAt(k));
                    }
                }

            }else{
                *out << ind++ << "{\n";
                closingPars++;
            }
            *out << ind << "const Tuple* tupleU = NULL;\n";
            *out << ind << "bool tupleUNegated = false;\n";

            std::vector<const aspc::Formula*> oredered_body = r.getOrderedBodyByStarter(starter);
            for(unsigned index = startJoining; index<oredered_body.size();index++){
                if(oredered_body[index]->isLiteral()){
                    const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                    closingPars += exploreLiteral(l,boundVariables,index);

                }else if(oredered_body[index]->isBoundedValueAssignment(boundVariables)){
                    const aspc::ArithmeticRelation* ineq = (aspc::ArithmeticRelation*)oredered_body[index];
                    *out << ind << "int "<< ineq->getAssignmentStringRep(boundVariables)<<";\n";
                    boundVariables.insert(ineq->getAssignedVariable(boundVariables));

                }else if(oredered_body[index]->isBoundedRelation(boundVariables)){
                    const aspc::ArithmeticRelation* ineq = (aspc::ArithmeticRelation*)oredered_body[index];
                    *out << ind++ << "if("<< ineq->getStringRep()<<"){\n";
                    closingPars++;
                }
            }
            *out << ind++ << "if(tupleU != NULL){\n";
                if(fromStarter){
                    *out << ind << "const auto& itUndef = tupleToVar.find(*tupleU);\n";
                    *out << ind++ << "if(itUndef!=tupleToVar.end()){\n";
                        *out << ind << "int var = tupleUNegated ? 1 : -1;\n";
                        *out << ind << "var*=itUndef->second;\n";
                        // *out << ind << "std::cout<<\"compute reason for \"<<var<<std::endl;\n";
                        *out << ind++ << "if(reasonForLiteral.count(var) == 0){\n";

                            for(unsigned index = 0; index<oredered_body.size();index++){
                                if(oredered_body[index]->isLiteral()){
                                    const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                                    if(index>0 || startJoining == 0){
                                        *out << ind++ << "if(tuple"<<index<<"!=tupleU){\n";
                                        *out << ind << "const auto& it = tupleToVar.find(*tuple"<<index<<");\n";
                                    }else{
                                        *out << ind++ << "{\n";
                                        *out << ind << "const auto& it = tupleToVar.find(starter);\n";
                                    }
                                        *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                            std::string sign = l->isNegated() ? "-1" : "1";
                                            // *out << ind << "std::cout<<\"add to reason \"<<it->second*"<<sign<<"<<std::endl;\n";

                                            *out << ind << "reasonForLiteral[var].insert(it->second*"<<sign<<");\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                }
                            }
                        *out << --ind << "}\n";

                    *out << --ind << "}\n";
                }
                // *out << ind << "std::cout<<\"Constraint propagation\"<<std::endl;\n";
                *out << ind << "bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);\n";
            *out << --ind << "}else{\n";
            ind++;
                // *out << ind << "std::cout<<\"Conflict On Constraint "<<r.getRuleId()<<"\"<<std::endl;\n";
                if(fromStarter){
                    for(unsigned index = 1; index<oredered_body.size();index++){
                        if(oredered_body[index]->isLiteral()){
                            const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                            *out << ind++ << "if(tuple"<<index<<"!=NULL){\n";
                                *out << ind << "const auto& it = tupleToVar.find(*tuple"<<index<<");\n";
                                *out << ind++ << "if(it!=tupleToVar.end()){\n";
                                    std::string sign = l->isNegated() ? "-1" : "1";
                                    *out << ind << "reasonForLiteral[-startVar].insert(it->second*"<<sign<<");\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                    }
                    *out << ind << "handleConflict(-startVar);\n";
                    *out << ind << "return;\n";
                }else{
                    *out << ind << "propagatedLiterals.insert(-1);\n";
                }
            *out << --ind << "}\n";
            while(closingPars>0){
                closingPars--;
                *out << --ind << "}\n";
            }

        }
        *out << --ind << "}\n";
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