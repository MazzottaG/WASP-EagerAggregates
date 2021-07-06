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

    for(const aspc::Rule& r :builder->getRuleWithoutCompletion()){
        for(const aspc::Literal& l : r.getBodyLiterals()){
            bodyPredicatesNotCompletion.insert(l.getPredicateName());
        }
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: r.getArithmeticRelationsWithAggregate()){
            for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                bodyPredicatesNotCompletion.insert(l.getPredicateName());
            }
        }
    }
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
    *out << ind << "#include \"datastructures/TupleFactory.h\"\n\n";
    *out << ind << "#include \"datastructures/SmartPredicateSet.h\"\n\n";

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
    *out << ind << "typedef TupleWithReasons Tuple;\n";
    // if (programHasConstraint) {
    //     *out << ind << "typedef TupleWithReasons Tuple;\n";
    // } else {
    //     *out << ind << "typedef TupleWithoutReasons Tuple;\n";
    // }
    *out << ind << "typedef AuxiliaryMap<Tuple> AuxMap;\n";

    *out << ind << "typedef std::vector<const Tuple* > Tuples;\n";
    *out << ind << "using PredicateWSet = SmartPredicateSet;\n\n";

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
    std::set< pair<std::string, unsigned> > predicatesNotCompletion;

    for(const aspc::Rule& r :builder->getRuleWithoutCompletion()){
        for(const aspc::Literal& l : r.getBodyLiterals()){
            if(predicatesNotCompletion.count({l.getPredicateName(),l.getAriety()})==0 && aggregatePredicates.count({l.getPredicateName(),l.getAriety()})==0 && predicates.count({l.getPredicateName(),l.getAriety()})==0){
                *out << ind << "const std::string _" << l.getPredicateName() << " = \"" << l.getPredicateName() << "\";\n";
                *out << ind << "PredicateWSet w" << l.getPredicateName() << "(" << l.getAriety() << ");\n";
                *out << ind << "PredicateWSet u" << l.getPredicateName() << "(" << l.getAriety() << ");\n";
                *out << ind << "PredicateWSet f" << l.getPredicateName() << "(" << l.getAriety() << ");\n";
                predicatesNotCompletion.insert({l.getPredicateName(),l.getAriety()});
            }
        }
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation:r.getArithmeticRelationsWithAggregate()){
            for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                if(predicatesNotCompletion.count({l.getPredicateName(),l.getAriety()})==0 && aggregatePredicates.count({l.getPredicateName(),l.getAriety()})==0 && predicates.count({l.getPredicateName(),l.getAriety()})==0){
                    *out << ind << "const std::string _" << l.getPredicateName() << " = \"" << l.getPredicateName() << "\";\n";
                    *out << ind << "PredicateWSet w" << l.getPredicateName() << "(" << l.getAriety() << ");\n";
                    *out << ind << "PredicateWSet u" << l.getPredicateName() << "(" << l.getAriety() << ");\n";
                    *out << ind << "PredicateWSet f" << l.getPredicateName() << "(" << l.getAriety() << ");\n";
                    predicatesNotCompletion.insert({l.getPredicateName(),l.getAriety()});
                }
            }
        }
    }

    if(mode == EAGER_MODE){
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

    // *out << ind << "std::vector<Tuple> atomsTable;\n\n";
    // *out << ind << "std::unordered_map<int,int> waspIDMapping;\n\n";
    // *out << ind << "unsigned lastID=0;\n\n";
    *out << ind << "TupleFactory factory;\n";

    // *out << ind << "std::unordered_map<Tuple, unsigned, TuplesHash> tupleToVar;\n\n";

    *out << ind << "std::unordered_map<const std::string*, ExplainNegative> explainNegativeFunctionsMap;\n\n";

    *out << ind++ << "const std::string* parseTuple(const std::string & literalString,std::vector<int>& terms) {\n";

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
    // *out << ind << "std::vector<int> terms;\n";
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
    // *out << ind << "return Tuple(terms, stringToUniqueStringPointer[predicateName]);\n";
    *out << ind << "return stringToUniqueStringPointer[predicateName];\n";
    
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
    for(const aspc::Rule& r : builder->getRuleWithoutCompletion()){
        std::vector<unsigned> orderedFormulas;
        r.orderBodyFormulas(orderedFormulas);
        std::unordered_set<std::string> boundVariables;
        for(unsigned formulaIndex : orderedFormulas){
            if(!r.getFormulas()[formulaIndex]->containsAggregate()){
                if(r.getFormulas()[formulaIndex]->isLiteral()){
                    const aspc::Literal* l = (aspc::Literal*)r.getFormulas()[formulaIndex];
                    if(!l->isBoundedLiteral(boundVariables)){
                        std::string mapName=l->getPredicateName()+"_";
                        std::vector<unsigned> boundIndices;
                        for(unsigned k=0;k<l->getAriety();k++){
                            if(!l->isVariableTermAt(k) || boundVariables.count(l->getTermAt(k))!=0){
                                boundIndices.push_back(k);
                                mapName+=std::to_string(k)+"_";
                            }
                        }
                        if(declaredMaps.count(mapName)==0){
                            for(std::string c: {"p","u","f"}){
                                //std::cout<<c<<mapName<<std::endl;
                                *out << ind << "AuxMap "<< c << mapName << "({";
                                for (unsigned k = 0; k < boundIndices.size(); k++) {
                                    if (k > 0) {
                                        *out << ",";
                                    }
                                    *out << boundIndices[k];
                                }
                                *out << "});\n";

                            }
                            l->addVariablesToSet(boundVariables);
                            predicateToAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                            predicateToUndefAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                            predicateToFalseAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                            declaredMaps.insert(mapName);
                        }
                    }
                }
            }else{
                std::vector<aspc::Formula*> aggrFormulas;
                std::unordered_set<std::string> localBoundVariables(boundVariables);
                const aspc::ArithmeticRelationWithAggregate* aggrRelation=(aspc::ArithmeticRelationWithAggregate*)r.getFormulas()[formulaIndex];
                aggrRelation->getOrderedAggregateBody(aggrFormulas,localBoundVariables);
                for(const aspc::Formula* f : aggrFormulas){
                    if(f->isLiteral()){
                        const aspc::Literal* l = (aspc::Literal*)f;
                        if(!l->isBoundedLiteral(localBoundVariables)){
                            std::string mapName=l->getPredicateName()+"_";
                            std::vector<unsigned> boundIndices;
                            for(unsigned k=0;k<l->getAriety();k++){
                                if(!l->isVariableTermAt(k) || localBoundVariables.count(l->getTermAt(k))!=0){
                                    boundIndices.push_back(k);
                                    mapName+=std::to_string(k)+"_";
                                }
                            }
                            if(declaredMaps.count(mapName)==0){
                                for(std::string c: {"p","u","f"}){
                                    //std::cout<<c<<mapName<<std::endl;
                                    *out << ind << "AuxMap "<< c << mapName << "({";
                                    for (unsigned k = 0; k < boundIndices.size(); k++) {
                                        if (k > 0) {
                                            *out << ",";
                                        }
                                        *out << boundIndices[k];
                                    }
                                    *out << "});\n";

                                }
                                l->addVariablesToSet(localBoundVariables);
                                predicateToAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                                predicateToUndefAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                                predicateToFalseAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                                declaredMaps.insert(mapName);
                            }
                        }
                    }
                }
                for(unsigned k=0; k<aggrFormulas.size();k++){
                    delete aggrFormulas[k];
                }
            }
        }
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
        //*out << ind << "std::cout<<\"Handle conflict\"<<std::endl;\n";
        *out << ind++ << "if(currentDecisionLevel == -1){\n";
                        // *out << ind << "std::cout<<\"Inserting -1\"<<std::endl;\n";
            *out << ind << "propagatedLiterals.insert(-1);\n";
            *out << ind << "return;\n";
        *out << --ind << "}\n\n";
        *out << ind << "std::unordered_set<int> visitedLiterals;\n";
        *out << ind << "Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);\n";
        // *out << ind << "std::cout<<\"Explain \"<<literal<<\" \";l->print();std::cout<<std::endl;\n";
        *out << ind << "explainExternalLiteral(literal,conflictReason,visitedLiterals,true);\n";
        // *out << ind << "std::cout<<\"Explain \"<<-literal<<\" \";l->print();std::cout<<std::endl;\n";
        *out << ind << "explainExternalLiteral(-literal,conflictReason,visitedLiterals,true);\n";
                        // *out << ind << "std::cout<<\"Inserting -1\"<<std::endl;\n";
        *out << ind << "propagatedLiterals.insert(-1);\n";
        *out << ind << "reasonForLiteral.erase(literal);\n";
        // *out << ind++ << "for(unsigned i =0; i<conflictReason.size();i++){\n";
        //     *out << ind << "Tuple var = conflictReason[i] > 0 ?atomsTable[conflictReason[i]] : atomsTable[-conflictReason[i]];\n";
        //     *out << ind++ << "if(conflictReason[i]<0)\n";
        //         *out << ind-- << "std::cout<<\"~\";\n";
        //     *out << ind << "var.print();\n";
        //     *out << ind << "std::cout<<std::endl;\n";
        // *out << --ind << "}\n";
        //*out << ind << "std::cout<<\"Handle conflict end\"<<std::endl;\n";
        
    *out << --ind << "}\n";

    *out << ind++ << "int Executor::explainExternalLiteral(int var,UnorderedSet<int>& reas,std::unordered_set<int>& visitedLiteral,bool propagatorCall){\n";
        
        *out << ind++ << "if(!propagatorCall){\n";
            //*out << ind << "std::cout<<\"Explain from wasp \"<<var<<std::endl;\n";
            *out << ind << "int uVar = var>0 ? var : -var;\n";
            *out << ind << "int internalVar = factory.getTupleFromWASPID(uVar)->getId();\n";
            *out << ind << "var = var>0 ? internalVar : -internalVar;\n";
            // *out << ind << "std::cout<<\"Explain from wasp mapped \"<<var<<std::endl;\n";
            // *out << ind << "factory.getTupleFromInternalID(internalVar)->print();\n";
                
        *out << --ind << "}\n";
        *out << ind << "std::vector<int> stack;\n";
        *out << ind << "stack.push_back(var);\n";


        *out << ind++ << "while(!stack.empty()){\n";
            *out << ind << "int lit = stack.back();\n";
            *out << ind << "stack.pop_back();\n";
            
            *out << ind++ << "for(unsigned i = 0; i<reasonForLiteral[lit].size(); i++){\n";
                *out << ind << "int reasonLiteral=reasonForLiteral[lit][i];\n";

                *out << ind << "Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);\n";
                // *out << ind << "std::cout<<\"Reason Literal \"<<reasonLiteral<<\" \";literal->print();std::cout<<std::endl;\n";
                *out << ind++ << "if(visitedLiteral.count(reasonLiteral) == 0){\n";
                    *out << ind << "visitedLiteral.insert(reasonLiteral);\n";
                    *out << ind++ << "if(literal->getWaspID()==0){\n";
                        *out << ind << "stack.push_back(reasonLiteral);\n";
                        // *out << ind << "std::cout<<\"Internal lit\"<<std::endl;\n";
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind << "int sign = reasonLiteral>0 ? 1 : -1;\n";
                        // *out << ind << "std::cout<<\"External literal \"<<sign * literal->getWaspID()<<std::endl;\n";
                        *out << ind << "reas.insert(sign * literal->getWaspID());\n";
                    *out << --ind << "}\n";

                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        //*out << ind << "std::cout<<\"Reason for: \"<<var<<std::endl;\n";
        // *out << ind++ << "for(unsigned i=0; i<reas.size(); i++){\n";
        //     *out << ind << "Tuple* t = reas[i]>0 ? factory.getTupleFromWASPID(reas[i]) : factory.getTupleFromWASPID(-reas[i]);\n";
        //     *out << ind << "std::cout<<reas[i]<<\" \";t->print();std::cout<<std::endl;\n";
        // *out << --ind << "}\n";
        // *out << ind << "std::cout<<\"End explaining\"<<std::endl;\n";
        // *out << ind++ << "if(!propagatorCall) std::cout<<reas.size()<<std::endl;\n";
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
    *out << ind++ << "inline void Executor::onLiteralTrue(int var, const std::string& literalString) {\n";
        *out << ind << "std::vector<int> terms;\n";
        *out << ind << "const std::string* predicate = parseTuple(literalString,terms);\n";
        *out << ind << "Tuple* tuple = factory.addNewTuple(terms,predicate,var);\n";
        // *out << ind << "std::cout<<literalString<<\" Tuple: \";tuple->print();std::cout<<std::endl;\n";
        *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if(uSetIt!=predicateUSetMap.end()) {\n";
        *out << ind << "uSetIt->second->erase(*tuple);\n";
        *out << --ind << "}\n";

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if (it == predicateWSetMap.end()) {\n";
        *out << ind << "} else {\n";
            *out << ind++ << "if (var > 0) {\n";

                *out << ind << "const auto& insertResult = it->second->insert(tuple);\n";
                *out << ind++ << "if (insertResult.second) {\n";
                    // *out << ind << "std::cout<<\"added\"<<std::endl;\n";
                    *out << ind++ << "for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {\n";
                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if (fSetIt == predicateFSetMap.end()) {\n";
        *out << ind << "} else {\n";
            *out << ind++ << "if (var < 0) {\n";

                *out << ind << "const auto& insertResult = fSetIt->second->insert(tuple);\n";
                *out << ind++ << "if (insertResult.second) {\n";

                    *out << ind++ << "for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[fSetIt->first]) {\n";
                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

    *out << --ind << "}\n";
    *out << ind++ << "inline void Executor::onLiteralTrue(int var) {\n";
    if (mode == EAGER_MODE) {
        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "Tuple* tuple = factory.getTupleFromWASPID(uVar);\n";
        *out << ind << "std::unordered_map<const std::string*,int>::iterator sum_it;\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";

        // *out << ind << "std::cout<<\"True \"<<var<<std::endl;\n";
        // *out << ind << "std::cout<<\"True \"<<minus;tuple->print();std::cout<<std::endl;\n";
        // *out << ind << "if(reasonForLiteral.count(18)!=0)std::cout<<\"reason of 18 size: \"<<reasonForLiteral[18].size()<<std::endl;else std::cout<<\"reason of 18 not founded \"<<std::endl;\n";
        *out << ind << "unRoll=false;\n";

        *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator uSetIt = predicateUSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if(uSetIt!=predicateUSetMap.end()) {\n";
        *out << ind << "uSetIt->second->erase(*tuple);\n";
        *out << --ind << "}\n";

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateWSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if (it == predicateWSetMap.end()) {\n";
        *out << ind << "} else {\n";
            *out << ind++ << "if (var > 0) {\n";

                *out << ind << "const auto& insertResult = it->second->insert(tuple);\n";
                *out << ind++ << "if (insertResult.second) {\n";
                    *out << ind++ << "for (AuxMap* auxMap : predicateToAuxiliaryMaps[it->first]) {\n";
                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if (fSetIt == predicateFSetMap.end()) {\n";
        *out << ind << "} else {\n";
            *out << ind++ << "if (var < 0) {\n";

                *out << ind << "const auto& insertResult = fSetIt->second->insert(tuple);\n";
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
                *out << ind++ << "if(tuple->getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                    if(aggrId->getAriety() == 0){
                        *out << ind << "int itAggrId = factory.addNewInternalTuple({},&_"<<aggrId->getPredicateName()<<")->getId();\n";
                        *out << ind++ << "if(var>0)\n";
                            *out << ind-- << "actualSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                        *out << ind << "possibleSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                    }else{
                        std::string terms = "";
                        unsigned varIndex = 0;
                        for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                            if(varIndex>0){
                                terms+=",";
                            }
                            terms+="tuple->at("+std::to_string(var)+")";
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
                                    *out << ind << "int itAggrId = aggrIds->at(i)->getId();\n";
                                    *out << ind++ << "if(var>0)\n";
                                        *out << ind-- << "actualSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                                    *out << ind << "possibleSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
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
        // *out << ind << "std::cout<<\"Exit onLiteralTrue\"<<std::endl;\n";
        // *out << ind << "std::cout<<\"ActualSum aggr_id0: \"<<actualSum[factory.addNewInternalTuple({},&_aggr_id0)->getId()]<<std::endl;\n";
        // *out << ind << "std::cout<<\"ActualSum aggr_id1: \"<<actualSum[factory.addNewInternalTuple({},&_aggr_id1)->getId()]<<std::endl;\n";
        // *out << ind << "std::cout<<\"PossibleSum aggr_id0: \"<<possibleSum[factory.addNewInternalTuple({},&_aggr_id0)->getId()]<<std::endl;\n";
        // *out << ind << "std::cout<<\"PossibleSum aggr_id1: \"<<possibleSum[factory.addNewInternalTuple({},&_aggr_id1)->getId()]<<std::endl;\n";
    }

    *out << --ind << "}\n";


    // ---------------------- onLiteralUndef(int var) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralUndef(int var) {\n";
    if (mode == EAGER_MODE) {
        // *out << ind << "std::cout<<\"undef \"<<var<<std::endl;\n";
        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "Tuple* tuple = factory.getTupleFromWASPID(uVar);\n";
        *out << ind << "int internalVar = var > 0 ? tuple->getId() : -tuple->getId();\n";
        // *out << ind << "if(tuple->getPredicateName()==&_lives && tuple->at(0)==4 && tuple->at(1)==3){std::cout<<\"WASP id: \"<<var<<\" Internal id: \"<<internalVar<<std::endl;}\n";
        // *out << ind << "std::cout<<\"Removing from reason \"<<internalVar<<\" \"<<reasonForLiteral[internalVar].size()<<std::endl;\n";
        *out << ind << "reasonForLiteral.erase(internalVar);\n";
        // *out << ind << "reasonForLiteral.erase(-internalVar);\n";
        // *out << ind << "if(reasonForLiteral.count(internalVar)!=0)std::cout<<\"not removed \"<<internalVar<<\" \"<<reasonForLiteral[internalVar].size()<<std::endl;\n";
        
        // *out << ind << "reasonForLiteral.erase(-var);\n\n";
        // *out << ind << "unRoll=true;\n";

        *out << ind << "std::unordered_map<const std::string*,int>::iterator sum_it;\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";
        // *out << ind << "std::cout<<\"print undef \"<<var<<std::endl;\n";

        // *out << ind << "std::cout<<\"Undef \"<<minus;tuple->print();std::cout<<std::endl;\n";
        // *out << ind << "if(reasonForLiteral.count(18)!=0)std::cout<<\"reason of 18 size: \"<<reasonForLiteral[18].size()<<std::endl;else std::cout<<\"reason of 18 not founded \"<<std::endl;\n";
#ifdef EAGER_DEBUG
        *out << ind << "std::cout<<\"on literal undef \";\n";
        *out << ind << "std::cout<<var<<\"\\n\";\n";
        *out << ind << "tuple.print();\n";
        *out << ind << "std::cout<<\"\\n\";\n";
#endif

        *out << ind++ << "if (var > 0) {\n";
            *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple->getPredicateName());\n";
            *out << ind++ << "if (wSetIt != predicateWSetMap.end()) {\n";
                // *out << ind << "std::cout<<\"Erase from true\"<<std::endl;\n";
                *out << ind << "wSetIt->second->erase(*tuple);\n";
                // *out << ind << "if(wSetIt->second->find(tuple)!=NULL) std::cout<<\"Tuple not erased from true for \"<<tuple.getPredicateName()<<std::endl;\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        // *out << ind << "std::cout<<\"Erased from true\"<<std::endl;\n";

        *out << ind++ << "if (var < 0) {\n";
            *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());\n";
            *out << ind++ << "if (fSetIt != predicateWSetMap.end()) {\n";
                // *out << ind << "std::cout<<\"Erase from true\"<<std::endl;\n";
                *out << ind << "fSetIt->second->erase(*tuple);\n";
                // *out << ind << "if(wSetIt->second->find(tuple)!=NULL) std::cout<<\"Tuple not erased from true for \"<<tuple.getPredicateName()<<std::endl;\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        // *out << ind << "std::cout<<\"Erased from false\"<<std::endl;\n";

        *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple->getPredicateName());\n";
        *out << ind++ << "if (it == predicateUSetMap.end()) {\n";
        *out << ind << "} else {\n";

        *out << ind << "const auto& insertResult = it->second->insert(tuple);\n";
        *out << ind++ << "if (insertResult.second) {\n";

        // *out << ind << "std::cout<<\"Saved in undef\"<<std::endl;\n";
        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[it->first]) {\n";
        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << --ind << "}\n";

        *out << ind++ << "if(currentDecisionLevel >= 0){\n";
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
                *out << ind++ << "if(tuple->getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                    if(aggrId->getAriety() == 0){
                        *out << ind << "int itAggrId = factory.addNewInternalTuple({},&_"<<aggrId->getPredicateName()<<")->getId();\n";
                        *out << ind++ << "if(var>0)\n";
                            *out << ind-- << "actualSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                        *out << ind << "possibleSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                    }else{
                        std::string terms = "";
                        unsigned varIndex = 0;

                        for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                            if(varIndex > 0){
                                terms+=",";
                            }
                            terms+="tuple->at("+std::to_string(var)+")";
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
                                    *out << ind << "int itAggrId = aggrIds->at(i)->getId();\n";
                                    *out << ind++ << "if(var>0)\n";
                                        *out << ind-- << "actualSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                                    *out << ind << "possibleSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                    }
                *out << --ind << "}\n";
            }
        }
        *out << --ind << "}\n";
        //*out << ind<< "std::cout<<\"Exit undef\"<<std::endl;\n";

        // *out << ind << "std::cout<<\"ActualSum aggr_id0: \"<<actualSum[factory.addNewInternalTuple({},&_aggr_id0)->getId()]<<std::endl;\n";
        // *out << ind << "std::cout<<\"ActualSum aggr_id1: \"<<actualSum[factory.addNewInternalTuple({},&_aggr_id1)->getId()]<<std::endl;\n";
        // *out << ind << "std::cout<<\"PossibleSum aggr_id0: \"<<possibleSum[factory.addNewInternalTuple({},&_aggr_id0)->getId()]<<std::endl;\n";
        // *out << ind << "std::cout<<\"PossibleSum aggr_id1: \"<<possibleSum[factory.addNewInternalTuple({},&_aggr_id1)->getId()]<<std::endl;\n";
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
        GraphWithTarjanAlgorithm graph = builder->getGraphWithTarjanAlgorithm();
        std::vector<std::vector<int>> scc = graph.SCC();
        std::unordered_map<std::string,std::vector<aspc::Literal>> auxToBody(builder->getAuxPredicateBody());
        std::unordered_map<std::string,std::vector<aspc::ArithmeticRelation>> auxToInequality(builder->getAuxPredicateInequalities());

        for(int component=scc.size()-1; component>=0 ; component--){
            for(unsigned predId : scc[component]){
                auto it = vertexByID.find(scc[component][0]);
                if(it!=vertexByID.end()){
                    // std::cout<<it->second.name<<std::endl;
                    if(auxToBody.count(it->second.name)!=0){
                        std::unordered_set<unsigned> visitedLiterals;
                        std::unordered_set<unsigned> visitedIneqs;
                        std::unordered_set<std::string> boundVariables;
                        unsigned closingPars=0;
                        // std::cout<<"Generating aux"<<std::endl;
                        *out << ind++ << "{\n";
                        while (visitedLiterals.size()<auxToBody[it->second.name].size() || visitedIneqs.size()<auxToInequality[it->second.name].size()){
                            const aspc::ArithmeticRelation* selectedIneq=NULL;
                            const aspc::Literal* selectedLit=NULL;
                            unsigned selectedIndex=0;
                            for(unsigned i=0; i<auxToInequality[it->second.name].size() && visitedIneqs.size()<auxToInequality[it->second.name].size();i++){
                                if(visitedIneqs.count(i)==0){
                                    if(auxToInequality[it->second.name][i].isBoundedRelation(boundVariables) || auxToInequality[it->second.name][i].isBoundedValueAssignment(boundVariables)){
                                        selectedIneq = &auxToInequality[it->second.name][i];
                                        selectedIndex = i;
                                        break;
                                    }
                                }
                            }
                            if(selectedIneq != NULL){
                                // std::cout<<"current formula is ineq"<<std::endl;

                                if(selectedIneq->isBoundedValueAssignment(boundVariables)){
                                    *out << ind << "int " << selectedIneq->getAssignmentStringRep(boundVariables) << ";\n";
                                    selectedIneq->addVariablesToSet(boundVariables);
                                }
                                else{
                                    *out << ind++ << "if(" << selectedIneq->getStringRep() << "){\n";
                                    closingPars++;
                                }
                                visitedIneqs.insert(selectedIndex);
                            }else{

                                for(unsigned i=0; i<auxToBody[it->second.name].size() && visitedLiterals.size()<auxToBody[it->second.name].size();i++){
                                    if(visitedLiterals.count(i)==0){
                                        if(auxToBody[it->second.name][i].isBoundedLiteral(boundVariables)){
                                            selectedLit = &auxToBody[it->second.name][i];
                                            selectedIndex = i;
                                            break;
                                        }else if(auxToBody[it->second.name][i].isPositiveLiteral() && selectedLit==NULL){
                                            selectedLit = &auxToBody[it->second.name][i];
                                            selectedIndex = i;
                                        }
                                    }
                                }
                                if(selectedLit!=NULL){
                                    // std::cout<<"current formula is literal"<<std::endl;

                                    if(selectedLit->isBoundedLiteral(boundVariables)){
                                        *out << ind << "Tuple* boundTuple = factory.addNewInternalTuple({";
                                        for(unsigned i=0;i<selectedLit->getAriety();i++){
                                            if(i>0)
                                                *out << ",";
                                            *out << selectedLit->getTermAt(i);
                                        }
                                        *out << "}, &_"<<selectedLit->getPredicateName()<<");\n";
                                        if(selectedLit->isPositiveLiteral()){
                                            *out << ind++ << "if(u"<<selectedLit->getPredicateName()<<".find(*boundTuple)!=NULL || w"<<selectedLit->getPredicateName()<<".find(*boundTuple)!=NULL){\n";
                                        }else{
                                            *out << ind++ << "if(w"<<selectedLit->getPredicateName()<<".find(*boundTuple)==NULL){\n";
                                        }
                                        closingPars++;
                                    }else{
                                        *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<selectedLit->getPredicateName()<<"_";
                                        std::string boundTerms="";
                                        std::vector<unsigned> boundTermsIndices;
                                        for(unsigned i=0;i<selectedLit->getAriety();i++){
                                            if(!selectedLit->isVariableTermAt(i) || boundVariables.count(selectedLit->getTermAt(i))!=0){
                                                if(boundTerms!="")
                                                    boundTerms+=",";
                                                boundTerms+=selectedLit->getTermAt(i);
                                                *out << i << "_";
                                                boundTermsIndices.push_back(i);
                                            }
                                        }
                                        *out << ".getValues({"<<boundTerms<<"});\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesU = &u"<<selectedLit->getPredicateName()<<"_";
                                        for(unsigned index: boundTermsIndices){
                                            *out << index << "_";
                                        }
                                        *out << ".getValues({"<<boundTerms<<"});\n";
                                        *out << ind++ << "for(unsigned i = 0; i <tuples->size()+tuplesU->size(); i++){\n";
                                        closingPars++;
                                            *out << ind << "const Tuple* tuple = NULL;\n";
                                            *out << ind++ << "if(i<tuples->size())\n";
                                                *out << ind-- << "tuple=tuples->at(i);\n";
                                            *out << ind++ << "else\n";
                                                *out << ind-- << "tuple=tuplesU->at(i-tuples->size());\n";

                                            for(unsigned i=0;i<selectedLit->getAriety();i++){
                                                if(selectedLit->isVariableTermAt(i)){
                                                    if(boundVariables.count(selectedLit->getTermAt(i))==0){
                                                        *out << ind << "int "<<selectedLit->getTermAt(i)<<" = tuple->at("<<i<<");\n";
                                                        boundVariables.insert(selectedLit->getTermAt(i));
                                                    }else{
                                                        *out << ind++ << "if(tuple->at("<<i<<") == "<<selectedLit->getTermAt(i)<<"){\n";
                                                        closingPars++;
                                                    }
                                                }
                                            }
                                    }
                                    visitedLiterals.insert(selectedIndex);
                                }
                            }
                        }
                        // std::cout<<"AuxBody visited"<<std::endl;
                        aspc::Literal aux(false,aspc::Atom(it->second.name,builder->getAuxPredicateTerms(it->second.name)));
                        std::string auxTerms;
                        for(unsigned k=0;k<aux.getAriety();k++){
                            if(k>0)
                                auxTerms += ",";
                            auxTerms += aux.getTermAt(k);
                        }
                        *out << ind << "Tuple* aux = factory.addNewInternalTuple({"<<auxTerms<< "}, &_"<<aux.getPredicateName()<<");\n";
                        *out << ind++ << "if(u"<<aux.getPredicateName()<<".find(*aux) == NULL){\n";
                            *out << ind << "const auto& insertResult = u"<<aux.getPredicateName()<<".insert(aux);\n";
                            *out << ind++ << "if (insertResult.second) {\n";
                                *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aux.getPredicateName()<<"]) {\n";
                                    *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                *out << --ind << "}\n";
                                // *out << ind << "aux.print();std::cout<<\" \"<<tupleToVar[aux]<<std::endl;\n";
                                for(const aspc::Rule& r : program.getRules()){
                                    if(!r.isConstraint() && !r.getBodyLiterals().empty() && r.getBodyLiterals()[0].getPredicateName()==it->second.name){
                                        // std::cout<<"store head for aux"<<std::endl;
                                        const aspc::Atom* head = &r.getHead()[0];
                                        std::string headTerms="";
                                        for(unsigned k=0; k<head->getAriety();k++){
                                            if(headTerms!="")
                                                headTerms+=",";
                                            headTerms+=head->getTermAt(k);
                                        }
                                        *out << ind++ << "{\n";
                                            *out << ind << "Tuple* head = factory.addNewInternalTuple({"<<headTerms<<"},&_"<<head->getPredicateName()<<");\n";
                                            *out << ind++ << "if(u"<<head->getPredicateName()<<".find(*head)==NULL){\n";
                                                *out << ind << "const auto& headInsertResult = u"<<head->getPredicateName()<<".insert(head);\n";
                                                *out << ind++ << "if (headInsertResult.second) {\n";
                                                    *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                                        *out << ind << "auxMap -> insert2(*headInsertResult.first);\n";
                                                    *out << --ind << "}\n";
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

                                                    *out << ind << "Tuple* aggr_id"<<aggr_r.getRuleId()<<" = factory.addNewInternalTuple({"<<aggrIdTerms<<"},&_"<<aggr_id->getPredicateName()<<");\n";
                                                    *out << ind++ << "if(u"<<aggr_id->getPredicateName()<<".find(*aggr_id"<<aggr_r.getRuleId()<<")==NULL){\n";
                                                        *out << ind << "const auto& aggrIdInsertResult = u"<<aggr_id->getPredicateName()<<".insert(aggr_id"<<aggr_r.getRuleId()<<");\n";
                                                        *out << ind++ << "if (aggrIdInsertResult.second) {\n";
                                                            *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr_id->getPredicateName()<<"]) {\n";
                                                                *out << ind << "auxMap -> insert2(*aggrIdInsertResult.first);\n";
                                                            *out << --ind << "}\n";
                                                        *out << --ind << "}\n";
                                                    *out << --ind << "}\n";
                                                }
                                            }
                                        *out << --ind << "}\n";
                                    }
                                }

                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                        //std::cout<<"Aux saved"<<std::endl;
                        while (closingPars>0){
                            *out << --ind << "}\n";
                            closingPars--;
                        }
                        *out << --ind << "}\n";
                    }else{
                        for(const aspc::Rule& r : program.getRules()){
                            if(!r.isConstraint() && r.getHead()[0].getPredicateName()==it->second.name && !r.containsAggregate()){
                                if(r.getBodyLiterals().size()==1 && auxToBody.count(r.getBodyLiterals()[0].getPredicateName())==0){
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
                                                *out << ind << "Tuple* head = factory.addNewInternalTuple({"<<terms<<"},&_"<<head->getPredicateName()<<");\n";
                                                *out << ind << "const auto& insertResult = w"<<head->getPredicateName()<<".insert(head);\n";
                                                *out << ind++ << "if (insertResult.second) {\n";
                                                    *out << ind++ << "for (AuxMap* auxMap : predicateToAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                    *out << --ind << "}\n";
                                                    // *out << ind << "aggrId.print();std::cout<<\" \"<<tupleToVar[aggrId]<<std::endl;\n";
                                                *out << --ind << "}\n";
                                                if(checkFormat)
                                                    *out << --ind << "}\n";
                                            *out << --ind << "}else{\n";
                                            ind++;
                                                *out << ind << "tuple=tuplesU->at(i-tuples->size());\n";
                                                checkFormat = checkTupleFormat(*bodyLit,"tuple",true);

                                                *out << ind << "Tuple* head = factory.addNewInternalTuple({"<<terms<<"},&_"<<head->getPredicateName()<<");\n";
                                                *out << ind << "const auto& insertResult = u"<<head->getPredicateName()<<".insert(head);\n";
                                                *out << ind++ << "if (insertResult.second) {\n";
                                                    *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                    *out << --ind << "}\n";
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
                                                        *out << ind << "Tuple* aggrId = factory.addNewInternalTuple({"<<terms<<"},&_"<<aggr_id->getPredicateName()<<");\n";
                                                        *out << ind << "const auto& insertResult = u"<<aggr_id->getPredicateName()<<".insert(aggrId);\n";
                                                        *out << ind++ << "if (insertResult.second) {\n";
                                                            *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggr_id->getPredicateName()<<"]) {\n";
                                                                *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                                            *out << --ind << "}\n";
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
                        }
                    }
                }
            }
        }
        //std::cout<<"End scc iteration"<<std::endl;
        for(const auto & aggrId : aggrIdToRule){
            if(program.getRule(aggrId.second).getBodyLiterals().empty()){
                *out << ind++ << "{\n";
                    *out << ind << "Tuple* aggrId = factory.addNewInternalTuple({},&_"<<aggrId.first<<");\n";
                    *out << ind << "const auto& insertResult = u"<<aggrId.first<<".insert(aggrId);\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<aggrId.first<<"]) {\n";
                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                        *out << --ind << "}\n";
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
                                *out << ind << "Tuple* head = factory.addNewInternalTuple({"<<terms<<"},&_"<<head->getPredicateName()<<");\n";
                                *out << ind << "const auto& insertResult = u"<<head->getPredicateName()<<".insert(head);\n";
                                *out << ind++ << "if (insertResult.second) {\n";
                                    *out << ind++ << "for (AuxMap* auxMap : predicateToUndefAuxiliaryMaps[&_"<<head->getPredicateName()<<"]) {\n";
                                        *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                                    *out << --ind << "}\n";
                                    // *out << ind << "head.print();std::cout<<\" \"<<tupleToVar[head]<<std::endl;\n";
                                *out << --ind << "}\n";

                            if(checkFormat)
                                *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                }
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
                            *out << ind << "int it = aggregateIds->at(i)->getId();\n";
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
                                *out << ind-- << "possibleSum[it]+=aggrSetTuples->at(j)->at("<<sumVar<<");\n";
                        
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";

                }
            }
        }
        // *out << ind++ << "for(int id :uroomTOcabinetSize.getTuplesId()){\n";
        //     *out << ind << "factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "std::cout<<std::endl;\n";
        // *out << --ind << "}\n";
        // *out << ind << "exit(0);\n";
        // *out << ind << "factory.print();\n";
        // *out << ind << "for(const Tuple* t : uaggr_set0.getTuples()){t->print();std::cout<<std::endl;}\n";
        // *out << ind << "std::cout<<\"Starting sum value\"<<std::endl;\n";
        // *out << ind++ << "for(auto pair : actualSum){\n";
        //     *out << ind << "factory.getTupleFromInternalID(pair.first)->print();\n";
        //     *out << ind << "std::cout<<\" ActualSum \"<<pair.second<<std::endl;\n";
        // *out << --ind <<"}\n";
        // *out << ind++ << "for(auto pair : possibleSum){\n";
        //     *out << ind << "factory.getTupleFromInternalID(pair.first)->print();\n";
        // *out << ind << "std::cout<<\"PossibleSum \"<<pair.second<<std::endl;\n";
        // *out << --ind <<"}\n";
    *out << --ind << "}\n";

    *out << ind++ << "inline void Executor::addedVarName(int var, const std::string & atom) {\n";
    // *out << ind << "atomsTable.resize(var+1);\n";
    // *out << ind << "atomsTable.insert(atomsTable.begin()+var, parseTuple(atom));\n";
    //waspIDMapping
    // *out << ind++ << "if(waspIDMapping.find(var)==waspIDMapping.end()){\n";
    //     *out << ind << "std::cout<<\"Added \"<<var<<\" \"<<atomsTable.size()<<std::endl;\n";
    //     *out << ind << "waspIDMapping[var]=atomsTable.size();\n";
    //     *out << ind << "atomsTable.push_back(parseTuple(atom));\n";
    //     *out << ind << "tupleToVar[atomsTable.back()]= var;\n";
    //     *out << ind << "if(var>lastID) lastID=var;\n";
    // *out << --ind << "}\n";
    // *out << ind << "std::cout<<\"Atoms table size: \"<<atomsTable.size()<<std::endl;\n";
        // *out << ind << "std::cout<<var<<\" \" << atom<<std::endl;\n";
        *out << ind << "std::vector<int> terms;\n";
        *out << ind << "const std::string* predicate = parseTuple(atom,terms);\n";
        *out << ind << "factory.addNewTuple(terms,predicate,var);\n";
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
    for (const pair<std::string, unsigned>& predicate : predicatesNotCompletion) {

        *out << ind << "predicateWSetMap[" << reference << "_" << predicate.first << "]=&w" << predicate.first << ";\n";
        if (mode == EAGER_MODE) {
            *out << ind << "predicateUSetMap[&_" << predicate.first << "]=&u" << predicate.first << ";\n";
            *out << ind << "predicateFSetMap[&_" << predicate.first << "]=&f" << predicate.first << ";\n";
        }
        *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = &_" << predicate.first << ";\n";
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
        
        *out << ind++ << "if(tupleU->getWaspID() == 0){\n";
            *out << ind << "bool propagated=false;\n";
            *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator falseSet = predicateFSetMap.find(tupleU->getPredicateName());\n";
            *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator undefSet = predicateUSetMap.find(tupleU->getPredicateName());\n";
            *out << ind << "std::unordered_map<const std::string*,PredicateWSet*>::iterator trueSet = predicateWSetMap.find(tupleU->getPredicateName());\n";

            *out << ind++ << "if(falseSet==predicateFSetMap.end()){\n";
                // *out << ind << "std::cout<<\"Unable to find false set for: \"<<tupleU->getPredicateName()<<std::endl;\n";
                *out << ind << "exit(180);\n";
            *out << -- ind << "}\n";

            *out << ind++ << "if(undefSet==predicateUSetMap.end()){\n";
                // *out << ind << "std::cout<<\"Unable to find undef set for: \"<<tupleU->getPredicateName()<<std::endl;\n";
                *out << ind << "exit(180);\n";
            *out << -- ind << "}\n";

            *out << ind++ << "if(trueSet==predicateWSetMap.end()){\n";
                // *out << ind << "std::cout<<\"Unable to find true set for: \"<<tupleU->getPredicateName()<<std::endl;\n";
                *out << ind << "exit(180);\n";
            *out << -- ind << "}\n";
            *out << ind++ << "if(isNegated == asNegative){\n";
                *out << ind++ << "if(falseSet->second->find(*tupleU)!=NULL){\n";
                    // *out << ind << "std::cout<<\"Conflict: Literal is already false\"<<std::endl;\n";
                    *out << ind << "return true;\n";
                *out << --ind << "}else if(undefSet->second->find(*tupleU)!=NULL){\n";
                ind++;
                    *out << ind << "undefSet->second->erase(*tupleU);\n";
                    *out << ind << "const auto& insertResult = trueSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));\n";
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
                                        *out << ind << "int itAggrId = factory.addNewInternalTuple({},&_"<<aggrId->getPredicateName()<<")->getId();\n";
                                        *out << ind << "actualSum[itAggrId]+=tupleU->at("<<sumVar<<");\n";
                                        *out << ind << "possibleSum[itAggrId]-=tupleU->at("<<sumVar<<");\n";
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
                                                    *out << ind << "int itAggrId = aggrIds->at(i)->getId();\n";
                                                    *out << ind << "actualSum[itAggrId]+=tupleU->at("<<sumVar<<");\n";
                                                    *out << ind << "possibleSum[itAggrId]-=tupleU->at("<<sumVar<<");\n";
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
                    *out << ind << "undefSet->second->erase(*tupleU);\n";
                    *out << ind << "const auto& insertResult = falseSet->second->insert(factory.getTupleFromInternalID(tupleU->getId()));\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        // *out << ind << "std::cout<<\"Saved in false pred set\"<<std::endl;\n";
                        *out << ind++ << "for (AuxMap* auxMap : predicateToFalseAuxiliaryMaps[falseSet->first]) {\n";
                            *out << ind << "auxMap -> insert2(*insertResult.first);\n";
                            // *out << ind << "std::cout<<\"Saved in false auxMap\"<<std::endl;\n";
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
                                        *out << ind << "int itAggrId = factory.addNewInternalTuple({},&_"<<aggrId->getPredicateName()<<")->getId();\n";
                                        *out << ind << "possibleSum[itAggrId]-=tupleU->at("<<sumVar<<");\n";
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
                                                    *out << ind << "int itAggrId = aggrIds->at(i)->getId();\n";
                                                    *out << ind << "possibleSum[itAggrId]-=tupleU->at("<<sumVar<<");\n";
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
                *out << ind << "int it = tupleU->getId();\n";
                *out << ind << "int sign = isNegated != asNegative ? -1 : 1;\n";
                *out << ind << "stack.push_back(sign*it);\n";
                *out << ind << "levelToIntLiterals[currentDecisionLevel].push_back(sign*it);\n";
            *out << --ind << "}\n";
        *out << --ind << "}else{\n";
        ind++;
            *out << ind << "int it = tupleU->getWaspID();\n";
            *out << ind << "int sign = isNegated == asNegative ? -1 : 1;\n";
            // *out << ind++ << "if(!propagatedLiterals.contains(-it*sign)){\n";

                // *out << ind << "std::cout<<\"Propagating external literal: \";\n";
                // *out << ind << "tupleU->print();\n";
                // *out << ind << "std::cout <<\" \"<<sign*it<<std::endl;\n";
                *out << ind << "propagatedLiterals.insert(it*sign);\n";
                // *out << ind << "for(int id : wtd.getTuplesId()){factory.getTupleFromInternalID(id)->print();std::cout<<std::endl;}\n";
                
            // *out << --ind << "}\n";

        *out << --ind << "}\n";
        *out << ind << "return false;\n";
    *out << --ind << "}\n";

    *out << ind++ << "void Executor::printInternalLiterals(){\n";
        for(std::string pred : builder->getPrintingPredicates()){
            *out << ind++ << "for(const Tuple* t : w"<<pred<<".getTuples()){\n";
                // *out << ind << "t->print();\n";
                // *out << ind << "std::cout<<std::endl;\n";
            *out << --ind << "}\n";
        }
        // *out << ind << "std::cout<<\"AtomsTable size: \"<<atomsTable.size()<<std::endl;\n";
        // *out << ind << "for(const auto& pair : answerSet) onLiteralTrue(pair.first,pair.second);\n";
        for(const aspc::Rule& r: builder->getRuleWithoutCompletion()){
            std::cout<<"Rule: "<<r.getRuleId()<<" without completion"<<std::endl;
            if(!r.isConstraint()){
            *out << ind++ << "{\n";
                *out << ind << "std::set<std::vector<int>> trueHeads;\n";
                std::vector<unsigned> orderedBodyFormulas;
                r.orderBodyFormulas(orderedBodyFormulas);
                std::unordered_set<std::string> boundVariables;
                unsigned closingPars=0;
                //std::cout<<"Formulas size "<<orderedBodyFormulas.size()<<std::endl;
                for(unsigned formulaIndex: orderedBodyFormulas){
                    const aspc::Formula* f = r.getFormulas()[formulaIndex];
                    if(!f->isLiteral() && !f->containsAggregate()){
                        f->print();
                        const aspc::ArithmeticRelation* ineq = (aspc::ArithmeticRelation*)f;
                        if(ineq->isBoundedValueAssignment(boundVariables)){
                            *out << ind << "int "<<ineq->getAssignmentStringRep(boundVariables)<<";\n";
                            ineq->addVariablesToSet(boundVariables);
                        }else{
                            *out << ind++ << "if("<<ineq->getStringRep()<<"){\n";
                            closingPars++;
                        }
                    }else if(f->isLiteral()){
                        const aspc::Literal* l = (aspc::Literal*)f;
                        if(f->isBoundedLiteral(boundVariables)){

                            *out << ind << "Tuple* boundTuple = factory.addNewInternalTuple({";
                            for(unsigned k = 0; k<l->getAriety(); k++){
                                if(k>0)
                                    *out << ",";
                                *out << l->getTermAt(k);
                            }
                            *out << "},&_"<<l->getPredicateName()<<");\n";
                            if(l->isNegated()){
                                *out << ind++ << "if(w"<<l->getPredicateName()<<".find(*boundTuple) == NULL && u"<<l->getPredicateName()<<".find(*boundTuple) == NULL){\n";
                                closingPars++;
                            }else{
                                *out << ind++ << "if(w"<<l->getPredicateName()<<".find(*boundTuple) != NULL){\n";
                                closingPars++;
                            }
                        }else{
                            *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                            std::string boundTerms="";
                            std::vector<unsigned> unBoundedIndices;
                            for(unsigned k = 0; k<l->getAriety(); k++){
                                if(!l->isVariableTermAt(k) || boundVariables.count(l->getTermAt(k))!=0){
                                    *out << k << "_";
                                    if(boundTerms!="")
                                        boundTerms+=",";
                                    boundTerms+=l->getTermAt(k);
                                }else{
                                    unBoundedIndices.push_back(k);
                                }
                            }
                            *out << ".getValues({"<<boundTerms<<"});\n";
                            *out << ind++ << "for(unsigned i=0; i<tuples->size();i++){\n";
                            closingPars++;
                                for(unsigned index:unBoundedIndices){
                                    if(boundVariables.count(l->getTermAt(index))==0){
                                        *out << ind << "int "<<l->getTermAt(index)<<" = tuples->at(i)->at("<<index<<");\n";
                                        boundVariables.insert(l->getTermAt(index));
                                    }else{
                                        *out << ind++ << "if(tuples->at(i)->at("<<index<<") == "<<l->getTermAt(index)<<"){\n";
                                        closingPars++;
                                    }
                                }
                                // *out << ind << "tuples->at(i)->print();std::cout<<\" Joining\"<<std::endl;\n";
                        }
                    }else{
                        std::vector<aspc::Formula*> aggrBodyFormulas;
                        const aspc::ArithmeticRelationWithAggregate* aggrRelation =(aspc::ArithmeticRelationWithAggregate*)r.getFormulas()[formulaIndex];
                        aggrRelation->getOrderedAggregateBody(aggrBodyFormulas,boundVariables);
                        std::unordered_set<std::string> localBoundVariables(boundVariables);
                        *out << ind << "std::set<std::vector<int>> aggrSetKey;\n";
                        *out << ind << "int aggregateValue=0;\n";
                        std::string exitCondition="";
                        std::string plusOne = aggrRelation->isPlusOne() ? "+1":"";
                        std::string negated = aggrRelation->isNegated() ? "!" :"";
                        
                        if(!aggrRelation->isNegated() && aggrRelation->getComparisonType()!=aspc::EQ){
                            exitCondition = " && aggregateValue < "+aggrRelation->getGuard().getStringRep()+plusOne;
                        }
                        unsigned localPars=0;
                        for(const aspc::Formula* fAggr:aggrBodyFormulas){
                            if(!fAggr->isLiteral() && !fAggr->containsAggregate()){
                                fAggr->print();
                                const aspc::ArithmeticRelation* ineq = (aspc::ArithmeticRelation*)fAggr;
                                if(ineq->isBoundedValueAssignment(localBoundVariables)){
                                    *out << ind << "int "<<ineq->getAssignmentStringRep(localBoundVariables)<<";\n";
                                    ineq->addVariablesToSet(localBoundVariables);
                                }else{
                                    *out << ind++ << "if("<<ineq->getStringRep()<<"){\n";
                                    localPars++;
                                }
                            }else if(fAggr->isLiteral()){
                                const aspc::Literal* l = (aspc::Literal*)fAggr;
                                if(fAggr->isBoundedLiteral(localBoundVariables)){

                                    *out << ind << "Tuple* boundTuple = factory.addNewInternalTuple({";
                                    for(unsigned k = 0; k<l->getAriety(); k++){
                                        if(k>0)
                                            *out << ",";
                                        *out << l->getTermAt(k);
                                    }
                                    *out << "},&_"<<l->getPredicateName()<<");\n";
                                    if(l->isNegated()){
                                        *out << ind++ << "if(w"<<l->getPredicateName()<<".find(*boundTuple) == NULL && u"<<l->getPredicateName()<<".find(*boundTuple) == NULL){\n";
                                        localPars++;
                                    }else{
                                        *out << ind++ << "if(w"<<l->getPredicateName()<<".find(*boundTuple) != NULL){\n";
                                        localPars++;
                                    }
                                }else{
                                    *out << ind << "const std::vector<const Tuple*>* tuples = &p"<<l->getPredicateName()<<"_";
                                    std::string boundTerms="";
                                    std::vector<unsigned> unBoundedIndices;
                                    for(unsigned k = 0; k<l->getAriety(); k++){
                                        if(!l->isVariableTermAt(k) || localBoundVariables.count(l->getTermAt(k))!=0){
                                            *out << k << "_";
                                            if(boundTerms!="")
                                                boundTerms+=",";
                                            boundTerms+=l->getTermAt(k);
                                        }else{
                                            unBoundedIndices.push_back(k);
                                        }
                                    }
                                    *out << ".getValues({"<<boundTerms<<"});\n";
                                    *out << ind++ << "for(unsigned i=0; i<tuples->size()"<<exitCondition<<";i++){\n";
                                    localPars++;
                                        for(unsigned index:unBoundedIndices){
                                            if(localBoundVariables.count(l->getTermAt(index))==0){
                                                *out << ind << "int "<<l->getTermAt(index)<<" = tuples->at(i)->at("<<index<<");\n";
                                                localBoundVariables.insert(l->getTermAt(index));
                                            }else{
                                                *out << ind++ << "if(tuples->at(i)->at("<<index<<") == "<<l->getTermAt(index)<<"){\n";
                                                localPars++;
                                            }
                                        }
                                        // *out << ind << "tuples->at(i)->print();std::cout<<\" Joining\"<<std::endl;\n";

                                }
                            }
                        }
                        *out << ind << "std::vector<int> aggrKey({";
                        bool first=true;
                        for(std::string v : aggrRelation->getAggregate().getAggregateVariables()){
                            if(!first)
                                *out << ",";
                            *out << v;
                            first=false;
                        }
                        *out << "});\n";
                        *out << ind++ << "if(aggrSetKey.count(aggrKey)==0){\n";
                            *out << ind << "aggrSetKey.insert(aggrKey);\n";
                            if(aggrRelation->getAggregate().isSum())
                                *out << ind << "aggregateValue+=aggrKey[0];\n";
                            else
                                *out << ind << "aggregateValue+=1;\n";
                        *out << --ind << "}\n";
                        while(localPars > 0){
                            *out << --ind << "}\n";
                            localPars--;
                        }
                        for(unsigned k=0;k<aggrBodyFormulas.size();k++){
                            delete aggrBodyFormulas[k];
                        }
                        *out << ind++ << "if("<<negated<<"aggregateValue "<<aggrRelation->getCompareTypeAsString()<<" "<<aggrRelation->getGuard().getStringRep()<<plusOne<<"){\n";
                        closingPars++;
                    }
                }
                *out << ind << "std::vector<int> head({";
                const aspc::Atom* head = &r.getHead()[0];
                for(unsigned k=0;k<head->getAriety();k++){
                    if(k>0)
                        *out << ",";
                    *out << head->getTermAt(k);
                }
                *out << "});\n";
                *out << ind++ << "if(trueHeads.count(head)==0){\n";
                    *out << ind << "std::cout<<\""<<head->getPredicateName()<<"(\"";
                    for(unsigned k=0;k<head->getAriety();k++){
                        if(k>0)
                            *out << "<<\",\"";
                        *out << "<<head["<<k<<"]";
                    }
                    *out << "<<\")\"<<std::endl;\n";
                *out << --ind << "}\n";
                while (closingPars>0){
                    *out << --ind << "}\n";
                    closingPars--;
                }

            *out << --ind << "}\n";
            }
        }
    *out << --ind << "}\n";

    *out << ind++ << "void Executor::unRollToLevel(int decisionLevel){\n";
        // *out << ind << "std::cout<<\"Unrolling to level: \"<<decisionLevel << \" \" <<currentDecisionLevel<<std::endl;\n";
        // *out << ind << "std::cout<<\"Literals not propagated: \"<<propagatedLiterals.size()<<std::endl;\n";

        *out << ind++ << "for(unsigned i = 0; i<propagatedLiterals.size(); i++){\n";
            // *out << ind << "std::cout<<\"Literal not propagated: \"<<propagatedLiterals[i] <<std::endl;\n";
            *out << ind << "int var = propagatedLiterals[i] > 0 ? propagatedLiterals[i] : -propagatedLiterals[i];\n";
            // *out << ind << "std::cout<<\"VAR: \"<<var <<std::endl;\n";
            *out << ind << "int sign = propagatedLiterals[i] > 0 ? -1 : 1;\n";
            *out << ind << "Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);\n";
            // *out << ind << "std::cout<<\"Internal \"<<sign*literalNotPropagated->getId()<<std::endl;\n";
            *out << ind++ << "if(literalNotPropagated!=NULL)\n";
                *out << ind-- << "reasonForLiteral.erase(sign*literalNotPropagated->getId());\n";
        *out << --ind << "}\n";
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
                *out << ind << "Tuple* tuple = factory.getTupleFromInternalID(uVar);\n";

                *out << ind++ << "if (var > 0) {\n";
                    *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator wSetIt = predicateWSetMap.find(tuple->getPredicateName());\n";
                    *out << ind++ << "if (wSetIt != predicateWSetMap.end()) {\n";
                        // *out << ind << "std::cout<<\"Removing true literal\"<<std::endl;\n";
                        *out << ind << "wSetIt->second->erase(*tuple);\n";
                    *out << --ind << "}\n";
                *out << --ind << "} //true removing\n";

                *out << ind++ << "if (var < 0) {\n";
                    *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator fSetIt = predicateFSetMap.find(tuple->getPredicateName());\n";
                    *out << ind++ << "if (fSetIt != predicateFSetMap.end()) {\n";
                        // *out << ind << "std::cout<<\"Removing false literal\"<<std::endl;\n";
                        *out << ind << "fSetIt->second->erase(*tuple);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}//false removing\n";

                *out << ind << "std::unordered_map<const std::string*, PredicateWSet*>::iterator it = predicateUSetMap.find(tuple->getPredicateName());\n";
                *out << ind++ << "if (it == predicateUSetMap.end()) {\n";
                *out << ind << "} else {\n";
                    *out << ind << "const auto& insertResult = it->second->insert(tuple);\n";
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
                        *out << ind++ << "if(tuple->getPredicateName() == &_"<<aggrSetPred.first<<"){\n";
                            if(aggrId->getAriety() == 0){
                                *out << ind << "int itAggrId = factory.addNewInternalTuple({},&_"<<aggrId->getPredicateName()<<")->getId();\n";
                                *out << ind++ << "if(var>0)\n";
                                    *out << ind-- << "actualSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                                *out << ind << "possibleSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                            }else{
                                std::string terms = "";
                                unsigned varIndex = 0;

                                for(unsigned var : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                                    if(varIndex > 0){
                                        terms+=",";
                                    }
                                    terms+="tuple->at("+std::to_string(var)+")";
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
                                            *out << ind << "int itAggrId = aggrIds->at(i)->getId();\n";
                                                *out << ind++ << "if(var>0)\n";
                                                    *out << ind-- << "actualSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                                                *out << ind << "possibleSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
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

        // *out << ind << "std::cout<<\"True aggr set\"<<std::endl;\n";
        // *out << ind++ << "for(int id : waggr_set0.getTuplesId())\n";
        //     *out << ind-- << "factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "std::cout<<std::endl;\n";
        // *out << ind << "std::cout<<\"Undef aggr set\"<<std::endl;\n";
        // *out << ind++ << "for(int id : uaggr_set0.getTuplesId())\n";
        //     *out << ind-- << "factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "std::cout<<std::endl;\n";
        //*out << ind << "std::cout<<\"End unroll\"<<std::endl;\n";
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
        //*out << ind << "std::cout<<\"OnFacts\"<<std::endl;\n";
        *out << ind << "std::vector<int> propagationStack;\n";
        *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
            // *out << ind << "std::cout<<\"facts: \"<<facts[i]<<std::endl;\n";
            *out << ind << "onLiteralTrue(facts[i]);\n";
            *out << ind << "int factVar = facts[i]>0 ? facts[i] : -facts[i];\n";
            *out << ind << "int minus = facts[i]<0 ? -1 : 1;\n";
            *out << ind << "propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());\n";
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
            // *out << ind << "std::cout<<\"level > -1\"<<std::endl;\n";
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
            // *out << ind << "std::cout<<\"level -1\"<<std::endl;\n";
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
            // *out << ind << "std::cout<<\"end level -1\"<<std::endl;\n";

        *out << --ind << "}//close decision level == -1\n";
        // *out << ind << "std::cout<<\"outOfDecisionLevel\"<<std::endl;\n";

        // *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
        //     *out << ind << "propagationStack.push_back(facts[i]);\n";
        // *out << --ind << "}\n";
        // *out << ind << "std::cout<<propagatedLiterals.size()<<std::endl;\n";
        *out << ind++ << "while(!propagationStack.empty()){\n";
            *out << ind << "int startVar = propagationStack.back();\n";
            *out << ind << "int uStartVar = startVar<0 ? -startVar : startVar;\n";
            *out << ind << "Tuple starter (*factory.getTupleFromInternalID(uStartVar));\n";
            *out << ind << "starter.setNegated(startVar<0);\n";
            *out << ind << "std::string minus = starter.isNegated() ? \"not \" : \"\";\n";
            //*out << ind << "std::cout<<minus;starter.print();std::cout<<\" Starter\"<<std::endl;\n";
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
                    // std::cout<<aggrId->getPredicateName()<<std::endl;
                    // for(unsigned v : sharedVarAggrIdAggrSet[aggrId->getPredicateName()]){
                    //     std::cout<<v << " ";
                    // }
                    // std::cout<<std::endl;
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
            *out << ind << "Tuple* negativeTuple = factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<lit->getPredicateName()<<");\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = w"<<lit->getPredicateName()<<".find(*negativeTuple);\n";
            *out << ind << "const Tuple* tupleUndef"<<currentLitIndex<<" = u"<<lit->getPredicateName()<<".find(*negativeTuple);\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<" == tupleUndef"<<currentLitIndex<<" && tupleUndef"<<currentLitIndex<<" == NULL)\n";
                *out << ind-- << "tuple"<<currentLitIndex<<" = negativeTuple;\n";
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
            *out << ind << "Tuple* positiveTuple = factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<lit->getPredicateName()<<");\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = w"<<lit->getPredicateName()<<".find(*positiveTuple);\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<" == tupleU && tupleU == NULL){\n";
                *out << ind << "tuple"<<currentLitIndex<<" = tupleU = u"<<lit->getPredicateName()<<".find(*positiveTuple);\n";
                *out << ind << "tupleUNegated=false;\n";
            *out << --ind << "}else if(tupleU!=NULL && tuple"<<currentLitIndex<<"==NULL && tupleU->getPredicateName() == &_"<<lit->getPredicateName()<<" && ! tupleUNegated){\n";
            ind++;
                *out << ind++ << "if(tupleU == u"<<lit->getPredicateName()<<".find(*positiveTuple)){\n";
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
        // if(lit->getPredicateName()=="aggr_set0"){
        //     *out << ind << "std::cout<<\"Undef size: \"<<tuplesU->size()<<std::endl;\n";
        //     *out << ind << "std::cout<<\"True size: \"<<tuples->size()<<std::endl;\n";
        // }
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
                // *out << ind << "std::cout<<\"Actual Sum: \"<<actualSum[uStartVar]<<std::endl;\n";

                *out << ind++ << "if(starter.isNegated()){\n";
                    if(aggregateRelation->getAggregate().isSum())
                        *out << ind++ << "if(actualSum[uStartVar]>="<<guard<<"){\n";
                    else
                       *out << ind++ << "if(tuples->size()>="<<guard<<"){\n";

                        //*out << ind << "std::cout<<\"Conflitct on aggregate start from aggrId false "<<r.getRuleId()<<"\"<<std::endl;\n";
                        *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                            *out << ind << "int it = tuples->at(i)->getId();\n";
                            *out << ind << "reasonForLiteral[-startVar].insert(it);\n";
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
                                    *out << ind << "int itProp =tuplesU->at(index)->getId();\n";
                                    *out << ind++ << "if(reasonForLiteral.count(-itProp)==0){\n";
                                        *out << ind++ << "if(reason.empty()){\n";
                                            *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                                *out << ind << "int it = tuples->at(i)->getId();\n";
                                                *out << ind << "reason.push_back(it);\n";
                                                *out << ind << "reasonForLiteral[-itProp].insert(it);\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "reason.push_back(startVar);\n";
                                            *out << ind << "reasonForLiteral[-itProp].insert(startVar);\n";
                                        *out << --ind << "}else{\n";
                                        ind++;
                                            *out << ind++ << "for(int reasonLit : reason)\n";
                                                *out << ind-- << "reasonForLiteral[-itProp].insert(reasonLit);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                                    *out << ind << "int itProp = tuplesU->at(index)->getId();\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-itProp)==0){\n";
                                        *out << ind++ << "if(reason.empty()){\n";
                                            *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                                *out << ind << "int it = tuples->at(i)->getId();\n";
                                                *out << ind << "reason.push_back(it);\n";
                                                *out << ind << "reasonForLiteral[-itProp].insert(it);\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "reason.push_back(startVar);\n";
                                            *out << ind << "reasonForLiteral[-itProp].insert(startVar);\n";
                                        *out << --ind << "}else{\n";
                                        ind++;
                                            *out << ind++ << "for(int reasonLit : reason)\n";
                                                *out << ind-- << "reasonForLiteral[-itProp].insert(reasonLit);\n";
                                        *out << --ind << "}\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                                *out << ind << "int it = tuples->at(i)->getId();\n";
                                *out << ind << "reason.push_back(it);\n";
                            *out << --ind << "}\n";
                            *out << ind << "reason.push_back(startVar);\n";
                            if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                                *out << ind++ << "while(!tuplesU->empty()){\n";
                                    *out << ind << "int itProp = tuplesU->at(0)->getId();\n";
                                    *out << ind++ << "if(reasonForLiteral.count(-itProp)==0){\n";
                                        *out << ind++ << "for(int reasonLit : reason)\n";
                                            *out << ind-- << "reasonForLiteral[-itProp].insert(reasonLit);\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,true,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            }else{
                                *out << ind++ << "for(unsigned i =0; i<tuplesU->size(); i++){\n";
                                    *out << ind << "int itProp = tuplesU->at(i)->getId();\n";
                                    *out << ind++ << "if(reasonForLiteral.count(-itProp)==0){\n";
                                        *out << ind++ << "for(int reasonLit : reason)\n";
                                            *out << ind-- << "reasonForLiteral[-itProp].insert(reasonLit);\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                        //*out << ind << "std::cout<<\"Conflitct on aggregate starting from aggrId true "<<r.getRuleId()<<"\"<<std::endl;\n";
                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                        *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                            *out << ind << "int it = tuplesF->at(i)->getId();\n";
                            *out << ind << "reasonForLiteral[-startVar].insert(-it);\n";
                        *out << --ind << "}\n";
                        *out << ind << "handleConflict(-startVar);\n";
                        *out << ind << "return;\n";
                    if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "for(unsigned index=0;index<tuplesU->size();){\n";
                                *out << ind++ << "if(actualSum[uStartVar]+possibleSum[uStartVar]-tuplesU->at(index)->at(0) < "<<guard<<"){\n";
                                    *out << ind << "int itProp = tuplesU->at(index)->getId();\n";
                                    *out << ind++ << "if(reasonForLiteral.count(itProp) == 0){\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                        *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                            *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                            *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "reasonForLiteral[itProp].insert(startVar);\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    // reason contains aggr_id and all aggr_set false
                                    *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
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
                                    *out << ind << "int itProp = tuplesU->at(index)->getId();\n";
                                    *out << ind++ << "if(reasonForLiteral.count(itProp) == 0){\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                        *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                            *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                            *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "reasonForLiteral[itProp].insert(startVar);\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    // reason contains aggr_id and all aggr_set false
                                    *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        }
                    *out << --ind << "}\n";
                    }else{
                        *out << --ind << "}else if(tuples->size() + tuplesU->size() == "<<guard<<"){\n";
                        ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "while(tuplesU->size()>0){\n";
                                *out << ind << "int itProp = tuplesU->at(0)->getId();\n";
                                *out << ind++ << "if(reasonForLiteral.count(itProp) == 0){\n";
                                    *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                        *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                        *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "reasonForLiteral[itProp].insert(startVar);\n";
                                *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                // reason contains aggr_id and all aggr_set false
                                *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        }else{
                            *out << ind++ << "for(unsigned index=0;index<tuplesU->size();index++){\n";
                                *out << ind << "int itProp = tuplesU->at(index)->getId();\n";
                                *out << ind++ << "if(reasonForLiteral.count(itProp) == 0){\n";
                                    *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                        *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                        *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "reasonForLiteral[itProp].insert(startVar);\n";
                                *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                // reason contains aggr_id and all aggr_set false
                                *out << ind << "propUndefined(tuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
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

        // *out << ind << "std::cout<<\"Propagation start from aggr_set\"<<std::endl;\n";
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
            // *out << ind << "std::cout<<\"AggrId true size: \"<<tuples->size()<<std::endl;\n";
            // *out << ind << "std::cout<<\"AggrId undef size: \"<<tuplesU->size()<<std::endl;\n";
            // *out << ind << "std::cout<<\"AggrId false size: \"<<tuplesF->size()<<std::endl;\n";
        
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
                *out << ind << "int aggrIdIt=tuples->at(i)->getId();\n";
                // *out << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << ind++ << "if(actualSum[aggrIdIt]+possibleSum[aggrIdIt] < "<<guard<<"){\n";
                else
                    *out << ind++ << "if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                    //*out << ind << "std::cout<<\"Conflitct on aggregate starting from true aggr id "<<r.getRuleId()<<"\"<<std::endl;\n";
                    if(fromStarter){
                        *out << ind << "int itProp = tuples->at(i)->getId();\n";
                        *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                        *out << ind++ << "for(unsigned j = 0; j < joinTuplesF->size(); j++){\n";
                            *out << ind << "int it = joinTuplesF->at(j)->getId();\n";
                            *out << ind << "reasonForLiteral[-itProp].insert(-it);\n";
                        *out << --ind << "}\n";
                        *out << ind << "handleConflict(-itProp);\n";
                        *out << ind << "return;\n";
                    }else{
                        // *out << ind << "std::cout<<\"Inserting -1\"<<std::endl;\n";
                        *out << ind << "propagatedLiterals.insert(-1);\n";
                    }
                if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size();){\n";
                            *out << ind << "if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at(0) >= "<<guard<<") {index++; continue;}\n";
                            *out << ind << "int itProp = joinTuplesU->at(index)->getId();\n";
                            *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 ){\n";
                                *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                    *out << ind << "int it =joinTuplesF->at(i)->getId();\n";
                                    *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i)->getId();\n";
                                *out << ind << "reasonForLiteral[itProp].insert(itAggrId);\n";
                            *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            // reason contains aggr_id and all aggr_set false
                            *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
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
                            *out << ind << "if(actualSum[aggrIdIt]+possibleSum[aggrIdIt]-joinTuplesU->at(index)->at("<<varIndex<<") >= "<<guard<<") {index++; continue;}\n";
                            *out << ind << "int itProp = joinTuplesU->at(index)->getId();\n";
                            *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 ){\n";
                                *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                    *out << ind << "int it = joinTuplesF->at(i)->getId();\n";
                                    *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i)->getId();\n";
                                *out << ind << "reasonForLiteral[itProp].insert(itAggrId);\n";
                            *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            // reason contains body, aggr_id and all aggr_set false
                            *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
                        *out << --ind << "}\n";
                    }
                    *out << --ind << "}\n";
                }else{

                    *out << --ind << "}else if(joinTuples->size() + joinTuplesU->size() == "<<guard<<"){\n";
                    ind++;
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        *out << ind++ << "while(joinTuplesU->size()>0){\n";
                            *out << ind << "int itProp = joinTuplesU->at(0)->getId();\n";
                            *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 ){\n";
                                *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                    *out << ind << "int it = joinTuplesF->at(i)->getId();\n";
                                    *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i)->getId();\n";
                                *out << ind << "reasonForLiteral[itProp].insert(itAggrId);\n";
                            *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            // reason contains body, aggr_id and all aggr_set false
                            *out << ind << "propUndefined(joinTuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size(); index++){\n";
                            *out << ind << "int itProp = joinTuplesU->at(index)->getId();\n";
                            *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 ){\n";
                                *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                    *out << ind << "int it = joinTuplesF->at(i)->getId();\n";
                                    *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i)->getId();\n";
                                *out << ind << "reasonForLiteral[itProp].insert(itAggrId);\n";
                            *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            // reason contains body, aggr_id and all aggr_set false
                            *out << ind << "propUndefined(joinTuplesU->at(index),false,propagationStack,false,propagatedLiterals);\n";
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
                *out << ind << "int aggrIdIt=tuplesF->at(i)->getId();\n";
                // *out << ind << "std::cout<<\"ActualSum: \"<<actualSum[aggrIdIt]<<std::endl;\n";
                // *out << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << ind++ << "if(actualSum[aggrIdIt] >= "<<guard<<"){\n";
                else
                    *out << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";
                    //*out << ind << "std::cout<<\"Conflitct on aggregate starting from false aggr id "<<r.getRuleId()<<"\"<<actualSum[aggrIdIt]<<std::endl;\n";
                    if(fromStarter){
                        *out << ind << "int itProp = tuplesF->at(i)->getId();\n";
                        *out << ind++ << "for(unsigned j =0; j< joinTuples->size(); j++){\n";
                            *out << ind << "int it = joinTuples->at(j)->getId();\n";
                            *out << ind << "reasonForLiteral[itProp].insert(it);\n";
                        *out << --ind << "}\n";
                        *out << ind << "handleConflict(itProp);\n";
                        *out << ind << "return;\n";
                    }else{
                        // *out << ind << "std::cout<<\"Inserting -1\"<<std::endl;\n";
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
                                *out << ind << "int itProp = joinTuplesU->at(index)->getId();\n";
                                *out << ind++ << "if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at(0) >= "<<guard<<"){\n";

                        }else{
                            *out << ind++ << "while(!joinTuplesU->empty()){\n";
                                *out << ind << "int itProp = joinTuplesU->at(0)->getId();\n";
                        }

                            *out << ind++ << "if(reasonForLiteral.count(-itProp) == 0 ){\n";
                                *out << ind++ << "if(reason.empty()){\n";
                                    *out << ind++ << "for(unsigned i =0; i< joinTuples->size(); i++){\n";
                                        *out << ind << "int it = joinTuples->at(i)->getId();\n";
                                        *out << ind << "reason.push_back(it);\n";
                                        *out << ind << "reasonForLiteral[-itProp].insert(it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                    *out << ind << "reason.push_back(-it);\n";
                                    *out << ind << "reasonForLiteral[-itProp].insert(-it);\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind++ << "for(int reasonLit : reason)\n";
                                        *out << ind-- << "reasonForLiteral[-itProp].insert(reasonLit);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                            *out << ind++ << "if(actualSum[aggrIdIt]+joinTuplesU->at(index)->at("<<varIndex<<") >= "<<guard<<"){\n";
                        }
                            *out << ind << "int itProp = joinTuplesU->at(index)->getId();\n";
                            *out << ind++ << "if(reasonForLiteral.count(-itProp) == 0 ){\n";
                                *out << ind++ << "if(reason.empty()){\n";
                                    *out << ind++ << "for(unsigned i =0; i< joinTuples->size(); i++){\n";
                                        *out << ind << "int it = joinTuples->at(i)->getId();\n";
                                        *out << ind << "reason.push_back(it);\n";
                                        *out << ind << "reasonForLiteral[-itProp].insert(it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                    *out << ind << "reason.push_back(-it);\n";
                                    *out << ind << "reasonForLiteral[-itProp].insert(-it);\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind++ << "for(int reasonLit : reason)\n";
                                        *out << ind-- << "reasonForLiteral[-itProp].insert(reasonLit);\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                *out << ind << "int aggrIdIt=tuplesU->at(i)->getId();\n";
                // *out << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << ind++ << "if(actualSum[aggrIdIt] >= "<<guard<<"){\n";
                else
                    *out << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";

                    *out << ind << "int itProp = tuplesU->at(i)->getId();\n";
                    *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 ){\n";
                        *out << ind++ << "for(unsigned j = 0; j < joinTuples->size(); j++){\n";
                            *out << ind << "int it = joinTuples->at(j)->getId();\n";
                            *out << ind << "reasonForLiteral[itProp].insert(it);\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                    *out << ind << "propUndefined(tuplesU->at(i),false,propagationStack,false,propagatedLiterals);\n";
                if(aggregateRelation->getAggregate().isSum())
                    *out << --ind << "}else if(actualSum[aggrIdIt] + possibleSum[aggrIdIt] < "<<guard<<"){\n";
                else
                    *out << --ind << "}else if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                ind++;
                    *out << ind << "int itProp = tuplesU->at(i)->getId();\n";
                    *out << ind++ << "if(reasonForLiteral.count(-itProp) == 0 ){\n";
                        *out << ind << "const std::vector<const Tuple*>* joinTuplesF = &f"<<mapName<<".getValues(sharedVar);\n";
                        *out << ind++ << "for(unsigned j = 0; j < joinTuplesF->size(); j++){\n";
                            *out << ind << "int it = joinTuplesF->at(j)->getId();\n";
                            *out << ind << "reasonForLiteral[-itProp].insert(-it);\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                    *out << ind << "propUndefined(tuplesU->at(i),false,propagationStack,true,propagatedLiterals);\n";
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
                            *out << ind << "Tuple* head = factory.addNewInternalTuple({";
                            for(unsigned k=0; k<head->getAriety(); k++){
                                if(k>0)
                                    *out << ",";
                                *out << head->getTermAt(k);
                            }
                            *out << "}, &_"<<head->getPredicateName()<<");\n";
                            *out << ind << "const Tuple* tupleU = u"<<head->getPredicateName()<<".find(*head);\n";
                            *out << ind++ << "if(w"<<head->getPredicateName()<<".find(*head) == tupleU && tupleU==NULL){\n";
                                //*out << ind << "std::cout<<\"Conflict: exists support for false head "<<r.getRuleId()<<"\"<<std::endl;\n";
                                *out << ind << "int it = head->getId();\n";
                                *out << ind << "reasonForLiteral[it].insert(startVar);\n";
                                *out << ind << "handleConflict(it);\n";
                                *out << ind << "return;\n";
                            *out << --ind << "}else if(tupleU != NULL){\n";
                            ind++;
                                *out << ind << "int it = head->getId();\n";
                                *out << ind++ << "if(reasonForLiteral.count(it) == 0 )\n";
                                    *out << ind-- << "reasonForLiteral[it].insert(startVar);\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                *out << ind << "propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);\n";
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
                            *out << ind << "Tuple* head = factory.addNewInternalTuple({";
                            for(unsigned k=0; k<head->getAriety(); k++){
                                if(k>0)
                                    *out << ",";
                                *out << head->getTermAt(k);
                            }
                            *out << "}, &_"<<head->getPredicateName()<<");\n";
                            if(l->isBoundedLiteral(headVariables)){
                                *out << ind++ << "if(w"<<head->getPredicateName()<<".find(*head) != NULL){\n";
                                    //*out << ind << "std::cout<<\"Conflict: unsupported head atom "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "int it = head->getId();\n";
                                    *out << ind << "reasonForLiteral[-it].insert(startVar);\n";
                                    *out << ind << "handleConflict(-it);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind << "const Tuple* tupleU = u"<<head->getPredicateName()<<".find(*head);\n";
                                    *out << ind++ << "if(tupleU!=NULL){\n";
                                        *out << ind << "int it = head->getId();\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-it) == 0 )\n";
                                            *out << ind-- << "reasonForLiteral[-it].insert(startVar);\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        *out << ind << "propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);\n";
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
                                *out << ind++ << "if(w"<<head->getPredicateName()<<".find(*head) != NULL){\n";
                                    *out << ind++ << "if(tuples->size()==0 && tuplesU->size()==0){\n";
                                        //*out << ind << "std::cout<<\"Conflict: unable to find support for true head "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        *out << ind << "int itHead = head->getId();\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                        for(unsigned k : boundIndices){
                                            *out << k << "_";
                                        }
                                        *out << ".getValues({"<<boundTerms<<"});\n";
                                        *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                            *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                            *out << ind << "reasonForLiteral[-itHead].insert(-it);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "handleConflict(-itHead);\n";
                                        *out << ind << "return;\n";
                                    *out << --ind << "}else if(tuples->size() == 0 && tuplesU->size() == 1){\n";
                                    ind++;
                                        *out << ind << "int itProp = tuplesU->at(0)->getId();\n";
                                        *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 ){\n";
                                            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                            for(unsigned k : boundIndices){
                                                *out << k << "_";
                                            }
                                            *out << ".getValues({"<<boundTerms<<"});\n";
                                            *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                                *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                                *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                            *out << --ind << "}\n";
                                            *out << ind << "int it = head->getId();\n";
                                            *out << ind << "reasonForLiteral[itProp].insert(it);\n";
                                        *out << --ind << "}\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind << "const Tuple* tupleU = u"<<head->getPredicateName()<<".find(*head);\n";
                                    *out << ind++ << "if(tupleU != NULL && tuples->size() == 0 && tuplesU->size() == 0){\n";
                                        *out << ind << "int itHead = head->getId();\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-itHead) == 0 ){\n";
                                            *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                            for(unsigned k : boundIndices){
                                                *out << k << "_";
                                            }
                                            *out << ".getValues({"<<boundTerms<<"});\n";
                                            *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                                *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                                *out << ind << "reasonForLiteral[-itHead].insert(-it);\n";
                                            *out << --ind << "}\n";
                                        *out << --ind << "}\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        *out << ind << "propUndefined(tupleU,false,propagationStack,true,propagatedLiterals);\n";
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
                            *out << ind << "const Tuple* tuple = factory.addNewInternalTuple({"<<boundTerms<<"}, &_"<<l->getPredicateName()<<");\n";
                            *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(*tuple);\n";
                            *out << ind++ << "if(!starter.isNegated()){\n";
                                *out << ind++ << "if(w"<<l->getPredicateName()<<".find(*tuple) == tupleU && tupleU==NULL){\n";
                                    //*out << ind << "std::cout<<\"Conflict: unable to find support for true head "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "int it = tuple->getId();\n";
                                    *out << ind << "reasonForLiteral[it].insert(startVar);\n";
                                    *out << ind << "handleConflict(it);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind++ << "if(tupleU!=NULL){\n";
                                        *out << ind << "int it = tuple->getId();\n";
                                        *out << ind++ << "if(reasonForLiteral.count(it) == 0 )\n";
                                            *out << ind-- << "reasonForLiteral[it].insert(startVar);\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        *out << ind << "propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);\n";
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                *out << ind++ << "if(w"<<l->getPredicateName()<<".find(*tuple)!=NULL){\n";
                                    //*out << ind << "std::cout<<\"Conflict: support found for false head "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "int it = tuple->getId();\n";
                                    *out << ind << "reasonForLiteral[-it].insert(startVar);\n";
                                    *out << ind << "handleConflict(-it);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    *out << ind++ << "if(tupleU!=NULL){\n";
                                        *out << ind << "int it = tuple->getId();\n";
                                        *out << ind++ << "if(reasonForLiteral.count(-it) == 0)\n";
                                            *out << ind-- << "reasonForLiteral[-it].insert(startVar);\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                            *out << ind++ << "if(!starter.isNegated()){\n";
                                *out << ind++ << "if(tuples->size() == 0 && tuplesU->size() == 0){\n";
                                    *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                    for(unsigned k : boundIndices){
                                        *out << k << "_";
                                    }
                                    *out << ".getValues({"<<boundTerms<<"});\n";
                                    *out << ind++ << "for(unsigned i=0; i<tuplesF->size(); i++){\n";
                                        *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                        *out << ind << "reasonForLiteral[-startVar].insert(-it);\n";
                                    *out << --ind << "}\n";
                                    //*out << ind << "std::cout<<\"conflict on rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "handleConflict(-startVar);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}else if(tuples->size() == 0 && tuplesU->size()==1){\n";
                                ind++;
                                    bool checkFormat=checkTupleFormat(*l,"tuplesU->at(0)",true);
                                    *out << ind << "int itProp = tuplesU->at(0)->getId();\n";
                                    *out << ind++ << "if(reasonForLiteral.count(itProp) == 0){\n";
                                        *out << ind << "const std::vector<const Tuple*>* tuplesF = &f"<<l->getPredicateName()<<"_";
                                        for(unsigned k : boundIndices){
                                            *out << k << "_";
                                        }
                                        *out << ".getValues({"<<boundTerms<<"});\n";
                                        *out << ind++ << "for(unsigned i=0; i<tuplesF->size(); i++){\n";
                                            *out << ind << "int it = tuplesF->at(i)->getId();\n";
                                            *out << ind << "reasonForLiteral[itProp].insert(-it);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "reasonForLiteral[itProp].insert(startVar);\n";
                                    *out << --ind << "}\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                    if(checkFormat)
                                    *out << --ind << "}\n";
                                *out << --ind << "}\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                *out << ind++ << "if(tuples->size()>0){\n";
                                    //*out << ind << "std::cout<<\"Conflict: support found for negative head "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    *out << ind << "int it = tuples->at(0)->getId();\n";
                                    *out << ind << "reasonForLiteral[-it].insert(startVar);\n";
                                    *out << ind << "handleConflict(-it);\n";
                                    *out << ind << "return;\n";
                                *out << --ind << "}else{\n";
                                ind++;
                                    //NOTICE WORKS ONLY IF LITERALS WILL BE REMOVED FROM UNDEF IN PROP FUNCTION
                                    if(builder->isAuxPredicate(l->getPredicateName())){
                                        *out << ind++ << "while(!tuplesU->empty()){\n";
                                            *out << ind << "int it = tuplesU->back()->getId();\n";

                                            //ONLY FOR DEBUG
                                            // *out << ind << "unsigned size = tuplesU->size();\n";
                                            //--------------
                                            *out << ind++ << "if(reasonForLiteral.count(-it) == 0 )\n";
                                                *out << ind-- << "reasonForLiteral[-it].insert(startVar);\n";
                                            // *out << ind << "unsigned previousSize = tuplesU->size();\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                                            *out << ind << "int it = tuplesU->at(i)->getId();\n";
                                            *out << ind++ << "if(reasonForLiteral.count(-it) == 0 )\n";
                                                *out << ind-- << "reasonForLiteral[-it].insert(startVar);\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                        *out << ind << "const Tuple* tuple = w"<<l->getPredicateName()<<".find(*factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(*factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind++ << "if(tuple == NULL){\n";
                            *out << ind++ << "if(tupleU == NULL){\n";
                                *out << ind << "propagatedLiterals.insert(-1);\n";
                                //*out << ind << "std::cout<<\"Conflict at level -1: unable to find support for: \";head->print();std::cout<<std::endl;\n";
                            *out << --ind << "}else{\n";
                            ind++;
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                *out << ind << "propUndefined(tupleU,false,propagationStack,false,propagatedLiterals);\n";
                                // *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                                // *out << ind++ << "if(it != tupleToVar.end()){\n";
                                //     // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                                // *out << --ind << "}\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            // *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                            // *out << ind++ << "if(it != tupleToVar.end()){\n";
                            //     // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                            // *out << --ind << "}\n";
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
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                *out << ind << "propUndefined(tuplesU->at(0),false,propagationStack,false,propagatedLiterals);\n";
                                // *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                                // *out << ind++ << "if(it != tupleToVar.end()){\n";
                                //     // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                                // *out << --ind << "}\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}else{\n";
                        ind++;
                            // *out << ind << "const auto & it = tupleToVar.find(*head);\n";
                            // *out << ind++ << "if(it != tupleToVar.end()){\n";
                            //     // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                            // *out << --ind << "}\n";

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
                        *out << ind << "const Tuple* tuple = w"<<l->getPredicateName()<<".find(*factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(*factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind++ << "if(tuple == NULL){\n";
                            *out << ind++ << "if(tupleU == NULL){\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                *out << ind << "propUndefined(head,false,propagationStack,true,propagatedLiterals);\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}else{\n";
                        ind++;
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            *out << ind << "propUndefined(head,false,propagationStack,false,propagatedLiterals);\n";
                            // *out << ind << "const auto& it = tupleToVar.find(*head);\n";
                            // *out << ind++ << "if(it!=tupleToVar.end()){\n";
                            //     // *out << ind << "supportedLiterals[it->second]=cursrentDecisionLevel;\n";
                            // *out << --ind << "}\n";
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
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                *out << ind << "propUndefined(head,false,propagationStack,true,propagatedLiterals);\n";
                            *out << --ind << "}\n";

                        *out << --ind << "}else{\n";
                        ind++;
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            *out << ind << "propUndefined(head,false,propagationStack,false,propagatedLiterals);\n";
                            // *out << ind << "const auto& it = tupleToVar.find(*head);\n";
                            // *out << ind++ << "if(it!=tupleToVar.end()){\n";
                            //     // *out << ind << "supportedLiterals[it->second]=currentDecisionLevel;\n";
                            // *out << --ind << "}\n";

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
                        *out << ind << "const Tuple* tuple = w"<<l->getPredicateName()<<".find(*factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind << "const Tuple* tupleU = u"<<l->getPredicateName()<<".find(*factory.addNewInternalTuple({"<<boundTerms<<"},&_"<<l->getPredicateName()<<"));\n";
                        *out << ind++ << "if(tuple == NULL){\n";
                            *out << ind++ << "if(tupleU != NULL){\n";
                                //*out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                            //*out << ind << "std::cout<<\"propagation from rule "<<r.getRuleId()<<"\"<<std::endl;\n";
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
                    *out << ind << "int itUndef = tupleU->getId();\n";
                    *out << ind << "int var = tupleUNegated ? 1 : -1;\n";
                    *out << ind << "var*=itUndef;\n";
                    // *out << ind << "std::cout<<\"compute reason for \"<<var<<std::endl;\n";
                    *out << ind++ << "if(reasonForLiteral.count(var) == 0){\n";

                        for(unsigned index = 0; index<oredered_body.size();index++){
                            if(oredered_body[index]->isLiteral()){
                                const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                                if(index>0 || startJoining == 0){
                                    *out << ind++ << "if(tuple"<<index<<"!=tupleU){\n";
                                    *out << ind << "int it = tuple"<<index<<"->getId();\n";
                                }else{
                                    *out << ind++ << "{\n";
                                    *out << ind << "int it = starter.getId();\n";
                                }
                                    std::string sign = l->isNegated() ? "-1" : "1";
                                        // *out << ind << "std::cout<<\"add to reason of \"<<var<<\": \"<<it*"<<sign<<"<<std::endl;\n";
                                    *out << ind << "reasonForLiteral[var].insert(it*"<<sign<<");\n";
                                *out << --ind << "}\n";
                            }
                        }
                    *out << --ind << "}else{\n";
                    ind++;
                        //*out << ind << "std::cout<<\"Reason of \"<<var<<\"already computed \"<<reasonForLiteral[var].size()<<\" \"<<std::endl;\n";
                        // *out << ind << "if(reasonForLiteral[var].size()>0){std::cout<<reasonForLiteral[var][0]<<std::endl;}else{std::cout<<\"Found empty reason\"<<std::endl;}\n";
                        // *out << ind << "UnorderedSet<int> rrrrrr;\n";
                        // *out << ind << "std::unordered_set<int> visitedLiteralssssssss;\n"; 
                        // *out << ind << "explainExternalLiteral(tupleU->getId(),rrrrrr,visitedLiteralssssssss,true);\n";
                    *out << --ind << "}\n";
                }
                //*out << ind << "std::cout<<\"Constraint propagation "<<r.getRuleId()<<"\"<<std::endl;\n";
                *out << ind << "bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals);\n";
                // *out << ind << "UnorderedSet<int> rrrrrr;\n";
                // *out << ind << "std::unordered_set<int> visitedLiteralssssssss;\n"; 
                // *out << ind << "int it = tupleU->getId();\n";
                // *out << ind << "int sign = tupleUNegated == true ? 1 : -1;\n";
                // *out << ind << "explainExternalLiteral(it*sign,rrrrrr,visitedLiteralssssssss,true);\n";
            *out << --ind << "}else{\n";
            ind++;
                //*out << ind << "std::cout<<\"Conflict On Constraint "<<r.getRuleId()<<"\"<<std::endl;\n";
                if(fromStarter){
                    for(unsigned index = 1; index<oredered_body.size();index++){
                        if(oredered_body[index]->isLiteral()){
                            const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                            *out << ind++ << "if(tuple"<<index<<"!=NULL){\n";
                                *out << ind << "int it = tuple"<<index<<"->getId();\n";
                                std::string sign = l->isNegated() ? "-1" : "1";
                                *out << ind << "reasonForLiteral[-startVar].insert(it*"<<sign<<");\n";
                            *out << --ind << "}\n";
                        }
                    }
                    *out << ind << "handleConflict(-startVar);\n";
                    *out << ind << "return;\n";
                }else{
                        // *out << ind << "std::cout<<\"Inserting -1\"<<std::endl;\n";
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
const std::set<std::string>& CompilationManager::getBodyPredicatesNotCompletion() {
    return bodyPredicatesNotCompletion;
}