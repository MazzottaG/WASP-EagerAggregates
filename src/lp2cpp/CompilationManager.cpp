/*
 *
 *  Copyright 2021  BLIND.
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

    std::cout << "lp2cpp"<<std::endl;
    generateStratifiedCompilableProgram(builder->getProgram(), builder);
    delete builder;
}

void CompilationManager::loadProgram(const std::string& filename) {
    DLV2::InputDirector director;
    std::cout << "loadProgram"<<std::endl;
    builder = new AspCore2ProgramBuilder();
    director.configureBuilder(builder);
    std::vector<const char*> fileNames;
    fileNames.push_back(filename.c_str());
    director.parse(fileNames);
    bodyPredicates = builder->getBodyPredicates();
    aspc::EagerProgram* lazy = &builder->getEndProgram();
    for(const aspc::Rule& r :lazy->getRules()){
        for(const aspc::Literal& l : r.getBodyLiterals()){
            bodyPredicatesNotCompletion.insert(l.getPredicateName());
        }
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: r.getArithmeticRelationsWithAggregate()){
            for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                bodyPredicatesNotCompletion.insert(l.getPredicateName());
            }
        }
    }
    headPredicates = builder->getHeadPredicates();

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
                *out << ind << "const auto& find = neg_w" << lit.getPredicateName() << ".find(Tuple(lit, _" << lit.getPredicateName() << "));\n";
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
            conditions+=tupleName+point+"at("+std::to_string(i)+")==";
            conditions+= isInteger(li.getTermAt(i)) ? li.getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+li.getTermAt(i)+"\")";
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

}
void CompilationManager::declareAuxMap(std::string mapVariableName,std::vector<unsigned> keyIndexes,std::string predicateName,bool createFalseAuxMap,bool aggrStruct){
    if(!declaredMaps.count(mapVariableName)){
        int BITSETSIZE=keyIndexes.size()*CHAR_BIT*sizeof(int);
        *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapVariableName << "({";
        for (unsigned k = 0; k < keyIndexes.size(); k++) {
            if (k > 0) {
                *out << ",";
            }
            *out << keyIndexes[k];
        }
        *out << "});\n";

        //TODO remove duplication
        *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapVariableName << "({";
        for (unsigned k = 0; k < keyIndexes.size(); k++) {
            if (k > 0) {
                *out << ",";
            }
            *out << keyIndexes[k];
        }
        *out << "});\n";
        if(aggrStruct){
            *out << ind << "AuxMap<"<<BITSETSIZE<<"> np" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";

            *out << ind << "AuxMap<"<<BITSETSIZE<<"> nu" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";
        }
        // if(createFalseAuxMap){
            *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapVariableName << "({";
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
void CompilationManager::storePossibleSum(const std::string& auxValPred,std::string tupleName,std::vector<int> sharedVarIndex, int sumVar){
    *out << ind++ << "{\n";
        *out << ind << "std::vector<int> key({";
        for(unsigned i=0; i<sharedVarIndex.size(); i++){
            if(i>0)
                *out << ",";
            *out << tupleName << "->at(" << sharedVarIndex[i] << ")";
        }
        *out << "});\n";
        *out << ind << "std::vector<int>* possibleSums = &possibleValues"<<auxValPred<<"[key];\n";
        *out << ind << "std::unordered_set<int>* possibleSumsSet = &possibleValuesSet"<<auxValPred<<"[key];\n";
        *out << ind++ << "if(possibleSums->empty()){\n";
            *out << ind << "possibleSums->push_back(0);\n";
            *out << ind << "Tuple* aux_val = factory.addNewInternalTuple({0},_"<<auxValPred<<");\n";
            *out << ind << "const auto& insertResult = aux_val->setStatus(True);\n";
            *out << ind++ << "if(insertResult.second){\n";
                *out << ind << "factory.removeFromCollisionsList(aux_val->getId());\n";
                *out << ind << "insertTrue(insertResult);\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        *out << ind << "unsigned size = possibleSums->size();\n";
        *out << ind++ << "for(unsigned i = 0; i<size; i++){\n";
            *out << ind++ << "if(possibleSumsSet->count(possibleSums->at(i)+"<<tupleName<<"->at("<<sumVar<<"))==0){\n";
                *out << ind << "possibleSumsSet->insert(possibleSums->at(i)+"<<tupleName<<"->at("<<sumVar<<"));\n";
                *out << ind << "possibleSums->push_back(possibleSums->at(i)+"<<tupleName<<"->at("<<sumVar<<"));\n";
                *out << ind << "Tuple* aux_val = factory.addNewInternalTuple({possibleSums->back()},_"<<auxValPred<<");\n";
                *out << ind << "const auto& insertResult = aux_val->setStatus(True);\n";
                *out << ind++ << "if(insertResult.second){\n";
                    *out << ind << "factory.removeFromCollisionsList(aux_val->getId());\n";
                    *out << ind << "insertTrue(insertResult);\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
    *out << --ind << "}\n";
}
void CompilationManager::generateStratifiedCompilableProgram(aspc::Program & program, AspCore2ProgramBuilder* builder) {

    bool programHasConstraint = program.hasConstraint();

    *out << ind << "#include \"Executor.h\"\n\n";
    *out << ind << "#include \"utils/ConstantsManager.h\"\n\n";
    *out << ind << "#include \"DLV2libs/input/InputDirector.h\"\n\n";
    *out << ind << "#include \"parsing/AspCore2InstanceBuilder.h\"\n\n";
    // *out << ind << "#include \"datastructures/PredicateSet.h\"\n\n";
    *out << ind << "#include \"datastructures/ReasonTable.h\"\n\n";
    *out << ind << "#include \"datastructures/PostponedReasons.h\"\n\n";
    *out << ind << "#include \"../util/WaspTrace.h\"\n\n";
    *out << ind << "#include \"../util/WaspOptions.h\"\n\n";
    *out << ind << "#include \"datastructures/DynamicTrie.h\"\n\n";
    *out << ind << "#include \"datastructures/VariablesMapping.h\"\n\n";
    *out << ind << "#include \"datastructures/VarsIndex.h\"\n\n";
    *out << ind << "#include \"datastructures/TupleFactory.h\"\n\n";
    *out << ind << "#include <chrono>\n\n";
    *out << ind << "#include \"datastructures/AuxiliaryMapSmart.h\"\n\n";
    *out << ind << "#include \"datastructures/VectorAsSet.h\"\n\n";
    *out << ind << "#include \"../tsl/hopscotch_map.h\"\n\n";
    *out << ind << "#include<ctime>\n\n";
    *out << ind << "#include<ctime>\n\n";
    *out << ind << "#include<map>\n\n";
    *out << ind << "#include<memory>\n\n";
    #ifdef TRACE_ON
    // *out << ind << "extern wasp::TraceLevels wasp::Options::traceLevels;\n\n";
    #endif
    *out << ind << "namespace aspc {\n";
    *out << ind++ << "extern \"C\" Executor* create_object() {\n";

    *out << ind << "return new Executor;\n";
    *out << --ind << "}\n";

    *out << ind++ << "extern \"C\" void destroy_object( Executor* object ) {\n";
    *out << ind << "delete object;\n";
    *out << --ind << "}\n";



    *out << ind++ << "Executor::Executor() {\n";
        #ifdef TRACE_ON
        // *out << ind << "setTraceLevel(eagerprop,10);\n";
        #endif
        *out << ind << "totalReasonSize=0;\n";
        *out << ind << "reasonCount=0;\n";
    *out << --ind << "}\n";

    //typedefs
    *out << ind << "typedef TupleLight Tuple;\n";
    // if (programHasConstraint) {
    //     *out << ind << "typedef TupleWithReasons Tuple;\n";
    // } else {
    //     *out << ind << "typedef TupleWithoutReasons Tuple;\n";
    // }
    // *out << ind << "typedef AuxiliaryMap<Tuple> AuxMap;\n";
    *out << ind << "template<size_t S>\n";
    *out << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

    *out << ind << "typedef std::vector<const Tuple* > Tuples;\n";
    // *out << ind << "using PredicateWSet = SmartPredicateSet;\n\n";

    if (mode == LAZY_MODE) {
        *out << ind << "std::unordered_map<std::string, PredicateWSet*> predicateWSetMap;\n";
        *out << ind << "std::unordered_map<std::string, PredicateWSet*> predicateFSetMap;\n";
    }
    *out << ind << "std::vector<std::string> Executor::predicateIds;\n";
    if (mode == EAGER_MODE) {

        for(std::string pred : builder->getInternalPredicates()){
            internalPredicates.insert(pred);
        }
        //store first occurence index of the first aggregate var
        for(const aspc::Rule& r : program.getRules()){
            if(!r.isConstraint()){
                if (r.containsAggregate() && r.getArithmeticRelationsWithAggregate()[0].getAggregate().isSum()){
                    const aspc::Literal* aggrSetLiteral = &(r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0]);
                    std::string var = r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateVariables()[0];
                    int index = -1;
                    for(unsigned i=0;i<aggrSetLiteral->getAriety();i++){
                        if(aggrSetLiteral->isVariableTermAt(i) && aggrSetLiteral->getTermAt(i) == var){
                            index = i;
                            break;
                        }
                    }
                    if(index!=-1){
                        predicateToOrderdedAux[aggrSetLiteral->getPredicateName()]=index;
                    }
                }
            }
        }

    }

    //contiene predicati con la rispettiva arità
    // const set< pair<std::string, unsigned> >& predicates = program.getPredicates();
    const set< pair<std::string, unsigned> >& predicates = program.getPredicates();

    for (const pair<std::string, unsigned>& predicate : predicates) {
        //*out << ind << "const std::string & "<< predicate.first << " = ConstantsManager::getInstance().getPredicateName("<< predicate.first <<");\n";
        mapPredicateNames[predicate.first]=predicateNames.size();
        predicateNames.push_back(predicate.first);
        *out << ind << "const int _" << predicate.first << " = " << mapPredicateNames[predicate.first] << ";\n";

    }
    const std::set< pair<std::string, unsigned> >& aggregatePredicates = program.getAggregatePredicates();

    for(const std::pair<std::string, unsigned>& predicate : aggregatePredicates){

        if(!predicates.count(predicate)){
            mapPredicateNames[predicate.first]=predicateNames.size();
            predicateNames.push_back(predicate.first);
            *out << ind << "const int _" << predicate.first << " = " << mapPredicateNames[predicate.first] << ";\n";
        }
    }
    std::set< pair<std::string, unsigned> > predicatesNotCompletion;

    for(const aspc::Rule& r :builder->getRuleWithoutCompletion()){
        for(const aspc::Literal& l : r.getBodyLiterals()){
            if(predicatesNotCompletion.count({l.getPredicateName(),l.getAriety()})==0 && aggregatePredicates.count({l.getPredicateName(),l.getAriety()})==0 && predicates.count({l.getPredicateName(),l.getAriety()})==0){
                mapPredicateNames[l.getPredicateName()]=predicateNames.size();
                predicateNames.push_back(l.getPredicateName());
                *out << ind << "const int _" << l.getPredicateName() << " = " << mapPredicateNames[l.getPredicateName()] << ";\n";
                predicatesNotCompletion.insert({l.getPredicateName(),l.getAriety()});
            }
        }
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation:r.getArithmeticRelationsWithAggregate()){
            for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                if(predicatesNotCompletion.count({l.getPredicateName(),l.getAriety()})==0 && aggregatePredicates.count({l.getPredicateName(),l.getAriety()})==0 && predicates.count({l.getPredicateName(),l.getAriety()})==0){
                    mapPredicateNames[l.getPredicateName()]=predicateNames.size();
                    predicateNames.push_back(l.getPredicateName());
                    *out << ind << "const int _" << l.getPredicateName() << " = " << mapPredicateNames[l.getPredicateName()] << ";\n";
                    predicatesNotCompletion.insert({l.getPredicateName(),l.getAriety()});
                }
            }
        }
    }
    
    if(mode == EAGER_MODE){
        *out << ind << "std::unordered_map<int,std::vector<int>> levelToIntLiterals;\n";
        *out << ind << "std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;\n";
        *out << ind << "std::vector<int> visitedExplainLiteral;\n";
        *out << ind << "std::unordered_set<int> eagerFacts;\n";
        *out << ind << "int currentDecisionLevel=-1;\n";
        *out << ind << "bool undefinedLoaded=false;\n";
    }
    *out << ind << "std::unordered_map<int,int> actualSum;\n";
    *out << ind << "std::unordered_map<int,int> possibleSum;\n";
    *out << ind << "std::vector<int> falseLits;\n";
    // *out << ind << "tsl::hopscotch_map<int,int> actualSum;\n";
    // *out << ind << "tsl::hopscotch_map<int,int> possibleSum;\n";
    *out << ind << "bool unRoll=false;\n";
    *out << ind << "unsigned conflictCount=0;\n";

    *out << ind++ << "Executor::~Executor() {\n";
    *out << --ind << "}\n\n";

    *out << ind << "\n";
    *out << ind << "const std::vector<int> EMPTY_TUPLES_VEC;\n";
    *out << ind << "const IndexedSet EMPTY_TUPLES_SET;\n";
    *out << ind << "std::unordered_map<std::string, int > stringToUniqueStringPointer;\n";

    *out << ind << "TupleFactory factory;\n";
    *out << ind++ << "void printTuple(const Tuple* t){\n";
        *out << ind << "if(t->isFalse()) std::cout << \"not \";\n";
        *out << ind << "if(t->isUndef()) std::cout << \"undef \";\n";
        *out << ind << "std::cout << Executor::predicateIds[t->getPredicateName()] << \"(\";\n";
        *out << ind++ << "for(int i=0;i<t->size();i++){\n";
            *out << ind << "if(i>0) std::cout << \",\";\n";
            *out << ind << "std::cout << ConstantsManager::getInstance().unmapConstant(t->at(i));\n";
        *out << --ind << "}\n";
        *out << ind << "std::cout << \")\"<<std::endl;\n";
    *out << --ind << "}\n";
    *out << ind++ << "int parseTuple(const std::string & literalString,std::vector<int>& terms) {\n";
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

    if (mode == LAZY_MODE) {
        *out << ind << "std::unordered_map <std::string, std::vector <AuxMap*> > predicateToAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <std::string, std::vector <AuxMap*> > predicateToUndefAuxiliaryMaps;\n";
        *out << ind << "std::unordered_map <std::string, std::vector <AuxMap*> > predicateToFalseAuxiliaryMaps;\n";
    }

    if(mode == EAGER_MODE){

        for(const auto& pred : builder->getValuesPredicates()){
            // std::cout<<"declaring map for auxToVal "<<pair.first+"_"<<std::endl;
            declareAuxMap(pred+"_",{},pred,false,false);
        }
        for(const auto& pred : builder->getDomainPredicates()){
            // std::cout<<"declaring map for auxToVal "<<pair.first+"_"<<std::endl;
            declareAuxMap(pred+"_",{},pred,false,false);
        }
    }
    // std::cout << "Declaring structure"<<std::endl;
    for (aspc::Rule& r : program.getRules()) {
        // r.print();
        if(mode == EAGER_MODE){
            int lIndex=0;
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
                // headPreds.insert({r.getHead()[0].getPredicateName(),&r});
            }
            declareRuleEagerStructures(r);

            r.bodyReordering(starters);

            for(unsigned starter : starters){
                if(starter <= r.getBodySize()){
                    declareDataStructures(r,starter,aggregatePredicates);
                }
            }
        }
        else if (!r.isConstraint()) {
            if(mode == EAGER_MODE){

            }else{
            }

        }
        // else if (exitRule || r.isConstraint()) {
        //     if (mode == LAZY_MODE) {
        //         r.bodyReordering();
        //         unsigned starter = r.getStarters()[0];
        //         aspc::Literal* starterL = (aspc::Literal*) r.getFormulas()[starter];
        //         starterToExitRulesByComponent[headLevel][starterL->getPredicateName()].push_back(r.getRuleId());

        //     } else {

        //     }
        // }
    }
    // std::cout << "Ordering Formulas"<<std::endl;
    {
        aspc::EagerProgram* endProgram = &builder->getEndProgram();
        std::unordered_set<int> recursiveComponents;
        std::unordered_map<string,int> predicateToComponent;
        auto scc = endProgram->positiveSCC();
        for(int component = scc.size()-1; component>=0; component--){
            bool recursive = scc[component].size()>1;
            if(!recursive){
                for(int predId : endProgram->getPositiveDG().getAdjForNode(scc[component][0])){
                    if(predId == scc[component][0]){
                        recursive=true;
                        break;
                    }
                }
            }
            if(recursive) recursiveComponents.insert(component);
            for(int predId : scc[component]){
                predicateToComponent[endProgram->getPredicateName(predId)]=component;
            }
        }
        // for(int comp : recursiveComponents)std::cout<<comp<<std::endl;
        for(const aspc::Rule& r : builder->getRuleWithoutCompletion()){
            std::vector<int> starters({r.getFormulas().size()});
            auto it = predicateToComponent.find(r.getHead()[0].getPredicateName());
            if(it!=predicateToComponent.end()){
                if(recursiveComponents.count(it->second)!=0){
                    const auto& body = r.getFormulas();
                    for(int fIndex=0;fIndex<body.size();fIndex++){
                        if(body[fIndex]->isPositiveLiteral()){
                            const aspc::Literal* l=(const aspc::Literal*)body[fIndex];
                            auto itBody = predicateToComponent.find(l->getPredicateName());
                            if(itBody != predicateToComponent.end()){
                                if(itBody->second == it->second){
                                    starters.push_back(fIndex);
                                }
                            }
                        }
                    }
                }
            }
            // for(int starter:starters) std::cout << starter << " "; r.print();
            for(int starter:starters){
                std::vector<unsigned> orderedFormulas;
                r.orderBodyFormulasFromStarter(starter,orderedFormulas);
                std::unordered_set<std::string> boundVariables;
                if(starter != r.getFormulas().size()){
                    r.getFormulas()[starter]->addVariablesToSet(boundVariables);
                    // std::cout <<std::endl;r.getFormulas()[starter]->print();std::cout <<std::endl;
                }
                // else std::cout <<std::endl<< "No starter"<<std::endl;

                for(unsigned formulaIndex : orderedFormulas){
                    // r.getFormulas()[formulaIndex]->print();
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
                                        int BITSETSIZE=boundIndices.size()*CHAR_BIT*sizeof(int);
                                        *out << ind << "AuxMap<"<<BITSETSIZE<<"> "<< c << mapName << "({";
                                        for (unsigned k = 0; k < boundIndices.size(); k++) {
                                            if (k > 0) {
                                                *out << ",";
                                            }
                                            *out << boundIndices[k];
                                        }
                                        *out << "});\n";

                                    }
                                    predicateToAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                                    predicateToUndefAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                                    predicateToFalseAuxiliaryMaps[l->getPredicateName()].insert(mapName);
                                    declaredMaps.insert(mapName);
                                }
                                l->addVariablesToSet(boundVariables);

                            }
                            // else std::cout << "Literal bound"<<std::endl;

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
                                            int BITSETSIZE=boundIndices.size()*CHAR_BIT*sizeof(int);
                                            *out << ind << "AuxMap<"<<BITSETSIZE<<"> "<< c << mapName << "({";
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
        }
    }

    for (const std::string & predicate : modelGeneratorPredicatesInNegativeReasons) {
        //*out << ind << "const std::string & "<< predicate.first << " = ConstantsManager::getInstance().getPredicateName("<< predicate.first <<");\n";
        *out << ind << "PredicateWSet neg_w" << predicate << "(" << predicateArieties[predicate] << ");\n";
    }
    // std::cout << "Structure Declared"<<std::endl;

    *out << ind++ << "void Executor::handleConflict(int literal,std::vector<int>& propagatedLiterals){\n";

        *out << ind++ << "if(currentDecisionLevel <= 0){\n";
            #ifdef TRACE_CONFLICT
                *out << ind << "std::cout<<\"Conflict at level 0 propagating 1\"<<std::endl;\n";
            #endif
            *out << ind << "propagatedLiterals.push_back(1);\n";
            *out << ind << "return;\n";
        *out << --ind << "}\n\n";
        *out << ind << "explainLevel++;\n";
        *out << ind << "Tuple* l = literal>0 ? factory.getTupleFromInternalID(literal) : factory.getTupleFromInternalID(-literal);\n";
        #ifdef TRACE_CONFLICT
            *out << ind << "std::cout<<\"Handle Internal conflict: \";\n";
            *out << ind << "printTuple(l);\n";
            *out << ind << "std::cout<<\"Explain \"<<literal<<\" \";printTuple(l);std::cout<<std::endl;\n";

        #endif

        *out << ind << "explainExternalLiteral(literal,conflictReason,true);\n";

        #ifdef TRACE_CONFLICT
            *out << ind << "std::cout<<\"Explain \"<<-literal<<\" \";printTuple(l);std::cout<<std::endl;\n";
        #endif

        *out << ind << "explainExternalLiteral(-literal,conflictReason,true);\n";
        *out << ind << "propagatedLiterals.push_back(1);\n";
        *out << ind << "reasonForLiteral[literal].get()->clear();\n";
        *out << ind << "updateReasonSize(conflictReason.size());\n";
        #ifdef TRACE_CONFLICT
        *out << ind << "std::cout<<\"Conflict Reason\"<<std::endl;\n";
        *out << ind++ << "for(unsigned i =0; i<conflictReason.size();i++){\n";
            *out << ind << "Tuple* var = conflictReason[i] > 0 ? factory.getTupleFromWASPID(conflictReason[i]) : factory.getTupleFromWASPID(-conflictReason[i]);\n";
            *out << ind << "std::cout << conflictReason[i] << \" \"; printTuple(var) ;\n";
        *out << --ind << "}\n";
        *out << ind << "std::cout<<std::endl;\n";
        *out << ind << "std::cout<<\"Conflict Handled\"<<std::endl;\n";
        #endif
    *out << --ind << "}\n";

    *out << ind++ << "int Executor::explainExternalLiteral(int var,std::vector<int>& reas,bool propagatorCall){\n";
        #ifdef TRACE_PROPAGATOR
            *out << ind << "std::cout<<\"Explain \"<<var<<std::endl;\n";
        #endif
        *out << ind << "unsigned literalsCount = factory.size();\n";
        *out << ind++ << "if(!propagatorCall){\n";
            *out << ind << "int uVar = var>0 ? var : -var;\n";
            *out << ind << "Tuple* waspTuple = factory.getTupleFromWASPID(uVar);\n";
            *out << ind << "if(waspTuple==NULL) std::cout << \"WARNING: Unable to find tuple from wasp id in explainExternalLiteral\"<<std::endl;\n";
            *out << ind << "int internalVar = waspTuple->getId();\n";
            // *out << ind << "int internalVar = factory.getTupleFromWASPID(uVar)->getId();\n";
            *out << ind << "var = var>0 ? internalVar : -internalVar;\n";
            *out << ind << "explainLevel++;\n";
            *out << ind << "reas.reserve(getMeanReasonSize());\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Explain from wasp \";\n";
                *out << ind << "factory.getTupleFromWASPID(uVar)->print();\n";
            #endif
            #ifdef TRACE_REASON
                *out << ind << "std::cout<<\"Explain from wasp \";\n";
                *out << ind << "factory.getTupleFromWASPID(uVar)->print();\n";
            #endif

        *out << --ind << "}\n";
        // *out << ind << "std::list<int> stack;\n";
        *out << ind << "buildingReasonStack.push_back(var);\n";
        #ifdef TRACE_PROPAGATOR
        *out << ind << "Tuple* starter = var > 0 ? factory.getTupleFromInternalID(var) : factory.getTupleFromInternalID(-var); printTuple(starter);\n";
        #endif
        *out << ind << "auto end=reasonForLiteral.end();\n";
        *out << ind++ << "while(!buildingReasonStack.empty()){\n";
            *out << ind << "int lit = buildingReasonStack.back();\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "Tuple* starter = lit > 0 ? factory.getTupleFromInternalID(lit) : factory.getTupleFromInternalID(-lit);\n";
                *out << ind << "std::cout<<\"Navigating Literal \"<<lit<<\" \";\n";
                *out << ind << "printTuple(starter);\n";
            #endif
            *out << ind << "buildingReasonStack.pop_back();\n";
            *out << ind << "auto itReason = reasonForLiteral.find(lit);\n";
            *out << ind << "VectorAsSet<int>* currentReas = itReason != end ? itReason->second.get() : NULL;\n";
            *out << ind << "unsigned currentReasonSize= currentReas != NULL ? currentReas->size() : 0;\n";
            *out << ind++ << "for(unsigned i = 0; i<currentReasonSize; i++){\n";
                *out << ind << "int& reasonLiteral=currentReas->at(i);\n";
                *out << ind << "int& visitCount = reasonLiteral>=0 ? visitedExplainLiteral[reasonLiteral] : visitedExplainLiteral[literalsCount-reasonLiteral];\n";
                *out << ind++ << "if(visitCount != explainLevel){\n";
                    *out << ind << "visitCount=explainLevel;\n";
                    *out << ind << "Tuple* literal = reasonLiteral>0 ? factory.getTupleFromInternalID(reasonLiteral):factory.getTupleFromInternalID(-reasonLiteral);\n";
                    *out << ind << "if(literal==NULL) std::cout << \"WARNING: Unable to find tuple in reason \"<<reasonLiteral<<std::endl;\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"   New Reason Literal To Navigate \"<<reasonLiteral<<\" \";\n";
                        *out << ind << "printTuple(literal);\n";
                    #endif

                    // *out << ind << "visitedLiteral.insert(reasonLiteral);\n";
                    *out << ind++ << "if(literal->isInternalLiteral()){\n";
                        *out << ind << "buildingReasonStack.push_back(reasonLiteral);\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Internal lit\"<<std::endl;\n";
                        #endif
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind << "int signedLit = reasonLiteral>0 ? literal->getWaspID() : -literal->getWaspID();\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"External literal \"<<signedLit<<std::endl;\n";
                        #endif
                        *out << ind << "reas.push_back(signedLit);\n";
                    *out << --ind << "}\n";

                *out << --ind << "}\n";
            *out << --ind << "}\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"End Navigating Literal \"<<lit<<\" \";\n";
                *out << ind << "starter->print();\n";
            #endif
        *out << --ind << "}\n";
        #ifdef TRACE_PROPAGATOR
            *out << ind << "std::cout<<\"Reason for: \"<<var<<std::endl;\n";
            *out << ind++ << "for(unsigned i=0; i<reas.size(); i++){\n";
                *out << ind << "Tuple* t = reas[i]>0 ? factory.getTupleFromWASPID(reas[i]) : factory.getTupleFromWASPID(-reas[i]);\n";
                *out << ind << "std::cout<<reas[i]<<\" \";t->print();\n";
            *out << --ind << "}\n";
            *out << ind << "std::cout<<\"End explaining\"<<std::endl;\n";
            *out << ind++ << "if(!propagatorCall) std::cout<<reas.size()<<std::endl;\n";
        #endif
        *out << ind << "return 0;\n";
    *out << --ind << "}\n";
    *out << ind++ << "void Executor::explainAggrLiteral(int var,UnorderedSet<int>& reas){\n";
        *out << ind << "return;\n";
    *out << --ind << "}\n";

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


    // string tupleType = "WithoutReasons";
    // if (programHasConstraint) {
    //     tupleType = "WithReasons";
    // }

    unordered_map<std::string,std::pair<char,std::unordered_map<std::string,std::set<std::string>>>> auxInsertToPrefix={{"insertUndef",{'u',predicateToUndefAuxiliaryMaps}},{"insertTrue",{'p',predicateToUndefAuxiliaryMaps}},{"insertFalse",{'f',predicateToUndefAuxiliaryMaps}}};
    for(auto function_prefix: auxInsertToPrefix){
        *out << ind++ << "inline void "<<function_prefix.first<<"(const std::pair<const TupleLight *, bool>& insertResult){\n";
        unsigned predIndex=0;
            for(auto predicateToMaps : function_prefix.second.second){
                std::string printElse = predIndex>0 ? "else " : "";
                *out << ind++ << printElse << "if(insertResult.first->getPredicateName() == _"<<predicateToMaps.first<<"){\n";
                    for(auto mapName : predicateToMaps.second){
                        if(predicateToOrderdedAux.count(predicateToMaps.first)!=0){
                            *out << ind << function_prefix.second.first<<mapName<<".insert2Set(*insertResult.first);\n";
                        }else{
                            *out << ind << function_prefix.second.first<<mapName<<".insert2Vec(*insertResult.first);\n";
                        }
                    }
                *out << --ind << "}\n";
                predIndex++;
            }
        *out << --ind <<"}\n";
    }

    // ---------------------- onLiteralTrue(const aspc::Literal* l) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralTrue(const aspc::Literal* l) {\n";
    if (mode == LAZY_MODE) {
    }
    *out << --ind << "}\n";
    // ---------------------- end onLiteralTrue(const aspc::Literal* l) --------------------------------------//

    // ---------------------- onLiteralUndef(const aspc::Literal* l) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralUndef(const aspc::Literal* l) {\n";
    *out << --ind << "}\n";
    // ---------------------- end onLiteralTrue() --------------------------------------//
    // ---------------------- onLiteralTrue(int var) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralTrue(int var, const std::string& literalString) {\n";
        *out << ind << "std::vector<int> terms;\n";
        *out << ind << "int predicate = parseTuple(literalString,terms);\n";
        *out << ind << "Tuple* tuple = factory.addNewTuple(terms,predicate,var);\n";
        *out << ind << "TruthStatus truth = var>0 ? True : False;\n";
        *out << ind << "const auto& insertResult = tuple->setStatus(truth);\n";
        *out << ind++ << "if(insertResult.second){\n";
            *out << ind << "factory.removeFromCollisionsList(tuple->getId());\n";
            *out << ind++ << "if (var > 0) {\n";
                *out << ind << "insertTrue(insertResult);\n";
            *out << --ind << "}else{\n";
            ind++;
                *out << ind << "insertFalse(insertResult);\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
    *out << --ind << "}\n";
    *out << ind++ << "inline void Executor::onLiteralTrue(int var) {\n";
    if (mode == EAGER_MODE) {
        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "Tuple* tuple = factory.getTupleFromWASPID(uVar);\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";
        // *out << ind << "trace_msg(eagerprop, 2, \"Literal true received \" << minus << tuple->toString());\n";
        
        *out << ind << "if(var<0) falseLits.push_back(-tuple->getId());\n";
        *out << ind << "std::unordered_map<const std::string*,int>::iterator sum_it;\n";
        *out << ind << "TruthStatus truth = var>0 ? True : False;\n";
        *out << ind << "const auto& insertResult = tuple->setStatus(truth);\n";
        *out << ind++ << "if(insertResult.second){\n";

            *out << ind << "factory.removeFromCollisionsList(tuple->getId());\n";
            *out << ind++ << "if (var > 0) {\n";
                *out << ind << "insertTrue(insertResult);\n";
            *out << --ind << "}else{\n";
            ind++;
                *out << ind << "insertFalse(insertResult);\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        #if defined(TRACE_PROPAGATOR) || defined(TRACE_PROPAGATION) || defined(TRACE_CONFLICT)
        // *out << ind << "std::cout<<\"True \" << minus << tuple->toString()<<std::endl;\n";
        *out << ind << "std::cout<<\"True \";printTuple(tuple);\n";
        #endif
        for(int ruleId=0;ruleId < program.getRules().size(); ruleId++){
            const aspc::Rule* rule = &program.getRules()[ruleId];
            if(!rule->containsAggregate() || rule->isConstraint()) continue;
            const aspc::Atom* aggrId = &rule->getHead()[0];
            const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
            const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
            unsigned sumVar = 0;
            if(!aggregateRelation->getAggregate().isSum() || builder->isAggrSetPredicate(aggrSetLit->getPredicateName()))
                continue;

            //aggregate is sum
            if(!builder->isAggrSetPredicate(aggrSetLit->getPredicateName())){
                std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                    if(aggrSetLit->getTermAt(i)==var){
                        sumVar=i;
                        break;
                    }
                }
            }
            *out << ind++ << "if(tuple->getPredicateName() == _"<<aggrSetLit->getPredicateName()<<"){\n";
                if(aggrId->getAriety() == 0){
                    *out << ind << "int itAggrId = factory.find({},_"<<aggrId->getPredicateName()<<")->getId();\n";
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
                            *out << ind << "const std::vector<int>* aggrIds = &"<<sign<<mapName<<".getValuesVec({"<<terms<<"});\n";
                            *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                *out << ind << "int itAggrId = aggrIds->at(i);\n";
                                *out << ind++ << "if(var>0)\n";
                                    *out << ind-- << "actualSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                                *out << ind << "possibleSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }
                }
            *out << --ind << "}\n";
        }
#ifdef EAGER_DEBUG
        *out << ind << "std::cout<<\"on literal true \";\n";
        *out << ind << "std::cout<<var<<\"\\n\";\n";
        *out << ind << "tuple.print();\n";
        *out << ind << "std::cout<<\"\\n\";\n";
#endif
        //*out << ind << "trace_msg(eagerprop, 2, \"Literal True saved\");\n";

    #ifdef TRACE_PROP_GEN
        *out << ind << "std::cout<<\"Exit onLiteralTrue\"<<std::endl;\n";
    #endif
    }

    *out << --ind << "}\n";


    // ---------------------- onLiteralUndef(int var) --------------------------------------//
    *out << ind++ << "inline void Executor::onLiteralUndef(int var) {\n";
    if (mode == EAGER_MODE) {
        *out << ind << "unsigned uVar = var > 0 ? var : -var;\n";
        *out << ind << "Tuple* tuple = factory.getTupleFromWASPID(uVar);\n";
        *out << ind << "int internalVar = var > 0 ? tuple->getId() : -tuple->getId();\n";
        *out << ind << "auto reas = reasonForLiteral.find(internalVar);\n";
        *out << ind << "if(reas!=reasonForLiteral.end())reas->second.get()->clear();\n";
        *out << ind << "std::string minus = var < 0 ? \"-\" : \"\";\n";

        
#ifdef EAGER_DEBUG
        *out << ind << "std::cout<<\"on literal undef \";\n";
        *out << ind << "std::cout<<var<<\"\\n\";\n";
        *out << ind << "tuple.print();\n";
        *out << ind << "std::cout<<\"\\n\";\n";
#endif
        //*out << ind << "trace_msg(eagerprop, 2, \"Literal undef received \" << minus << tuple->toString());\n";

        *out << ind << "const auto& insertResult = tuple->setStatus(Undef);\n";
        *out << ind++ << "if (insertResult.second) {\n";
            *out << ind << "factory.removeFromCollisionsList(tuple->getId());\n";
            *out << ind << "insertUndef(insertResult);\n";
        *out << --ind << "}\n";
        #if defined(TRACE_PROPAGATOR) || defined(TRACE_PROPAGATION) || defined(TRACE_CONFLICT)
        // *out << ind++ << "if(tuple == NULL)\n";
        //     *out << ind-- << "std::cout<<\"Unable to find tuple \"<<var<<std::endl;\n";
        // *out << ind++ << "else\n";
        //     *out << ind-- << "std::cout<<\"Undef \" <<var << \" \" << minus << tuple->toString()<<std::endl;\n";
        
        *out << ind-- << "std::cout<<\"Undef \"; printTuple(tuple);\n";
        #endif

        *out << ind++ << "if(currentDecisionLevel > 0){\n";
        for(int ruleId=0; ruleId < program.getRules().size();ruleId++){
            const aspc::Rule* rule = &program.getRules()[ruleId];
            if(rule->isConstraint() || !rule->containsAggregate()) continue;

            const aspc::Atom* aggrId = &rule->getHead()[0];
            const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
            const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
            unsigned sumVar = 0;
            if(!aggregateRelation->getAggregate().isSum() || builder->isAggrSetPredicate(aggrSetLit->getPredicateName()))
                continue;
            if(!builder->isAggrSetPredicate(aggrSetLit->getPredicateName())){
                std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                    if(aggrSetLit->getTermAt(i)==var){
                        sumVar=i;
                        break;
                    }
                }
            }
            *out << ind++ << "if(tuple->getPredicateName() == _"<<aggrSetLit->getPredicateName()<<"){\n";
                if(aggrId->getAriety() == 0){
                    *out << ind << "int itAggrId = factory.find({},_"<<aggrId->getPredicateName()<<")->getId();\n";
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
                            *out << ind << "const std::vector<int>* aggrIds = &"<<sign<<mapName<<".getValuesVec({"<<terms<<"});\n";
                            *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                *out << ind << "int itAggrId = aggrIds->at(i);\n";
                                *out << ind++ << "if(var>0)\n";
                                    *out << ind-- << "actualSum[itAggrId]-=tuple->at("<<sumVar<<");\n";
                                *out << ind << "possibleSum[itAggrId]+=tuple->at("<<sumVar<<");\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }
                }
            *out << --ind << "}\n";

        }
        *out << --ind << "}\n";
        #ifdef TRACE_PROPAGATOR
            // *out << ind << "trace_msg(eagerprop, 2, \"Exit undef\");\n";
            *out << ind<< "std::cout<<\"Exit undef\"<<std::endl;\n";
            // *out << ind << "std::cout<<\"ActualSum aggr_id0: \"<<actualSum[factory.addNewInternalTuple({},&_aggr_id0)->getId()]<<std::endl;\n";
            // *out << ind << "std::cout<<\"ActualSum aggr_id1: \"<<actualSum[factory.addNewInternalTuple({},&_aggr_id1)->getId()]<<std::endl;\n";
            // *out << ind << "std::cout<<\"PossibleSum aggr_id0: \"<<possibleSum[factory.addNewInternalTuple({},&_aggr_id0)->getId()]<<std::endl;\n";
            // *out << ind << "std::cout<<\"PossibleSum aggr_id1: \"<<possibleSum[factory.addNewInternalTuple({},&_aggr_id1)->getId()]<<std::endl;\n";
        #endif
    }
    *out << --ind << "}\n";


    // ---------------------- end onLiteralTrue(int var) --------------------------------------//
    // ---------------------- addedVarName(int var, const std::string & atom) --------------------------------------//
    // std::cout<<"Printing aux generation"<<std::endl;
    *out << ind++ << "bool compTuple(const int& l1,const int& l2){\n";
        *out << ind << "Tuple* first = factory.getTupleFromInternalID(l1);\n";
        *out << ind << "unsigned firstAggrVarIndex = factory.getIndexForAggrSet(first->getPredicateName());\n";
        *out << ind << "int w = first->at(firstAggrVarIndex)-factory.getTupleFromInternalID(l2)->at(firstAggrVarIndex);\n";
        *out << ind << "return w==0 ? l1 > l2 : w > 0;\n";
    *out << --ind << "}\n";
    // std::cout << "Building Unfounded Procedures"<<std::endl;

    {

        *out << ind << "std::unordered_map<const std::string*,std::unordered_set<int>*> predsToUnfoundedSet;\n";
        *out << ind << "std::vector<int> foundnessFactory;\n";

        aspc::EagerProgram* program = &builder->getRewrittenProgram();
        aspc::EagerProgram* compilingProgram = &builder->getCompilingProgram();
        auto ruleToSubProgram = builder->getSubPrograms();

        GraphWithTarjanAlgorithm graph = program->getPositiveDG();
        std::vector<std::vector<int>> scc = graph.SCC();

        auto sumPredicate = builder->getSumPredicates();
        std::vector<int> recursiveComponent;
        for(int componentId = scc.size()-1;componentId>=0;componentId--){
            bool recursive = scc[componentId].size()>1;
            if(!recursive){
                for(int adj : graph.getAdjForNode(scc[componentId][0])){
                    if(adj==scc[componentId][0]){
                        recursive=true;
                        break;
                    }
                }
            }
            if(recursive){
                recursiveComponent.push_back(componentId);
                // *out << ind << "std::unordered_map<int,std::unordered_set<int>> supportedAux"<<componentId<<";\n";
                // *out << ind << "std::unordered_map<int,std::unordered_set<int>> supportedLiterals"<<componentId<<";\n";
                *out << ind << "std::vector<std::vector<int>> supportedAux"<<componentId<<";\n";
                *out << ind << "std::vector<std::vector<int>> supportedLiterals"<<componentId<<";\n";
                *out << ind << "std::unordered_map<int,int> sourcePointers"<<componentId<<";\n";
                // *out << ind << "std::unordered_set<int> unfoundedSetForComponent"<<componentId<<";\n";
                *out << ind << "std::vector<int> unfoundedSetForComponent"<<componentId<<";\n";

            }

            // std::cout << "component "<<componentId<<std::endl;
            // for(int predId: scc[componentId]){
            //     std::cout << program->getPredicateName(predId)<<" ";
            // }
            // std::cout<<std::endl;

        }


        for(int componentId : recursiveComponent){
            std::unordered_set<std::string> componentPred;
            for(int predId : scc[componentId]){
                std::string predName = program->getPredicateName(predId);
                for(std::string sup : builder->getSupportPredicateForHead(predName)){
                    componentPred.insert(sup);
                }
                componentPred.insert(predName);
            }
            for(unsigned ruleId = 0; ruleId < program->getRules().size(); ruleId++){
                const aspc::Rule* r = &program->getRule(ruleId);
                if(!r->isConstraint()){
                    const aspc::Atom* head = &r->getHead()[0];
                    if(componentPred.count(head->getPredicateName())!=0){
                        std::string auxFound="";
                        std::unordered_set<std::string> internalLitsFound;
                        for(int subRuleId:ruleToSubProgram[ruleId]){
                            const aspc::Rule* subRule = &compilingProgram->getRule(subRuleId);
                            if(subRule->isConstraint()){
                                for(const aspc::Literal& l : subRule->getBodyLiterals()){
                                    if(builder->isAuxPredicate(l.getPredicateName()))
                                        auxFound=l.getPredicateName();
                                    else if (l.isPositiveLiteral() && componentPred.count(l.getPredicateName()))
                                        internalLitsFound.insert(l.getPredicateName());
                                }
                            }
                        }
                        if(!internalLitsFound.empty() && auxFound!=""){
                            auxForRecursiveComponent[auxFound]={componentId,internalLitsFound};
                        }
                    }
                }
            }
            // *out << ind << "std::unordered_set<int> foundedSetForComponent"<<componentId<<";\n";

            *out << ind++ << "void propFoundnessForComponent"<<componentId<<"(int foundedLiteral){\n";
                *out << ind << "std::vector<int> foundedStack({foundedLiteral});\n";
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"   New Founded Literal to Propagate \"<<factory.getTupleFromInternalID(foundedLiteral)->toString()<<std::endl;\n";
                #endif
                *out << ind++ << "while(!foundedStack.empty()){\n";
                *out << ind << "Tuple* starter = factory.getTupleFromInternalID(foundedStack.back());\n";
                *out << ind << "foundedStack.pop_back();\n";
                // *out << ind << "founded.insert(starter->getId());\n";
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"   Propagating Foundness of \"<<starter->toString()<<std::endl;\n";
                #endif
                for(int predId : scc[componentId]){
                    std::string predName = program->getPredicateName(predId);
                    std::cout << predName << std::endl;

                    for(unsigned ruleId = 0; ruleId < program->getRules().size(); ruleId++){
                        const aspc::Rule* r = &program->getRule(ruleId);
                        if(!r->isConstraint() && r->getHead()[0].getPredicateName()==predName){
                            bool isExitRule = true;
                            for(const aspc::Literal& l : r->getBodyLiterals()){
                                if(l.isPositiveLiteral() && componentPred.count(l.getPredicateName())!=0){
                                    isExitRule=false;
                                }else{
                                }
                            }
                            if(isExitRule) continue;
                            for(int rId : ruleToSubProgram[ruleId]){
                                aspc::Rule subRule(compilingProgram->getRule(rId));
                                if(!r->isConstraint()){
                                    const aspc::Atom* head=NULL;
                                    const aspc::Literal* body=NULL;
                                    std::vector<unsigned> starters;

                                    if(!subRule.isConstraint()){
                                        head=&subRule.getHead()[0];
                                        body=&subRule.getBodyLiterals()[0];
                                    }else{
                                        bool supportsAux=false;
                                        unsigned litIndex=0;
                                        for(const aspc::Formula* f : subRule.getFormulas()){
                                            if(f->isLiteral()){
                                                const aspc::Literal* l = (const aspc::Literal*)f;
                                                if(builder->isAuxPredicate(l->getPredicateName())){
                                                    supportsAux=true;
                                                    head = &l->getAtom();
                                                }
                                                if(l->isPositiveLiteral() /*&& componentPred.count(l->getPredicateName())!=0*/){
                                                    starters.push_back(litIndex);
                                                }
                                            }
                                            litIndex++;
                                        }
                                        if(!supportsAux){
                                            if(subRule.getBodyLiterals().size() != 2 || subRule.getBodyLiterals()[0].isNegated() || ! subRule.getBodyLiterals()[1].isNegated()){
                                                subRule.print();
                                                std::cout << "Error:    Unexpexted constraint format. Expected constraint :-l1,not l2"<<std::endl;
                                                std::exit(180);
                                            }else{
                                                head=&subRule.getBodyLiterals()[1].getAtom();
                                                body=&subRule.getBodyLiterals()[0];
                                            }
                                        }else{
                                            subRule.bodyReordering(starters);
                                        }
                                    }
                                    if(head != NULL && body!=NULL){
                                        *out << ind++ << "if(starter->getPredicateName() == _"<<body->getPredicateName()<<"){\n";
                                        std::unordered_set<std::string> boundTerms;
                                        unsigned closinPars =1;
                                        for(unsigned k = 0; k < body->getAriety(); k++){
                                            std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                            if(body->isVariableTermAt(k) && boundTerms.count(body->getTermAt(k))==0){
                                                *out << ind << "int " << term << "=starter->at("<<k<<");\n";
                                                boundTerms.insert(term);
                                            }else{
                                                *out << ind++ << "if(" << term << " == starter->at("<<k<<")){\n";
                                                closinPars++;
                                            }
                                        }
                                        std::string terms="";
                                        for(unsigned k = 0; k < head->getAriety(); k++){
                                            std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                            if(terms!="")
                                                terms+=",";
                                            terms+=term;
                                        }
                                        *out << ind << "Tuple* head = factory.find({"<<terms<<"},_"<<head->getPredicateName()<<");\n";

                                        *out << ind++ << "if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){\n";
                                        closinPars++;
                                            #ifdef TRACE_PROPAGATOR
                                                *out << ind << "std::cout<<\"       New Founded Literal to Propagate \"<<head->toString()<<std::endl;\n";
                                            #endif

                                            *out << ind << "supportedLiterals"<<componentId<<"[starter->getId()].push_back(head->getId());\n";
                                            *out << ind << "sourcePointers"<<componentId<<"[head->getId()] = starter->getId();\n";
                                            *out << ind << "foundedStack.push_back(head->getId());\n";
                                            *out << ind << "foundnessFactory[head->getId()]=1;\n";

                                        while (closinPars>0){
                                            *out << --ind << "}\n";
                                            closinPars--;
                                        }
                                    }else{
                                        //constraint with aux
                                        // subRule.print();
                                        for(unsigned starter : starters){
                                            std::vector<unsigned> formulasIndexes;
                                            const auto & orderedBody = subRule.getOrderedBodyByStarter(starter);
                                            const aspc::Literal* startinLit = (const aspc::Literal*)orderedBody[0];
                                            *out << ind++ << "if(starter->getPredicateName() == _"<<startinLit->getPredicateName()<<"){\n";
                                            std::unordered_set<std::string> boundTerms;
                                            unsigned closinPars =1;
                                            for(unsigned k = 0; k < startinLit->getAriety(); k++){
                                                std::string term = startinLit->isVariableTermAt(k) || isInteger(startinLit->getTermAt(k)) ? startinLit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+startinLit->getTermAt(k)+"\")";
                                                if(startinLit->isVariableTermAt(k) && boundTerms.count(startinLit->getTermAt(k))==0){
                                                    *out << ind << "int " << term << "=starter->at("<<k<<");\n";
                                                    boundTerms.insert(term);
                                                }else{
                                                    *out << ind++ << "if(" << term << " == starter->at("<<k<<")){\n";
                                                    closinPars++;
                                                }
                                            }
                                            for(unsigned fIndex = 1; fIndex<orderedBody.size();fIndex++){
                                                if(orderedBody[fIndex]->isBoundedValueAssignment(boundTerms)){
                                                    const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*)orderedBody[fIndex];
                                                    std::string var = ineq->getAssignedVariable(boundTerms);
                                                    *out << ind << "int "<<ineq->getAssignmentStringRep(boundTerms)<<";\n";
                                                    boundTerms.insert(var);
                                                }else if(orderedBody[fIndex]->isBoundedRelation(boundTerms)){
                                                    const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*)orderedBody[fIndex];
                                                    *out << ind++ << "if("<<ineq->getStringRep()<<"){\n";
                                                    closinPars++;
                                                }else if(orderedBody[fIndex]->isLiteral()){
                                                    const aspc::Literal* lit = (const aspc::Literal*) orderedBody[fIndex];
                                                    if(lit->getPredicateName() == head->getPredicateName()) continue;
                                                    formulasIndexes.push_back(fIndex);
                                                    if(lit->isBoundedLiteral(boundTerms)){
                                                        std::string terms="";
                                                        for(unsigned k = 0; k < lit->getAriety(); k++){
                                                            std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                                            if(terms!="")
                                                                terms+=",";
                                                            terms+=term;
                                                        }
                                                        *out << ind << "Tuple* tuple"<<fIndex<<" = factory.find({"<<terms<<"},_"<<lit->getPredicateName()<<");\n";
                                                        if(lit->isPositiveLiteral()){
                                                            *out << ind++ << "if(tuple"<<fIndex<<"!=NULL && !tuple"<<fIndex<<"->isFalse()){\n";
                                                            closinPars++;
                                                        }else{
                                                            *out << ind++ << "if(tuple"<<fIndex<<"==NULL || !tuple"<<fIndex<<"->isTrue()){\n";
                                                            closinPars++;
                                                        }
                                                    }else{
                                                        std::string terms="";
                                                        std::vector<unsigned> boundIndices;
                                                        for(unsigned k = 0; k < lit->getAriety(); k++){
                                                            std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                                            if(!lit->isVariableTermAt(k) || boundTerms.count(lit->getTermAt(k))!=0){
                                                                if(terms!="")
                                                                    terms+=",";
                                                                terms+=term;
                                                                boundIndices.push_back(k);
                                                            }
                                                        }
                                                        *out << ind << "const std::vector<int>* tuples = &p"<<lit->getPredicateName()<<"_";
                                                        for(unsigned k : boundIndices){
                                                            *out << k << "_";
                                                        }
                                                        *out << ".getValuesVec({"<<terms<<"});\n";
                                                        *out << ind << "const std::vector<int>* tuplesU = &u"<<lit->getPredicateName()<<"_";
                                                        for(unsigned k : boundIndices){
                                                            *out << k << "_";
                                                        }
                                                        *out << ".getValuesVec({"<<terms<<"});\n";
                                                        *out << ind++ << "for(unsigned i=0; i<tuples->size()+tuplesU->size();i++){\n";
                                                        closinPars++;
                                                            *out << ind << "Tuple* tuple"<<fIndex<<" = NULL;\n";
                                                            *out << ind << "if(i<tuples->size()) tuple"<<fIndex<<" = factory.getTupleFromInternalID(tuples->at(i));\n";
                                                            *out << ind << "else tuple"<<fIndex<<" = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
                                                            std::unordered_set<std::string> previousBound(boundTerms);
                                                            for(unsigned k = 0; k < lit->getAriety(); k++){
                                                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                                                if(lit->isVariableTermAt(k) && boundTerms.count(lit->getTermAt(k))==0){
                                                                    *out << ind << "int " << term << "=tuple"<<fIndex<<"->at("<<k<<");\n";
                                                                    boundTerms.insert(term);
                                                                }else{
                                                                    if(previousBound.count(term)==0){
                                                                        *out << ind++ << "if(" << term << " == tuple"<<fIndex<<"->at("<<k<<")){\n";
                                                                        closinPars++;
                                                                    }
                                                                }
                                                            }

                                                    }
                                                    if(componentPred.count(lit->getPredicateName())!=0 && lit->isPositiveLiteral()){
                                                        *out << ind++ << "if(foundnessFactory[tuple"<<fIndex<<"->getId()]>=0){\n";
                                                        closinPars++;
                                                    }
                                                }
                                            }
                                            std::string terms="";
                                            for(unsigned k = 0; k < head->getAriety(); k++){
                                                std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                                if(terms!="")
                                                    terms+=",";
                                                terms+=term;
                                            }
                                            *out << ind << "Tuple* head = factory.find({"<<terms<<"},_"<<head->getPredicateName()<<");\n";

                                            *out << ind++ << "if(head!=NULL && !head->isFalse() && foundnessFactory[head->getId()]<0){\n";
                                            closinPars++;
                                                #ifdef TRACE_PROPAGATOR
                                                    *out << ind << "std::cout<<\"       New Founded Aux to Propagate \"<<head->toString()<<std::endl;\n";
                                                #endif
                                                *out << ind << "foundedStack.push_back(head->getId());\n";
                                                *out << ind << "foundnessFactory[head->getId()]=1;\n";

                                                // for(unsigned fIndex: formulasIndexes){
                                                //     const aspc::Literal* lit = (const aspc::Literal*) orderedBody[fIndex];
                                                //     if(componentPred.count(lit->getPredicateName())!=0){
                                                //         *out << ind++ << "if(tuple"<<fIndex<<"!=NULL){\n";
                                                //             *out << ind << "supportedAux"<<componentId<<"[tuple"<<fIndex<<"->getId()].push_back(head->getId());\n";
                                                //         *out << --ind << "}\n";
                                                //     }
                                                // }
                                                // if(componentPred.count(startinLit->getPredicateName())!=0){
                                                //     *out << ind << "supportedAux"<<componentId<<"[starter->getId()].push_back(head->getId());\n";
                                                // }


                                            while (closinPars>0){
                                                *out << --ind << "}\n";
                                                closinPars--;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                *out << --ind << "}//close while \n";
            *out << --ind << "}//close function\n";

            *out << ind++ << "void unfoundedPropagatorForComponent"<<componentId<<"(std::vector<int>& literalToPropagate,Executor* executor){\n";
                // *out << ind << "std::unordered_set<int> founded;\n";
                
                *out << ind << "currentDecisionLevel=executor->getCurrentDecisionLevel();\n";
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"UnfoundedPropagatorForComponent"<<componentId<<"\"<<std::endl;\n";
                    *out << ind << "std::cout<<\"   Unfounded Set\"<<std::endl;\n";
                    *out << ind << "for(int id : unfoundedSetForComponent"<<componentId<<"){std::cout<<\"        \";factory.getTupleFromInternalID(id)->print();}\n";
                    *out << ind << "std::cout<<\"   Computing Source Pointers\"<<std::endl;\n";

                #endif
                // *out << ind << "auto t1_e = std::chrono::high_resolution_clock::now();\n";
                *out << ind << "int unfoundedCount=0;\n";
                *out << ind++ << "for(int id : unfoundedSetForComponent"<<componentId<<"){\n";
                    *out << ind << "Tuple* starter = factory.getTupleFromInternalID(id);\n";

                    #ifdef TRACE_PROPAGATOR
                    *out << ind << "if(foundnessFactory[id]>=0) std::cout<<\"      Literal already founded \"<<starter->toString()<<std::endl;\n";
                    #endif

                    *out << ind << "if(starter->isFalse() || foundnessFactory[id]>=0) continue;\n";
                    *out << ind++ << "if(eagerFacts.count(id)!=0){\n";
                        *out << ind << "foundnessFactory[starter->getId()]=1;\n";
                        *out << ind << "propFoundnessForComponent"<<componentId<<"(id);\n";
                        *out << ind << "continue;\n";
                    *out << --ind << "}\n";
                    #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"      Searching SP for \"<<starter->toString()<<std::endl;\n";
                    #endif
                    *out << ind << "bool spFound=false;\n";
                    auto programRules = program->getRules();
                    for(int predId : scc[componentId]){
                        std::string predName = program->getPredicateName(predId);
                        for(unsigned ruleId = 0; ruleId < program->getRules().size(); ruleId++){
                            const aspc::Rule* r = &programRules[ruleId];
                            if(!r->isConstraint() && r->getHead()[0].getPredicateName()==predName){
                                bool isExitRule = true;
                                for(const aspc::Literal& l : r->getBodyLiterals()){
                                    if(componentPred.count(l.getPredicateName())!=0)
                                        isExitRule=false;
                                }
                                // if(!isExitRule) continue;
                                for(int rId : ruleToSubProgram[ruleId]){
                                    aspc::Rule subRule(compilingProgram->getRule(rId));
                                    const aspc::Atom* head=NULL;
                                    const aspc::Literal* body=NULL;
                                    if(!subRule.isConstraint()){
                                        head=&subRule.getHead()[0];
                                        body=&subRule.getBodyLiterals()[0];
                                    }else{
                                        bool supportsAux=false;
                                        for(const aspc::Literal& l : subRule.getBodyLiterals()){
                                            if(builder->isAuxPredicate(l.getPredicateName())){
                                                supportsAux=true;
                                                break;
                                            }
                                        }
                                        if(!supportsAux){
                                            if(subRule.getBodyLiterals().size() != 2 || subRule.getBodyLiterals()[0].isNegated() || ! subRule.getBodyLiterals()[1].isNegated()){
                                                subRule.print();
                                                std::cout << "Error:    Unexpexted constraint format. Expected constraint :-l1,not l2"<<std::endl;
                                                std::exit(180);
                                            }else{
                                                head=&subRule.getBodyLiterals()[1].getAtom();
                                                body=&subRule.getBodyLiterals()[0];
                                            }
                                        }
                                    }
                                    if(head != NULL && body!=NULL){
                                        if(isExitRule && head->getPredicateName()!=predName) continue;
                                        *out << ind++ << "if(!spFound && starter->getPredicateName() == _"<<head->getPredicateName()<<" && foundnessFactory[starter->getId()]<0){\n";
                                        std::unordered_set<std::string> boundTerms;
                                        unsigned closinPars =1;
                                        for(unsigned k = 0; k < head->getAriety(); k++){
                                            std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                            if(head->isVariableTermAt(k) && boundTerms.count(head->getTermAt(k))==0){
                                                *out << ind << "int " << term << "=starter->at("<<k<<");\n";
                                                boundTerms.insert(term);
                                            }else{
                                                *out << ind++ << "if(" << term << " == starter->at("<<k<<")){\n";
                                                closinPars++;
                                            }
                                        }
                                        if(body->isBoundedLiteral(boundTerms)){
                                            std::string terms="";
                                            for(unsigned k = 0; k < body->getAriety(); k++){
                                                std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                                if(terms!="")
                                                    terms+=",";
                                                terms+=term;
                                            }
                                            *out << ind << "Tuple* body = factory.find({"<<terms<<"},_"<<body->getPredicateName()<<");\n";
                                            // *out << ind << "if(body!=NULL && body->isFalse()) shared_reason.get()->insert(-body->getId());\n";
                                            *out << ind++ << "if(body!=NULL && !body->isFalse()){\n";
                                            closinPars++;

                                        }else{
                                            std::string terms="";
                                            std::vector<unsigned> boundIndices;
                                            for(unsigned k = 0; k < body->getAriety(); k++){
                                                std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                                if(!body->isVariableTermAt(k) || boundTerms.count(body->getTermAt(k))!=0){
                                                    if(terms!="")
                                                        terms+=",";
                                                    terms+=term;
                                                    boundIndices.push_back(k);
                                                }
                                            }
                                            // *out << ind << "const std::vector<int>* tuplesF = &f"<<body->getPredicateName()<<"_";
                                            // for(unsigned k : boundIndices){
                                            //     *out << k << "_";
                                            // }
                                            // *out << ".getValuesVec({"<<terms<<"});\n";
                                            // *out << ind++ << "for(unsigned i=0; i<tuplesF->size();i++)\n";
                                            //     *out << ind-- << "shared_reason.get()->insert(-tuplesF->at(i));\n";

                                            *out << ind << "const std::vector<int>* tuples = &p"<<body->getPredicateName()<<"_";
                                            for(unsigned k : boundIndices){
                                                *out << k << "_";
                                            }
                                            *out << ".getValuesVec({"<<terms<<"});\n";
                                            *out << ind << "const std::vector<int>* tuplesU = &u"<<body->getPredicateName()<<"_";
                                            for(unsigned k : boundIndices){
                                                *out << k << "_";
                                            }
                                            *out << ".getValuesVec({"<<terms<<"});\n";
                                            *out << ind++ << "for(unsigned i=0; !spFound && i<tuples->size()+tuplesU->size();i++){\n";
                                            closinPars++;
                                                *out << ind << "Tuple* body = NULL;\n";
                                                *out << ind << "if(i<tuples->size()) body = factory.getTupleFromInternalID(tuples->at(i));\n";
                                                *out << ind << "else body = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
                                            *out << ind++ << "if(body!=NULL){\n";
                                            closinPars++;

                                        }
                                        if(!isExitRule){
                                            *out << ind++ << "if(foundnessFactory[body->getId()]>=0){\n";
                                            closinPars++;
                                        }

                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"           SP found \"<<body->toString()<<std::endl;\n";
                                        #endif
                                        *out << ind << "sourcePointers"<<componentId<<"[starter->getId()]=body->getId();\n";
                                        *out << ind << "supportedLiterals"<<componentId<<"[body->getId()].push_back(starter->getId());\n";
                                        *out << ind << "foundnessFactory[starter->getId()]=1;\n";
                                        *out << ind << "propFoundnessForComponent"<<componentId<<"(starter->getId());\n";
                                        *out << ind << "spFound=true;\n";

                                        while (closinPars>0){
                                            *out << --ind << "}\n";
                                            closinPars--;
                                        }

                                    }
                                }
                            }
                        }
                    }
                    *out << ind++ << "if(!spFound) unfoundedSetForComponent"<<componentId<<"[unfoundedCount++]=id;\n";
                *out << --ind << "} //close unfounded for\n";
                *out << ind << "unfoundedSetForComponent"<<componentId<<".resize(unfoundedCount);\n";
                // *out << ind << "std::cout << \"Unfounded size: \"<<unfoundedSetForComponent"<<componentId<<".size()<<std::endl;\n";
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "if(unfoundedSetForComponent"<<componentId<<".empty()) std::cout << \"   No Unfounded\"<<std::endl;\n";
                    *out << ind++ << "else{\n";
                        *out << ind << "std::cout<<\"   Unfounded Literals\"<<std::endl;\n";
                        *out << ind++ << "for(int lit : unfoundedSetForComponent"<<componentId<<"){\n";
                            *out << ind << "Tuple* starter = factory.getTupleFromInternalID(lit);\n";
                            *out << ind << "if(foundnessFactory[lit]<0)std::cout << \"     \"<<starter->toString()<<std::endl;\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";

                #endif

                *out << ind++ << "if(!unfoundedSetForComponent"<<componentId<<".empty()){\n";
                    *out << ind << "int conflictDetected=0;\n";
                    *out << ind << "int currentExplainLevel = executor->getNextExplainLevel();\n";
                    *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                    *out << ind << "std::vector<int> propLiterals({currentDecisionLevel});\n";
                    *out << ind << "std::vector<int> reasonStack;\n";
                    *out << ind++ << "for(int lit : unfoundedSetForComponent"<<componentId<<"){\n";
                        *out << ind << "Tuple* starter = factory.getTupleFromInternalID(lit);\n";
                        *out << ind << "if(starter == NULL || starter->isFalse() || foundnessFactory[lit]>=0) continue;\n";
                        *out << ind++ << "if(";
                        for(int predId=0;predId < scc[componentId].size();predId++){
                            std::string predName = program->getPredicateName(scc[componentId][predId]);
                            if(predId > 0) *out << " || "; 
                            *out << "starter->getPredicateName()==_"<<predName;
                        }
                        *out << "){\n";
                            *out << ind << "if(starter->isTrue() && conflictDetected==0) conflictDetected=-lit;\n";
                            *out << ind << "propLiterals.push_back(-lit);\n";
                            *out << ind << "int& visitedLevel = visitedExplainLiteral[lit];\n";
                            *out << ind++ << "if(visitedLevel!=currentExplainLevel){\n";
                                *out << ind << "visitedLevel = currentExplainLevel;\n";
                                *out << ind << "reasonStack.push_back(lit);\n";
                            *out << --ind << "}\n";
                            *out << ind << "reasonForLiteral[-lit]=shared_reason;\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout << \" Computing Reason \"<<std::endl;\n";
                    #endif
                    *out << ind++ << "if(currentDecisionLevel > 0){\n";
                        *out << ind++ << "while(!reasonStack.empty()){\n";
                            *out << ind << "int lit = reasonStack.back();\n";
                            *out << ind << "reasonStack.pop_back();\n";
                            *out << ind << "Tuple* starter = factory.getTupleFromInternalID(lit);\n";
                            #ifdef TRACE_PROPAGATION
                            *out << ind << "std::cout << \"Searching reason for: \";printTuple(starter);\n";
                            #endif
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout << \"     Searching False Body for \"<<starter->toString()<<std::endl;\n";
                            #endif
                            bool addElse=false;
                            for(int predId : scc[componentId]){
                                std::string predName = program->getPredicateName(predId);
                                for(unsigned ruleId = 0; ruleId < program->getRules().size(); ruleId++){
                                    const aspc::Rule* r = &programRules[ruleId];
                                    if(!r->isConstraint() && r->getHead()[0].getPredicateName()==predName){
                                        bool isExitRule = true;
                                        for(const aspc::Literal& l : r->getBodyLiterals()){
                                            if(componentPred.count(l.getPredicateName())!=0)
                                                isExitRule=false;
                                        }
                                        // if(!isExitRule) continue;
                                        for(int rId : ruleToSubProgram[ruleId]){
                                            aspc::Rule subRule(compilingProgram->getRule(rId));
                                            const aspc::Atom* head=NULL;
                                            const aspc::Literal* body=NULL;
                                            if(!subRule.isConstraint()){
                                                head=&subRule.getHead()[0];
                                                body=&subRule.getBodyLiterals()[0];
                                            }else{
                                                bool supportsAux=false;
                                                for(const aspc::Literal& l : subRule.getBodyLiterals()){
                                                    if(builder->isAuxPredicate(l.getPredicateName())){
                                                        supportsAux=true;
                                                        break;
                                                    }
                                                }
                                                if(!supportsAux){
                                                    if(subRule.getBodyLiterals().size() != 2 || subRule.getBodyLiterals()[0].isNegated() || ! subRule.getBodyLiterals()[1].isNegated()){
                                                        subRule.print();
                                                        std::cout << "Error:    Unexpexted constraint format. Expected constraint :-l1,not l2"<<std::endl;
                                                        std::exit(180);
                                                    }else{
                                                        head=&subRule.getBodyLiterals()[1].getAtom();
                                                        body=&subRule.getBodyLiterals()[0];
                                                    }
                                                }
                                            }
                                            if(head != NULL && body!=NULL){
                                                // h:-b || :-sup, not h || h :- aux || sup:-b || sup :- aux
                                                // for exit rule must be considered
                                                //      h:-b
                                                //      h:-aux
                                                //      :-sup not h
                                                if(isExitRule && head->getPredicateName()!=predName) continue;

                                                std::string printElse = addElse ? "": "";
                                                addElse=true;
                                                *out << ind++ <<printElse<< "if(starter->getPredicateName() == _"<<head->getPredicateName()<<"){\n";
                                                std::unordered_set<std::string> boundTerms;
                                                unsigned closinPars =1;
                                                for(unsigned k = 0; k < head->getAriety(); k++){
                                                    std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                                    if(head->isVariableTermAt(k) && boundTerms.count(head->getTermAt(k))==0){
                                                        *out << ind << "int " << term << "=starter->at("<<k<<");\n";
                                                        boundTerms.insert(term);
                                                    }else{
                                                        *out << ind++ << "if(" << term << " == starter->at("<<k<<")){\n";
                                                        closinPars++;
                                                    }
                                                }
                                                // unfounded must be navigated only for recursive rule of the form
                                                //      :-sup, not h
                                                bool navigateUnfounded=!isExitRule && head->getPredicateName()==predName && builder->isSupPredicate(body->getPredicateName());
                                                
                                                if(body->isBoundedLiteral(boundTerms)){

                                                    std::string terms="";
                                                    for(unsigned k = 0; k < body->getAriety(); k++){
                                                        std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                                        if(terms!="")
                                                            terms+=",";
                                                        terms+=term;
                                                    }
                                                    *out << ind << "Tuple* tuple = factory.find({"<<terms<<"},_"<<body->getPredicateName()<<");\n";
                                                    *out << ind++ << "if(tuple!=NULL){\n";
                                                    closinPars++;

                                                }else{
                                                    std::string terms="";
                                                    std::vector<unsigned> boundIndices;
                                                    for(unsigned k = 0; k < body->getAriety(); k++){
                                                        std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                                        if(!body->isVariableTermAt(k) || boundTerms.count(body->getTermAt(k))!=0){
                                                            if(terms!="")
                                                                terms+=",";
                                                            terms+=term;
                                                            boundIndices.push_back(k);
                                                        }
                                                    }
                                                    *out << ind << "const std::vector<int>* tuplesF = &f"<<body->getPredicateName()<<"_";
                                                    for(unsigned k : boundIndices){
                                                        *out << k << "_";
                                                    }
                                                    *out << ".getValuesVec({"<<terms<<"});\n";
                                                    if(navigateUnfounded){
                                                        // undefined must be navigated only for recursive rule in the following cases
                                                        //      :-sup, not h 
                                                        //      h :- aux (it might be avoided since aux are not navigated)
                                                        *out << ind << "const std::vector<int>* tuplesU = &u"<<body->getPredicateName()<<"_";
                                                        for(unsigned k : boundIndices){
                                                            *out << k << "_";
                                                        }
                                                        *out << ".getValuesVec({"<<terms<<"});\n";

                                                        *out << ind++ << "for(unsigned i=0; i<tuplesF->size()+tuplesU->size();i++){\n";
                                                        closinPars++;
                                                            *out << ind << "Tuple* tuple = i<tupleF->size() ? factory.getTupleFromInternalID(tuplesF->at(i)) : factory.getTupleFromInternalID(tuplesU->at(i-tuplesF->size()));\n";
                                                    }else{
                                                        *out << ind++ << "for(unsigned i=0; i<tuplesF->size();i++){\n";
                                                        closinPars++;
                                                            *out << ind << "Tuple* tuple =factory.getTupleFromInternalID(tuplesF->at(i));\n";
                                                    }
                                                        *out << ind++ << "if(tuple!=NULL){\n";
                                                        closinPars++;
                                                }
                                                #ifdef TRACE_PROPAGATOR
                                                    *out << ind << "std::cout << \"         Add To Reason ~\"<<tuple->toString()<<std::endl;\n";
                                                #endif
                                                *out << ind++ << "if(tuple->isFalse())\n";
                                                    *out << ind-- << "shared_reason.get()->insert(-tuple->getId());\n";
                                                if(navigateUnfounded){
                                                    *out << ind++ << "else if(foundnessFactory[tuple->getId()]<0){\n";
                                                        *out << ind << "int& visitedLevel = visitedExplainLiteral[tuple->getId()];\n";
                                                        *out << ind++ << "if(visitedLevel!=currentExplainLevel){\n";
                                                            *out << ind << "visitedLevel = currentExplainLevel;\n";
                                                            *out << ind << "reasonStack.push_back(tuple->getId());\n";
                                                        *out << --ind << "}\n";
                                                    *out << --ind << "}\n";
                                                }
                                                
                                                while (closinPars>0){
                                                    *out << --ind << "}\n";
                                                    closinPars--;
                                                }

                                            }
                                        }
                                    }
                                }
                            }
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                     #ifdef TRACE_UNFOUNDED
                        *out << ind << "std::cout<<\"UnfoundedSet\"<<std::endl;\n";
                    #endif
                    *out << ind++ << "for(int lit : unfoundedSetForComponent"<<componentId<<"){\n";
                        *out << ind << "Tuple* starter = factory.getTupleFromInternalID(lit);\n";
                        *out << ind << "if(starter == NULL || starter->isFalse() || foundnessFactory[lit]>=0) continue;\n";
                        #ifdef TRACE_UNFOUNDED
                            *out << ind << "std::cout<<\"   \";printTuple(starter);\n";
                        #endif
                        *out << ind << "foundnessFactory[lit]=1;\n";
                        *out << ind << "auto oldSP = sourcePointers"<<componentId<<".find(lit);\n";
                        *out << ind++ << "if(oldSP!=sourcePointers"<<componentId<<".end()){\n";
                            *out << ind << "supportedLiterals"<<componentId<<"[oldSP->second].push_back(lit);\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "Tuple* spTuple = factory.getTupleFromInternalID(oldSP->second);\n";
                                *out << ind << "Tuple* tuple = factory.getTupleFromInternalID(lit);\n";
                                *out << ind << "std::cout << spTuple->toString() << \" supports \"<<tuple->toString()<<std::endl;\n";
                            #endif

                        *out << --ind << "}\n";
                        #ifdef TRACE_PROPAGATOR
                        *out << ind << "else std::cout << \"No SP for : \"<<starter->toString()<<std::endl;\n";
                        #endif
                    *out << --ind << "}\n";
                    *out << ind++ << "if(conflictDetected!=0) {\n";
                        #ifdef TRACE_PROGATATOR
                            *out << ind << "std::cout << \" Conflict detected:  Unfounded literal already true\"<<tuple->toString()<<std::endl;\n";
                        #endif
                        *out << ind << "executor->handleConflict(conflictDetected,literalToPropagate);\n";
                        *out << ind << "if(currentDecisionLevel > 0) for(int i=1; i<propLiterals.size(); i++) reasonForLiteral[propLiterals[i]].get()->clear();\n";
                    *out << --ind << "}else if(propLiterals.size()>1){\n";
                    ind++;
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout << \" Propagating Unfounded set\"<<std::endl;\n";
                        #endif
                        #ifdef TRACE_PROPAGATION
                            *out << ind << "std::cout << \"Unfounded set reason: {\"<<std::endl;\n";
                            *out << ind << "for(int i =0; i<shared_reason.get()->size();i++){ int uVar = shared_reason.get()->at(i) > 0 ? shared_reason.get()->at(i) : -shared_reason.get()->at(i); std::cout <<\"   \";printTuple(factory.getTupleFromInternalID(uVar));}\n";
                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                        #endif
                            *out << ind << "executor->executeProgramOnFacts(propLiterals,literalToPropagate,true);\n";
                                                    
                    *out << --ind << "}\n";
                    *out << ind << "unfoundedSetForComponent"<<componentId<<".clear();\n";

                *out << --ind << "}//close if empty unfounded set\n";

                // *out << ind++ << "for(auto pair : supportedLiterals0){\n";
                    //  *out << ind << "std::cout << \"Literals supported by \";std::cout<<factory.getTupleFromInternalID(pair.first)->toString();std::cout<<\": [\";\n";
                    //  *out << ind << "for(int lit : pair.second) {std::cout<<factory.getTupleFromInternalID(lit)->toString()<<\" \";}\n";
                    //  *out << ind << "std::cout<<\"]\"<<std::endl;\n";
                // *out << --ind << "}\n";
                // *out << ind++ << "for(auto pair : supportedAux0){\n";
                    //  *out << ind << "std::cout << \"Aux Literals supported by \";std::cout<<factory.getTupleFromInternalID(pair.first)->toString();std::cout<<\": [\";\n";
                    //  *out << ind << "for(int lit : pair.second) {std::cout<<factory.getTupleFromInternalID(lit)->toString()<<\" \";}\n";
                    //  *out << ind << "std::cout<<\"]\"<<std::endl;\n";
                // *out << --ind << "}\n";
                // *out << ind << "std::cout<<\"source pointers\"<<std::endl;\n";
                // *out << ind++ << "for(auto pair : sourcePointers1){\n";
                    //  *out << ind << "std::cout <<factory.getTupleFromInternalID(pair.first)->toString()<<\": \"<<factory.getTupleFromInternalID(pair.second)->toString()<<std::endl;\n";
                // *out << --ind << "}\n";
                // *out << ind << "int r_2_3 = factory.find({2,3},&_r)->getId();\n";
                // *out << ind << "int r_2_4 = factory.find({2,4},&_r)->getId();\n";
                // *out << ind << "int r_2_5 = factory.find({2,5},&_r)->getId();\n";
                // *out << ind << "std::cout <<\"sp r(2,3): \"<<factory.getTupleFromInternalID(sourcePointers1[r_2_3])->toString()<<std::endl;\n";
                // *out << ind << "std::cout <<\"sp r(2,4): \"<<factory.getTupleFromInternalID(sourcePointers1[r_2_4])->toString()<<std::endl;\n";
                // *out << ind << "std::cout <<\"sp r(2,5): \"<<factory.getTupleFromInternalID(sourcePointers1[r_2_5])->toString()<<std::endl;\n";
                // *out << ind << "int sup_1_2_3 = factory.find({2,3},&_sup_1)->getId();\n";
                // *out << ind << "int sup_1_2_4 = factory.find({2,4},&_sup_1)->getId();\n";
                // *out << ind << "int sup_0_2_4 = factory.find({2,4},&_sup_0)->getId();\n";
                // *out << ind << "int sup_1_2_5 = factory.find({2,5},&_sup_1)->getId();\n";
                // *out << ind << "for(int sup : supportedLiterals1[sup_0_2_4]) std::cout<<factory.getTupleFromInternalID(sup)->toString()<<\" \";std::cout<<std::endl;\n";
                // *out << ind << "std::cout <<\"sp sup_1(2,3): \"<<factory.getTupleFromInternalID(sourcePointers1[sup_1_2_3])->toString()<<std::endl;\n";
                // *out << ind << "std::cout <<\"sp sup_1(2,4): \"<<factory.getTupleFromInternalID(sourcePointers1[sup_1_2_4])->toString()<<std::endl;\n";
                // *out << ind << "std::cout <<\"sp sup_1(2,5): \"<<factory.getTupleFromInternalID(sourcePointers1[sup_1_2_5])->toString()<<std::endl;\n";
                // *out << ind << "auto t2_e = std::chrono::high_resolution_clock::now();\n";
                // *out << ind << "auto duration_e = std::chrono::duration_cast<std::chrono::microseconds>(t2_e - t1_e).count();\n";
                // *out << ind << "std::cout << \"time \" << duration_e / 1000 << endl;\n";
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout << \"Supported Literals\" <<std::endl;\n";
                    // *out << ind++ << "for(int lit =1;lit<supportedLiterals1.size();lit++){\n";
                    //     *out << ind++ << "if(!supportedLiterals1[lit].empty()){\n";
                    //         *out << ind << "std::cout << factory.getTupleFromInternalID(lit)->toString() << \" -> [\";\n";
                    //         *out << ind << "for(int l : supportedLiterals1[lit]) std::cout << factory.getTupleFromInternalID(l)->toString() << \" \";\n";
                    //         *out << ind << "std::cout << std::endl;\n";
                    //     *out << --ind << "}\n";
                    // *out << --ind << "}\n";
                #endif
            *out << --ind << "}// close unfoundedPropagatorForComponent\n";
        }

        *out << ind++ << "void checkFoundness(){\n";
            //NOTICE: suppport comes only from positive literal
            // *out << ind << "const auto* internalLits=&levelToIntLiterals[unfounded[0]];\n";
            // *out << ind << "for(unsigned i=0;i<internalLits->size();i++) if(internalLits->at(i)<0) if(i==0) unfounded[0]=internalLits->at(i); else unfounded.push_back(internalLits->at(i));\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Check Foundness\"<<std::endl;\n";
                *out << ind << "if(falseLits.empty()) std::cout << \"   No False Lits at current decision level\"<<std::endl;\n";
                *out << ind << "else{\n";
                    *out << ind << "std::cout << \"   False Lits at current decision level\"<<std::endl;\n";
                    *out << ind++ << "for(int i=0;i<falseLits.size();i++){\n";
                        *out << ind << "Tuple* tuple = factory.getTupleFromInternalID(-falseLits[i]);\n";
                        *out << ind << "if(tuple == NULL) std::cout << -falseLits[i]<<std::endl;\n";
                        *out << ind << "else std::cout << -falseLits[i] << \"     ~\"<<tuple->toString()<<std::endl;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            #endif
            // *out << ind << "std::unordered_set<int> visited;\n";
            *out << ind++ << "while(!falseLits.empty()){\n";
                #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout << \"Next Lit\" << std::endl;\n";
                #endif
                *out << ind << "int starter = falseLits.back();\n";
                *out << ind << "int current = starter >= 0 ? starter : -starter;\n";
                *out << ind << "falseLits.pop_back();\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "const Tuple* tuple = factory.getTupleFromInternalID(current);\n";
                        *out << ind << "if(tuple==NULL) std::cout << \"NULL\" <<std::endl;\n";
                        *out << ind << "std::cout<<\"   Searching Literal supported by \"<<tuple->toString()<<std::endl;\n";
                    #endif
                    for(int componentId : recursiveComponent){
                        *out << ind++ << "{\n";
                            *out << ind << "std::vector<int>& supported = supportedLiterals"<<componentId<<"[current];\n";
                            *out << ind << "int saving=0;\n";
                            *out << ind++ << "for(int i=0;i < supported.size(); i++){\n";
                                *out << ind << "int lit = supported[i];\n";
                                *out << ind << "Tuple* removingLit = factory.getTupleFromInternalID(lit);\n";
                                *out << ind << "if(removingLit->isFalse()){supported[saving++]=supported[i]; continue;}\n";
                                *out << ind++ << "if(foundnessFactory[lit]>=0){\n";
                                    *out << ind << "foundnessFactory[lit]=-1;\n";
                                    *out << ind << "unfoundedSetForComponent"<<componentId<<".push_back(lit);\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"   Adding to Unfounded Set \"<<removingLit->toString()<<std::endl;\n";
                                    #endif
                                    *out << ind << "falseLits.push_back(lit);\n";
                                *out << --ind << "}//close if\n";
                            *out << --ind << "}//close for\n";
                            *out << ind << "supported.resize(saving);\n";
                            *out << ind++ << "if(current < supportedAux"<<componentId<<".size()){\n";
                                *out << ind << "std::vector<int>& supAux = supportedAux"<<componentId<<"[current];\n";
                                *out << ind++ << "for(int lit : supAux){\n";
                                    *out << ind << "Tuple* removingLit = factory.getTupleFromInternalID(lit);\n";
                                    *out << ind++ << "if(!removingLit->isFalse() && foundnessFactory[lit]>=0){\n";
                                        *out << ind << "foundnessFactory[lit]=-1;\n";
                                        *out << ind << "unfoundedSetForComponent"<<componentId<<".push_back(lit);\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"   Adding to Unfounded Set \"<<removingLit->toString()<<std::endl;\n";
                                        #endif
                                        *out << ind << "falseLits.push_back(lit);\n";
                                    *out << --ind << "}//close if\n";
                                *out << --ind << "}//close for\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}//close local scope\n";
                    }
                // *out << --ind << "}//close if\n";
            *out << --ind << "}//close while\n";
        *out << --ind << "}//close function\n";
        *out << ind++ << "void Executor::checkUnfoundedSets(std::vector<int>& literalsToPropagate,Executor* executor){\n";
            *out << ind << "checkFoundness();\n";
            for(int componentId : recursiveComponent){
                *out << ind << "unfoundedPropagatorForComponent"<<componentId<<"(literalsToPropagate,executor);\n";
            }
        *out << --ind << "}\n";

    }


    // std::cout << "Unfounded Procedures Built"<<std::endl;
    // std::cout << "Building Generator"<<std::endl;
    
    *out << ind++ << "void Executor::undefLiteralsReceived(){\n";
        *out << ind << "factory.setGenerated(true);\n";

        #ifdef TRACE_PROPAGATOR
        *out << ind << "std::cout<<\"Undef received\"<<std::endl;\n";
        #endif
        *out << ind << "undefinedLoaded=true;\n";
        *out << ind << "std::cout<<\"Undef received \"<<factory.size()<<std::endl;\n";
        buildGenerator(builder,program);
        *out << ind << "std::cout<<\"Generated\"<<factory.size()<<std::endl;\n";
        *out << ind << "buildingReasonStack.reserve(2*factory.size());\n";
        *out << ind << "conflictReason.reserve(factory.size());\n";

        // *out << ind << "factory.printStats();\n";
        // *out << ind << "factory.rehash();\n";
        // *out << ind << "factory.printStats();\n";
        // *out << ind << "std::cout << \"Reach size: \" << ureachable_color_.getValuesVec({}).size()<<std::endl;\n";

        // *out << ind << "for(int id : ureachable_color_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : preachable_color_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : ue_.getValuesVec({})) printTuple(factory.getTupleFromInternalID(id));\n";
        // *out << ind << "for(int id : pe_.getValuesVec({})) printTuple(factory.getTupleFromInternalID(id));\n";
        // *out << ind << "for(int id : uvertex_color_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : pvertex_color_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : ugtnumber_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : pgtnumber_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : ufirst_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "for(int id : pfirst_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        // *out << ind << "std::cout << \"reachable_color size:  \" << ureachable_color_.getValuesVec({}).size()+preachable_color_.getValuesVec({}).size()<<std::endl;\n";
        // *out << ind << "std::cout << \"e size:                \" << ue_.getValuesVec({}).size()+pe_.getValuesVec({}).size()<<std::endl;\n";
        // *out << ind << "std::cout << \"vertex_color size:     \" << uvertex_color_.getValuesVec({}).size()+pvertex_color_.getValuesVec({}).size()<<std::endl;\n";
        // *out << ind << "std::cout << \"gtnumber size:         \" << ugtnumber_.getValuesVec({}).size()+pgtnumber_.getValuesVec({}).size()<<std::endl;\n";
        // *out << ind << "std::cout << \"first size:            \" << ufirst_.getValuesVec({}).size()+pfirst_.getValuesVec({}).size()<<std::endl;\n";
        
        *out << ind << "visitedExplainLiteral.resize(2*factory.size());\n";
        *out << ind << "explainLevel=1;\n";
        // *out << ind++ << "{\n";
            // *out << ind << "for(int id: urange_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
            // *out << ind << "for(int id: prange_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: uq_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: ua_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: up_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: ubody_0_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: ubody_1_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: uagg_set_0_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "for(int id: uagg_set_1_.getValuesVec({})) factory.getTupleFromInternalID(id)->print();\n";
        //     *out << ind << "exit(180);\n";
        // *out << --ind << "}\n";
        #ifdef GROUNDING
            for(std::string pred : builder->getPrintingPredicates()){
                *out << ind++ << "for(int internalId : u"<<pred<<"_.getValues({})){\n";
                    *out << ind << "std::cout<<\"Undefined literal: \";factory.getTupleFromInternalID(internalId)->print();\n";
                *out << --ind << "}\n";
            }
            *out << ind << "exit(-1);\n";
        #endif

        #ifdef TRACE_PROPAGATOR
            *out << ind << "std::cout<<possibleSum.size()<<std::endl;\n";
            *out << ind << "std::cout<<possibleSum.bucket_count()<<std::endl;\n";
            *out << ind << "std::cout<<possibleSum.load_factor()<<std::endl;\n";
            *out << ind++ << "for(auto pair : actualSum){\n";
                *out << ind << "factory.getTupleFromInternalID(pair.first)->print();\n";
                *out << ind << "std::cout<<\" ActualSum \"<<pair.second<<std::endl;\n";
            *out << --ind <<"}\n";
            *out << ind++ << "for(auto pair : possibleSum){\n";
                *out << ind << "factory.getTupleFromInternalID(pair.first)->print();\n";
                *out << ind << "std::cout<<\"PossibleSum \"<<pair.second<<std::endl;\n";
            *out << --ind <<"}\n";
            *out << ind << "std::cout<<\"Generated\"<<std::endl;\n";
            *out << ind << "std::cout<<\"exit undef received\"<<std::endl;\n";
        #endif
        //*out << ind << "trace_msg(eagerprop,2,\"Interna lUndefined Computed\");\n";

    *out << --ind << "}\n";
    // std::cout << "Generator Built"<<std::endl;

    *out << ind++ << "inline void Executor::addedVarName(int var, const std::string & atom) {\n";
        // *out << ind << "exit(180);\n";
        #ifdef TRACE_PROPAGATOR
         *out << ind << "std::cout<<var<<\" \" << atom<<std::endl;\n";
        #endif
        *out << ind << "std::vector<int> terms;\n";
        *out << ind << "int predicate = parseTuple(atom,terms);\n";
        *out << ind << "Tuple* t = factory.addNewTuple(terms,predicate,var);\n";

        //  *out << ind << "factory.addNewTuple(std::array<int>(terms.data()),predicate,var);\n";
    *out << --ind << "}\n";
    // ---------------------- end addedVarName(int var, const std::string & atom) --------------------------------------//

    // ---------------------- clearPropagatedLiterals() --------------------------------------//
    *out << ind++ << "void Executor::clearPropagations() {\n";
    *out << ind << "propagatedLiteralsAndReasons.clear();\n";
    *out << --ind << "}\n";

    // ---------------------- end clearPropagatedLiterals() --------------------------------------//

    // ---------------------- clear() --------------------------------------//
    *out << ind++ << "void Executor::clear() {\n";
    *out << ind << "failedConstraints.clear();\n";
    // *out << ind << "predicateToAuxiliaryMaps.clear();\n";

    if (mode == LAZY_MODE) {
        *out << ind << "predicateToFalseAuxiliaryMaps.clear();\n";
    }

    // for (const pair<std::string, unsigned>& predicate : predicates) {
    //     if (idbs.count(predicate.first) || headPredicates.count(predicate.first)) {
    //         *out << ind << "w" << predicate.first << ".clear();\n";
    //     }
    // }


    // for (const std::string & predicate : modelGeneratorPredicatesInNegativeReasons) {
    //     if (idbs.count(predicate) || headPredicates.count(predicate)) {
    //         *out << ind << "neg_w" << predicate << ".clear();\n";
    //     }
    // }

    // for (const auto & entry : predicateToAuxiliaryMaps) {
    //     for (const auto & auxSet : entry.second) {
    //         if (idbs.count(entry.first) || headPredicates.count(entry.first)) {
    //             *out << ind << "p" << auxSet << ".clear();\n";
    //         }
    //     }
    // }

    // for (const auto & entry : predicateToFalseAuxiliaryMaps) {
    //     for (const auto & auxSet : entry.second) {
    //         if (idbs.count(entry.first) || headPredicates.count(entry.first)) {
    //             *out << ind << "f" << auxSet << ".clear();\n";
    //         }
    //     }
    // }

    *out << --ind << "}\n";

    // ---------------------- end clear() --------------------------------------//

    // ---------------------- init() --------------------------------------//
    *out << ind++ << "void Executor::init() {\n";
    string reference = (mode == EAGER_MODE) ? "&" : "";

    for (const pair<std::string, unsigned>& predicate : predicates) {

        *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = _" << predicate.first << ";\n";
    }
    for (const pair<std::string, unsigned>& predicate : aggregatePredicates) {
        if(predicates.count(predicate)==0){
            *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = _" << predicate.first << ";\n";
        }
    }
    for (const pair<std::string, unsigned>& predicate : predicatesNotCompletion) {

        *out << ind << "stringToUniqueStringPointer[\"" << predicate.first << "\"] = _" << predicate.first << ";\n";
    }
    for(std::string pred : predicateNames){
        *out << ind << "Executor::predicateIds.push_back(\""<<pred<<"\");\n";
        *out << ind << "factory.addPredicate();\n";
    }

    for(auto pair :predicateToOrderdedAux ){
        *out << ind << "factory.setIndexForAggregateSet("<<pair.second<<",_"<<pair.first<<");\n";
    }
    *out << --ind << "}\n";
    *out << ind++ << "void Executor::printStatus(){\n";
        *out << ind++ << "for(const Tuple* t : factory.getTuples())\n";
            *out << ind << "if(!t->isInternalLiteral()) printTuple(t);\n";
    *out << --ind << "}\n";
    // ---------------------- end init() --------------------------------------//
    *out << ind++ << "bool propUndefined(const Tuple* tupleU,bool isNegated,std::vector<int>& stack,bool asNegative,std::vector<int> & propagatedLiterals,std::unordered_set<int> & remainingPropagatingLiterals,const Solver* solver,PropComparator& propComparison,unsigned minConflict, unsigned minHeapSize, unsigned maxHeapSize, unsigned heapSize){\n";
        *out << ind++ << "if(tupleU->getWaspID() == 0){\n";
            *out << ind << "bool propagated=false;\n";
            *out << ind << "Tuple* realTupleU=factory.find(*tupleU);\n";
            *out << ind++ << "if(isNegated == asNegative){\n";
                *out << ind++ << "if(realTupleU->isFalse()){\n";
                    #ifdef TRACE_PROPAGATION
                        *out << ind << "std::cout<<\"Conflict: Literal is already false\"<<std::endl;\n";
                    #endif
                    *out << ind << "return true;\n";
                *out << --ind << "}else if(realTupleU->isUndef()){\n";
                ind++;
                    *out << ind << "const auto& insertResult = realTupleU->setStatus(True);\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        *out << ind << "factory.removeFromCollisionsList(realTupleU->getId());\n";

                        *out << ind << "insertTrue(insertResult);\n";
                        for(unsigned ruleId=0; ruleId<program.getRules().size(); ruleId++){
                            const aspc::Rule* rule = &program.getRules()[ruleId];
                            if(!rule->isConstraint() && rule->containsAggregate()){
                                const aspc::Atom* aggrId = &rule->getHead()[0];
                                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                                const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                                unsigned sumVar = 0;
                                if(!aggregateRelation->getAggregate().isSum())
                                    continue;
                                if(!builder->isAggrSetPredicate(aggrSetLit->getPredicateName())){
                                    std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                                    for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                                        if(aggrSetLit->getTermAt(i)==var){
                                            sumVar=i;
                                            break;
                                        }
                                    }
                                }

                                *out << ind++ << "if(tupleU->getPredicateName() == _"<<aggrSetLit->getPredicateName()<<"){\n";
                                    if(aggrId->getAriety() == 0){
                                        *out << ind << "int itAggrId = factory.find({},_"<<aggrId->getPredicateName()<<")->getId();\n";
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
                                                *out << ind << "const std::vector<int>* aggrIds = &"<<sign<<mapName<<".getValuesVec({"<<terms<<"});\n";
                                                *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                                    *out << ind << "int itAggrId = aggrIds->at(i);\n";
                                                    *out << ind << "actualSum[itAggrId]+=tupleU->at("<<sumVar<<");\n";
                                                    *out << ind << "possibleSum[itAggrId]-=tupleU->at("<<sumVar<<");\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                        }
                                    }
                                *out << --ind << "}\n";
                            }
                        }
                        #ifdef TRACE_CONFLICT
                            *out << ind << "std::cout<<\"Prop::Propagating Literal as True at decisionLevel \"<<currentDecisionLevel;\n";
                            *out << ind << "printTuple(tupleU);\n";
                        #endif

                        *out << ind << "propagated = true;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}else{\n";
            ind++;
                *out << ind++ << "if(realTupleU->isTrue()){\n";
                    #ifdef TRACE_PROPAGATION
                        *out << ind << "std::cout<<\"Conflict: Literal is already true \";printTuple(tupleU);\n";
                    #endif
                    *out << ind << "return true;\n";
                *out << --ind << "}else if(realTupleU->isUndef()){\n";
                ind++;
                    *out << ind << "const auto& insertResult = realTupleU->setStatus(False);\n";
                    *out << ind++ << "if (insertResult.second) {\n";
                        *out << ind << "factory.removeFromCollisionsList(realTupleU->getId());\n";
                        *out << ind << "falseLits.push_back(-realTupleU->getId());\n";
                        *out << ind << "insertFalse(insertResult);\n";

                        for(unsigned ruleId=0; ruleId<program.getRules().size(); ruleId++){
                            const aspc::Rule* rule = &program.getRules()[ruleId];
                            if(!rule->isConstraint() && rule->containsAggregate()){
                                const aspc::Atom* aggrId = &rule->getHead()[0];
                                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                                const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                                unsigned sumVar = 0;
                                if(!aggregateRelation->getAggregate().isSum())
                                    continue;

                                if(!builder->isAggrSetPredicate(aggrSetLit->getPredicateName())){
                                    std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                                    for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                                        if(aggrSetLit->getTermAt(i)==var){
                                            sumVar=i;
                                            break;
                                        }
                                    }
                                }
                                *out << ind++ << "if(tupleU->getPredicateName() == _"<<aggrSetLit->getPredicateName()<<"){\n";
                                    if(aggrId->getAriety() == 0){
                                        *out << ind << "int itAggrId = factory.find({},_"<<aggrId->getPredicateName()<<")->getId();\n";
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
                                                *out << ind << "const std::vector<int>* aggrIds = &"<<sign<<mapName<<".getValuesVec({"<<terms<<"});\n";
                                                *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                                    *out << ind << "int itAggrId = aggrIds->at(i);\n";
                                                    *out << ind << "possibleSum[itAggrId]-=tupleU->at("<<sumVar<<");\n";
                                                *out << --ind << "}\n";
                                            *out << --ind << "}\n";
                                        }
                                    }
                                *out << --ind << "}\n";
                            }
                        }
                        #ifdef TRACE_CONFLICT
                            *out << ind << "std::cout<<\"Prop::Propagating Literal as False at decisionLevel \"<<currentDecisionLevel;\n";
                            *out << ind << "printTuple(tupleU);\n";
                        #endif

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
            *out << ind << "int sign = isNegated == asNegative ? 1 : -1;\n";
            *out << ind++ << "if(remainingPropagatingLiterals.count(it*sign)==0){\n";
                #ifdef TRACE_PROPAGATION
                    *out << ind << "std::cout<<\"Prop::Propagating external literal: \"<<sign<<\" at decisionLevel \"<<currentDecisionLevel;\n";
                    *out << ind << "printTuple(tupleU);\n";
                #endif

                *out << ind << "remainingPropagatingLiterals.insert(it*sign);\n";
                *out << ind << "propagatedLiterals.push_back(it*sign);\n";
                *out << ind++ << "if(conflictCount > minConflict){\n";
                    //  *out << ind << "if(propagatedLiterals.size() == heapSize){/*std::cout<<\"Heap size: \"<<heapSize<<std::endl;*/std::make_heap(propagatedLiterals.begin(),propagatedLiterals.end(),propComparison);/*for(int i=0; i < heapSize && i < propagatedLiterals.size(); i++)std::cout<<solver->getActivityForLiteral(propagatedLiterals[i])<<\" \";std::cout<<std::endl;*/}\n";
                    *out << ind++ << "if(propagatedLiterals.size() > heapSize){\n";
                        *out << ind << "int heapMinimum = propagatedLiterals.front();\n";
                        *out << ind << "Activity heapMinimumWeight = solver->getActivityForLiteral(heapMinimum);\n";
                        *out << ind << "Activity currentWeight = solver->getActivityForLiteral(propagatedLiterals.back());\n";
                        *out << ind++ << "if(currentWeight > heapMinimumWeight){\n";
                            *out << ind << "std::pop_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);\n";
                            *out << ind << "std::swap(propagatedLiterals[heapSize-1],propagatedLiterals[propagatedLiterals.size()-1]);\n";
                            *out << ind << "std::push_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);\n";
                        *out << --ind << "}\n";
                    // *out << --ind << "}\n";
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind << "std::push_heap(propagatedLiterals.begin(),propagatedLiterals.end(),propComparison);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
        // #ifdef TRACE_PROPAGATION
        // *out << ind << "std::cout<<\"exit propundef\"<<std::endl;\n";
        // #endif
        *out << ind << "return false;\n";

    *out << --ind << "}\n";

    // *out << ind++ << "void callSolver(std::string trueConstraint,const Solver* solver){\n";
    //     *out << ind << "solver->printConstraints(trueConstraint);\n";
    // *out << --ind << "}\n";

    aspc::EagerProgram& lazy = builder->getEndProgram();
    //predicates that appear in the body of some lazy rule
    std::unordered_set<std::string> lazyBodyPredicates;
    std::unordered_set<std::string> lazyHeadPredicates;
    for(const aspc::Rule& r : lazy.getRules()){
        for(const aspc::Literal& l : r.getBodyLiterals()){
            lazyBodyPredicates.insert(l.getPredicateName());
        }
        for(const aspc::Atom& h : r.getHead()){
            lazyHeadPredicates.insert(h.getPredicateName());
        }
    }
    unordered_map<std::string,std::pair<char,std::unordered_map<std::string,std::set<std::string>>>> auxClearToPrefix={{"clearUndef",{'u',predicateToUndefAuxiliaryMaps}},{"clearTrue",{'p',predicateToUndefAuxiliaryMaps}},{"clearFalse",{'f',predicateToUndefAuxiliaryMaps}}};
    for(auto function_prefix: auxClearToPrefix){
        *out << ind++ << "inline void "<<function_prefix.first<<"(){\n";
        for(auto predicateToMaps : function_prefix.second.second){
            if(lazyBodyPredicates.count(predicateToMaps.first)!=0 && lazyHeadPredicates.count(predicateToMaps.first)!=0){
                for(auto mapName : predicateToMaps.second){
                    *out << ind << function_prefix.second.first<<mapName<<".clear();\n";
                }
            }
        }
        *out << --ind <<"}\n";
    }
    // *out << ind << "int TupleLight::countPredSize;\n";
    // *out << ind << "int TupleLight::countFor;\n";
    // *out << ind << "int TupleLight::countTrue;\n";
    *out << ind++ << "std::string Executor::printInternalLiterals(){\n";
        // *out << ind << "std::cout << \"Count if: \" <<TupleLight::countPredSize<<std::endl;\n";
        // *out << ind << "std::cout << \"Count for: \" <<TupleLight::countFor<<std::endl;\n";
        // *out << ind << "std::cout << \"Count true: \" <<TupleLight::countTrue<<std::endl;\n";
        // *out << ind << "std::cout << \"Load Factor: \" <<factory.loadFactor()<<std::endl;\n";
        // *out << ind << "std::cout << \"Conflict count: \"<<conflictCount<<std::endl;\n";
        // std::unordered_map<int,std::vector<int>> levelToIntLiterals;
        // std::unordered_map<int,std::shared_ptr<VectorAsSet<int>>> reasonForLiteral;
        // *out << ind << "std::cout << \"Stored reason count             \"<<reasonForLiteral.size()<<std::endl;\n";
        // *out << ind << "std::cout << \"Stored level count              \"<<levelToIntLiterals.size()<<std::endl;\n";
        // *out << ind << "int sum = 0,count=0;for(auto pair : levelToIntLiterals) if(pair.second.size()>0){count++;sum+=pair.second.size();}\n";
        // *out << ind << "if(count >0) std::cout << \"Averager per level              \"<<sum/count<<std::endl;\n";
        // *out << ind << "sum = 0;count=0;for(auto pair : reasonForLiteral) if(pair.second.get()->size()>0){count++;sum+=pair.second.get()->size();}\n";
        // *out << ind << "if(count >0) std::cout << \"Averager reason per literal     \"<<sum/count<<std::endl;\n";
        
        *out << ind << "std::string trueConstraint = \"\";\n";
        for(std::string pred : builder->getPrintingPredicates()){
            //predicate that appears in the head of some eager rules
            if(predicateToOrderdedAux.count(pred)!=0)
                *out << ind++ << "for(int internalId : p"<<pred<<"_.getValuesSet({})){\n";
            else
                *out << ind++ << "for(int internalId : p"<<pred<<"_.getValuesVec({})){\n";
                    *out << ind << "Tuple* tuple = factory.getTupleFromInternalID(internalId);\n";
                    *out << ind << "std::string tupleToString = tuple->size() > 0 ? \""<<pred<<"(\" : \""<<pred<<"\";\n";
                    *out << ind++ << "for(unsigned k=0; k<tuple->size();k++){\n";
                        *out << ind << "if(k>0) tupleToString+=\",\";\n";
                        *out << ind << "tupleToString+=ConstantsManager::getInstance().unmapConstant(tuple->at(k));\n";
                    *out << --ind << "}\n";
                    *out << ind << "tupleToString+= tuple->size() > 0 ? \")\" : \"\";\n";

                *out << ind << "std::cout << tupleToString <<\" \";\n";
                #ifdef PRINTCONSTRAINT
                *out << ind++ << "if(trueConstraint!=\"\" && trueConstraint.back()!=',')\n";
                    *out << ind-- << "trueConstraint+=\",\";\n";
                *out << ind << "trueConstraint+=tupleToString;\n";
                #endif
            *out << --ind << "}\n";
        }
        *out << ind << "std::cout << std::endl;\n";

        #ifdef PRINTCONSTRAINT
            *out << ind << "std::cout<<\"MODEL_AS_CONSTRAINT\"<<std::endl;\n";
            for(std::string pred : builder->getPrintingPredicates()){
                if(predicateToOrderdedAux.count(pred)!=0)
                    *out << ind++ << "for(int internalId : f"<<pred<<"_.getValuesSet({})){\n";
                else
                    *out << ind++ << "for(int internalId : f"<<pred<<"_.getValuesVec({})){\n";
                        *out << ind << "Tuple* tuple = factory.getTupleFromInternalID(internalId);\n";
                        *out << ind << "std::string tupleToString = \""<<pred<<"(\";\n";
                        *out << ind++ << "for(unsigned k=0; k<tuple->size();k++){\n";
                            *out << ind << "if(k>0) tupleToString+=\",\";\n";
                            *out << ind << "tupleToString+=ConstantsManager::getInstance().unmapConstant(tuple->at(k));\n";
                        *out << --ind << "}\n";
                        *out << ind << "tupleToString+=\")\";\n";
                        *out << ind << "std::cout<<\":-\"<<tupleToString <<\".\"<<std::endl;\n";
                    *out << --ind << "}\n";
            }

        #endif

        *out << ind << "TupleFactory lazyFactory;\n";
        for(int i=0;i<predicateNames.size();i++){
            *out << ind << "lazyFactory.addPredicate();\n";
        }
        GraphWithTarjanAlgorithm* graphNoCompletion = &lazy.getPositiveDG();
        std::vector<std::vector<int>> sccNoCompletion = graphNoCompletion->SCC();
        std::vector<aspc::Rule> lazyRules = lazy.getRules();
        std::vector<aspc::Atom> programFacts = builder->getFacts();
        for(int component=sccNoCompletion.size()-1; component>=0 ; component--){
            std::unordered_set<std::string> componentPredicateNames;
            for(int predId : sccNoCompletion[component]){
                componentPredicateNames.insert(lazy.getPredicateName(predId));
            }
            std::vector<int> exitRules;
            std::vector<int> recursiveRules;
            for(int ruleId=0;ruleId<lazyRules.size();ruleId++){
                if(lazyRules[ruleId].isConstraint()){
                    std::cout << "Error:\tConstraint not allowed into end program"<<std::endl;
                    exit(180);
                }else{
                    const aspc::Atom* head = &lazyRules[ruleId].getHead()[0];
                    if(componentPredicateNames.count(head->getPredicateName())!=0){
                        for(const aspc::Literal& l : lazyRules[ruleId].getBodyLiterals()){
                            if(componentPredicateNames.count(l.getPredicateName())!=0){
                                recursiveRules.push_back(ruleId);
                                break;
                            }
                        }
                        if(recursiveRules.empty() || recursiveRules.back() != ruleId)
                            exitRules.push_back(ruleId);
                    }
                }
            }
            bool isRecursive = sccNoCompletion[component].size() > 1;
            if(!isRecursive){
                for(int adj : graphNoCompletion->getAdjForNode(sccNoCompletion[component][0])){
                    if (adj == sccNoCompletion[component][0]){
                        isRecursive=true;
                        break;
                    }
                }
            }
            if(exitRules.size()+recursiveRules.size() > 0){

                *out << ind++ << "{\n";
                if(isRecursive){
                    *out << ind << "std::vector<int> stack;\n";
                }
                for(const aspc::Atom& fact : programFacts){
                    if(componentPredicateNames.count(fact.getPredicateName())!=0){
                        *out << ind++ << "{\n";
                            *out << ind << "std::vector<int> head({";
                            for(unsigned k=0; k<fact.getAriety(); k++){
                                std::string term = isInteger(fact.getTermAt(k)) ? fact.getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+fact.getTermAt(k)+"\")";
                                if(k>0)
                                    *out << ",";
                                *out << term;
                            }
                            *out << "});\n";
                            *out << ind << "Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,_"<<fact.getPredicateName()<<");\n";
                            *out << ind << "const auto& insertResult = tupleHead->setStatus(True);\n";
                            *out << ind++ << "if (insertResult.second) {\n";
                                *out << ind << "lazyFactory.removeFromCollisionsList(tupleHead->getId());\n";
                                *out << ind << "insertTrue(insertResult);\n";
                                if(isRecursive){
                                    *out << ind << "stack.push_back(tupleHead->getId());\n";
                                }
                                *out << ind << "std::cout<<\""<<fact.getPredicateName()<<"(\"";
                                for(unsigned k=0;k<fact.getAriety();k++){
                                    if(k>0)
                                        *out << "<<\",\"";
                                    *out << "<<ConstantsManager::getInstance().unmapConstant(head["<<k<<"])";
                                }
                                *out << "<<\")\"<<std::endl;\n";
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";
                    }
                }

                for(int ruleId:exitRules){
                    aspc::Rule r(lazyRules[ruleId]);
                    const aspc::Atom* head = &r.getHead()[0];
                    *out << ind++ << "{\n";
                    if(!lazyBodyPredicates.count(head->getPredicateName()) && !isRecursive){
                        *out << ind << "std::set<std::vector<int>> trueHeads;\n";
                    }
                        std::vector<unsigned> orderedBodyFormulas;
                        r.orderBodyFormulas(orderedBodyFormulas);
                        std::unordered_set<std::string> boundVariables;
                        unsigned closingPars=0;
                        for(unsigned formulaIndex: orderedBodyFormulas){
                            const aspc::Formula* f = r.getFormulas()[formulaIndex];
                            if(!f->isLiteral() && !f->containsAggregate()){
                                const aspc::ArithmeticRelation* ineq = (aspc::ArithmeticRelation*)f;
                                if(ineq->isBoundedValueAssignment(boundVariables)){
                                    *out << ind << "int "<<ineq->getAssignmentStringRep(boundVariables)<<";\n";
                                    ineq->addVariablesToSet(boundVariables);
                                }else if(ineq->isBoundedRelation(boundVariables)){
                                    *out << ind++ << "if("<<ineq->getStringRep()<<"){\n";
                                    closingPars++;
                                }else {
                                    ineq->print();
                                    std::cout << "  Error:    Unable to evaluate inequality"<<std::endl;
                                    exit(180);
                                }
                            }else if(f->isLiteral()){
                                const aspc::Literal* l = (aspc::Literal*)f;
                                std::string factoryName = lazyBodyPredicates.count(l->getPredicateName())!=0 && lazyHeadPredicates.count(l->getPredicateName())!=0 ? "lazyFactory" : "factory";
                                if(f->isBoundedLiteral(boundVariables)){
                                    *out << ind << "Tuple* boundTuple = "<<factoryName<<".find({";
                                    for(unsigned k = 0; k<l->getAriety(); k++){
                                        if(k>0)
                                            *out << ",";
                                        *out << l->getTermAt(k);
                                    }
                                    *out << "},_"<<l->getPredicateName()<<");\n";
                                    if(l->isNegated()){
                                        *out << ind++ << "if(boundTuple == NULL or boundTuple->isFalse()){\n";
                                        closingPars++;
                                    }else{
                                        *out << ind++ << "if(boundTuple!=NULL && boundTuple->isTrue()){\n";
                                        closingPars++;
                                    }
                                }else{
                                    std::string type = predicateToOrderdedAux.count(l->getPredicateName()) == 0 ? "const std::vector<int>*" : "const IndexedSet*";
                                    std::string toStruct = predicateToOrderdedAux.count(l->getPredicateName()) != 0 ? "Set" : "Vec";

                                    *out << ind << type << " tuples = &p"<<l->getPredicateName()<<"_";
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
                                    *out << ".getValues" << toStruct << "({"<<boundTerms<<"});\n";
                                    if(predicateToOrderdedAux.count(l->getPredicateName())!=0){
                                        *out << ind++ << "for(auto itTrue=tuples->begin(); itTrue != tuples->end(); itTrue++){\n";
                                        closingPars++;
                                            *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(*itTrue);\n";

                                    }else{
                                        *out << ind++ << "for(unsigned i=0; i<tuples->size();i++){\n";
                                        closingPars++;
                                            *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(tuples->at(i));\n";

                                    }
                                        for(unsigned index:unBoundedIndices){
                                            if(boundVariables.count(l->getTermAt(index))==0){
                                                *out << ind << "int "<<l->getTermAt(index)<<" = currentTuple->at("<<index<<");\n";
                                                boundVariables.insert(l->getTermAt(index));
                                            }else{
                                                *out << ind++ << "if(currentTuple->at("<<index<<") == "<<l->getTermAt(index)<<"){\n";
                                                closingPars++;
                                            }
                                        }
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "currentTuple->print();std::cout<<\" Joining\"<<std::endl;\n";
                                        #endif
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
                                        // fAggr->print();
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
                                        std::string factoryName = lazyBodyPredicates.count(l->getPredicateName())!=0 && lazyHeadPredicates.count(l->getPredicateName())!=0 ? "lazyFactory" : "factory";
                                        if(fAggr->isBoundedLiteral(localBoundVariables)){

                                            *out << ind << "Tuple* boundTuple = "<<factoryName<<".find({";
                                            for(unsigned k = 0; k<l->getAriety(); k++){
                                                if(k>0)
                                                    *out << ",";
                                                *out << l->getTermAt(k);
                                            }
                                            *out << "},_"<<l->getPredicateName()<<");\n";
                                            if(l->isNegated()){
                                                *out << ind++ << "if(boundTuple == NULL or boundTuple->isFalse()){\n";
                                                localPars++;
                                            }else{
                                                *out << ind++ << "if(boundTuple != NULL and boundTuple->isTrue()){\n";
                                                localPars++;
                                            }
                                        }else{
                                            std::string type = predicateToOrderdedAux.count(l->getPredicateName())==0 ? "const std::vector<int>*" : "const IndexedSet*";
                                            std::string toStruct = predicateToOrderdedAux.count(l->getPredicateName())==0 ? "Vec" : "Set";
                                            *out << ind << type << " tuples = &p"<<l->getPredicateName()<<"_";
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
                                            *out << ".getValues" << toStruct << "({"<<boundTerms<<"});\n";
                                            if(predicateToOrderdedAux.count(l->getPredicateName())!=0){
                                                *out << ind++ << "for(auto itTrue=tuples->begin(); itTrue != tuples->end()"<<exitCondition<<";itTrue++){\n";
                                                localPars++;
                                                    *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(*itTrue);\n";

                                            }else{
                                                *out << ind++ << "for(unsigned i=0; i<tuples->size()"<<exitCondition<<";i++){\n";
                                                localPars++;
                                                    *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(tuples->at(i));\n";

                                            }
                                                for(unsigned index:unBoundedIndices){
                                                    if(localBoundVariables.count(l->getTermAt(index))==0){
                                                        *out << ind << "int "<<l->getTermAt(index)<<" = currentTuple->at("<<index<<");\n";
                                                        localBoundVariables.insert(l->getTermAt(index));
                                                    }else{
                                                        *out << ind++ << "if(currentTuple->at("<<index<<") == "<<l->getTermAt(index)<<"){\n";
                                                        localPars++;
                                                    }
                                                }
                                                #ifdef TRACE_PROPAGATOR
                                                    *out << ind << "currentTuple->print();std::cout<<\" Joining\"<<std::endl;\n";
                                                #endif
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
                                if(aggrRelation->isBoundedRelation(boundVariables)){
                                    *out << ind++ << "if("<<negated<<"aggregateValue "<<aggrRelation->getCompareTypeAsString()<<" "<<aggrRelation->getGuard().getStringRep()<<plusOne<<"){\n";
                                    closingPars++;
                                }else {
                                    aspc::ArithmeticExpression exp (aggrRelation->getGuard());
                                    if(exp.isSingleTerm()){
                                        *out << ind << "int "<<exp.getTerm1()<<" = aggregateValue;\n";
                                        boundVariables.insert(exp.getTerm1());
                                    }else{
                                        std::string assignedVar = isVariable(exp.getTerm1()) && boundVariables.count(exp.getTerm1())==0 ? exp.getTerm1() : exp.getTerm2();
                                        std::string secondTerm = isVariable(exp.getTerm1()) && boundVariables.count(exp.getTerm1())==0 ? exp.getTerm2() : exp.getTerm1();
                                        std::string op = exp.getOperation() == '-' ? "+" : "-";
                                        *out << ind << "int "<<assignedVar<<" = aggregateValue"<<op<<secondTerm<<";\n";
                                        boundVariables.insert(assignedVar);
                                    }
                                }
                            }
                        }
                        *out << ind << "std::vector<int> head({";
                        for(unsigned k=0; k<head->getAriety(); k++){
                            std::string term = isVariable(head->getTermAt(k)) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                            if(k>0)
                                *out << ",";
                            *out << term;
                        }
                        *out << "});\n";
                        if(lazyBodyPredicates.count(head->getPredicateName())!=0){
                            *out << ind << "Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,_"<<head->getPredicateName()<<");\n";
                            *out << ind << "const auto& insertResult = tupleHead->setStatus(True);\n";
                            *out << ind++ << "if (insertResult.second) {\n";
                                *out << ind << "lazyFactory.removeFromCollisionsList(tupleHead->getId());\n";
                                *out << ind << "insertTrue(insertResult);\n";
                                if(isRecursive){
                                    *out << ind << "stack.push_back(tupleHead->getId());\n";
                                }

                        }else{
                            *out << ind++ << "if(trueHeads.count(head)==0){\n";
                                *out << ind << "trueHeads.insert(head);\n";
                        }
                                *out << ind << "std::cout<<\""<<head->getPredicateName()<<"(\"";
                                for(unsigned k=0;k<head->getAriety();k++){
                                    if(k>0)
                                        *out << "<<\",\"";
                                    *out << "<<ConstantsManager::getInstance().unmapConstant(head["<<k<<"])";
                                }
                                *out << "<<\")\"<<std::endl;\n";
                            *out << --ind << "}\n";

                        while (closingPars>0){
                            *out << --ind << "}\n";
                            closingPars--;
                        }
                        if(lazyBodyPredicates.count(head->getPredicateName())==0)
                            *out << ind << "trueHeads.clear();\n";
                    *out << --ind << "}\n";
                }
                if(isRecursive){
                    *out << ind++ << "while(!stack.empty()){\n";
                        *out << ind << "Tuple* starter = lazyFactory.getTupleFromInternalID(stack.back());\n";
                        *out << ind << "stack.pop_back();\n";
                    for(int ruleId: recursiveRules){
                        aspc::Rule r(lazyRules[ruleId]);
                        const std::vector<const aspc::Formula*>* body = &r.getFormulas();
                        for(unsigned fIndex =0; fIndex<body->size();fIndex++){
                            if(body->at(fIndex)->isPositiveLiteral()){
                                const aspc::Literal* l = (const aspc::Literal*) body->at(fIndex);
                                if(componentPredicateNames.count(l->getPredicateName())!=0){
                                    std::unordered_set<std::string> boundVariables;
                                    unsigned closingPars = printStarter(l,boundVariables);
                                    std::vector<unsigned> orderedFormulas;
                                    r.orderBodyFormulasFromStarter(fIndex,orderedFormulas);
                                    for(unsigned formulaIndex: orderedFormulas){
                                        const aspc::Formula* f = r.getFormulas()[formulaIndex];
                                        if(!f->isLiteral() && !f->containsAggregate()){
                                            // f->print();
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
                                            std::string factoryName = lazyBodyPredicates.count(l->getPredicateName())!=0 && lazyHeadPredicates.count(l->getPredicateName())!=0 ? "lazyFactory" : "factory";

                                            if(f->isBoundedLiteral(boundVariables)){

                                                *out << ind << "Tuple* boundTuple = "<<factoryName<<".find({";
                                                for(unsigned k = 0; k<l->getAriety(); k++){
                                                    if(k>0)
                                                        *out << ",";
                                                    *out << l->getTermAt(k);
                                                }
                                                *out << "},_"<<l->getPredicateName()<<");\n";
                                                if(l->isNegated()){
                                                    *out << ind++ << "if(boundTuple == NULL or boundTuple->isFalse()){\n";
                                                    closingPars++;
                                                }else{
                                                    *out << ind++ << "if(boundTuple!=NULL && boundTuple->isTrue()){\n";
                                                    closingPars++;
                                                }
                                            }else{
                                                std::string type = predicateToOrderdedAux.count(l->getPredicateName()) == 0 ? "const std::vector<int>*" : "const IndexedSet*";
                                                std::string toStruct = predicateToOrderdedAux.count(l->getPredicateName()) != 0 ? "Set" : "Vec";

                                                *out << ind << type << " tuples = &p"<<l->getPredicateName()<<"_";
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
                                                *out << ".getValues" << toStruct << "({"<<boundTerms<<"});\n";
                                                if(predicateToOrderdedAux.count(l->getPredicateName())!=0){
                                                    *out << ind++ << "for(auto itTrue=tuples->begin(); itTrue != tuples->end(); itTrue++){\n";
                                                    closingPars++;
                                                        *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(*itTrue);\n";

                                                }else{
                                                    *out << ind++ << "for(unsigned i=0; i<tuples->size();i++){\n";
                                                    closingPars++;
                                                        *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(tuples->at(i));\n";

                                                }
                                                    for(unsigned index:unBoundedIndices){
                                                        if(boundVariables.count(l->getTermAt(index))==0){
                                                            *out << ind << "int "<<l->getTermAt(index)<<" = currentTuple->at("<<index<<");\n";
                                                            boundVariables.insert(l->getTermAt(index));
                                                        }else{
                                                            *out << ind++ << "if(currentTuple->at("<<index<<") == "<<l->getTermAt(index)<<"){\n";
                                                            closingPars++;
                                                        }
                                                    }
                                                    #ifdef TRACE_PROPAGATOR
                                                        *out << ind << "currentTuple->print();std::cout<<\" Joining\"<<std::endl;\n";
                                                    #endif
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
                                                    // fAggr->print();
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
                                                    std::string factoryName = lazyBodyPredicates.count(l->getPredicateName())!=0 && lazyHeadPredicates.count(l->getPredicateName())!=0 ? "lazyFactory" : "factory";

                                                    if(fAggr->isBoundedLiteral(localBoundVariables)){

                                                        *out << ind << "Tuple* boundTuple = "<<factoryName<<".find({";
                                                        for(unsigned k = 0; k<l->getAriety(); k++){
                                                            if(k>0)
                                                                *out << ",";
                                                            *out << l->getTermAt(k);
                                                        }
                                                        *out << "},_"<<l->getPredicateName()<<");\n";
                                                        if(l->isNegated()){
                                                            *out << ind++ << "if(boundTuple == NULL or boundTuple->isFalse()){\n";
                                                            localPars++;
                                                        }else{
                                                            *out << ind++ << "if(boundTuple != NULL and boundTuple->isTrue()){\n";
                                                            localPars++;
                                                        }
                                                    }else{
                                                        std::string type = predicateToOrderdedAux.count(l->getPredicateName())==0 ? "const std::vector<int>*" : "const IndexedSet*";
                                                        std::string toStruct = predicateToOrderdedAux.count(l->getPredicateName())==0 ? "Vec" : "Set";
                                                        *out << ind << type << " tuples = &p"<<l->getPredicateName()<<"_";
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
                                                        *out << ".getValues" << toStruct << "({"<<boundTerms<<"});\n";
                                                        if(predicateToOrderdedAux.count(l->getPredicateName())!=0){
                                                            *out << ind++ << "for(auto itTrue=tuples->begin(); itTrue != tuples->end()"<<exitCondition<<";itTrue++){\n";
                                                            localPars++;
                                                                *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(*itTrue);\n";

                                                        }else{
                                                            *out << ind++ << "for(unsigned i=0; i<tuples->size()"<<exitCondition<<";i++){\n";
                                                            localPars++;
                                                                *out << ind << "const Tuple* currentTuple = "<<factoryName<<".getTupleFromInternalID(tuples->at(i));\n";

                                                        }
                                                            for(unsigned index:unBoundedIndices){
                                                                if(localBoundVariables.count(l->getTermAt(index))==0){
                                                                    *out << ind << "int "<<l->getTermAt(index)<<" = currentTuple->at("<<index<<");\n";
                                                                    localBoundVariables.insert(l->getTermAt(index));
                                                                }else{
                                                                    *out << ind++ << "if(currentTuple->at("<<index<<") == "<<l->getTermAt(index)<<"){\n";
                                                                    localPars++;
                                                                }
                                                            }
                                                            #ifdef TRACE_PROPAGATOR
                                                                *out << ind << "currentTuple->print();std::cout<<\" Joining\"<<std::endl;\n";
                                                            #endif
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
                                            if(aggrRelation->isBoundedRelation(boundVariables)){
                                                *out << ind++ << "if("<<negated<<"aggregateValue "<<aggrRelation->getCompareTypeAsString()<<" "<<aggrRelation->getGuard().getStringRep()<<plusOne<<"){\n";
                                                closingPars++;
                                            }else {
                                                aspc::ArithmeticExpression exp (aggrRelation->getGuard());
                                                if(exp.isSingleTerm()){
                                                    *out << ind << "int "<<exp.getTerm1()<<" = aggregateValue;\n";
                                                }else{
                                                    std::string assignedVar = isVariable(exp.getTerm1()) && boundVariables.count(exp.getTerm1())==0 ? exp.getTerm1() : exp.getTerm2();
                                                    std::string secondTerm = isVariable(exp.getTerm1()) && boundVariables.count(exp.getTerm1())==0 ? exp.getTerm2() : exp.getTerm1();
                                                    std::string op = exp.getOperation() == '-' ? "+" : "-";
                                                    *out << ind << "int "<<assignedVar<<" = aggregateValue"<<op<<secondTerm<<";\n";
                                                }
                                            }
                                        }
                                    }
                                    *out << ind << "std::vector<int> head({";
                                    const aspc::Atom* head = &r.getHead()[0];
                                    for(unsigned k=0; k<head->getAriety(); k++){
                                        std::string term = isVariable(head->getTermAt(k)) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                        if(k>0)
                                            *out << ",";
                                        *out << term;
                                    }
                                    *out << "});\n";

                                    *out << ind << "Tuple* tupleHead = lazyFactory.addNewInternalTuple(head,_"<<head->getPredicateName()<<");\n";
                                    *out << ind << "const auto& insertResult = tupleHead->setStatus(True);\n";
                                    *out << ind++ << "if (insertResult.second) {\n";
                                        *out << ind << "lazyFactory.removeFromCollisionsList(tupleHead->getId());\n";
                                        *out << ind << "insertTrue(insertResult);\n";
                                        *out << ind << "stack.push_back(tupleHead->getId());\n";

                                        *out << ind << "std::cout<<\""<<head->getPredicateName()<<"(\"";
                                        for(unsigned k=0;k<head->getAriety();k++){
                                            if(k>0)
                                                *out << "<<\",\"";
                                            *out << "<<ConstantsManager::getInstance().unmapConstant(head["<<k<<"])";
                                        }
                                        *out << "<<\")\"<<std::endl;\n";
                                    *out << --ind << "}\n";

                                    while (closingPars>0){
                                        *out << --ind << "}\n";
                                        closingPars--;
                                    }
                                }
                            }
                        }

                    }
                    *out << --ind << "}\n";
                }
                *out << --ind << "}\n";
            }
        }
        *out << ind << "clearUndef();\n";
        *out << ind << "clearTrue();\n";
        *out << ind << "clearFalse();\n";
        *out << ind << "return trueConstraint;\n";
    *out << --ind << "}\n";
    *out << ind++ << "void Executor::unRollToLevel(int decisionLevel){\n";
        //*out << ind << "trace_msg(eagerprop,2,\"Unrolling to level: \"<<decisionLevel << \" \" <<currentDecisionLevel);\n";
        *out << ind << "conflictCount++;\n";

        #ifdef TRACE_CONFLICT
            *out << ind << "std::cout<<\"Unrolling to level: \"<<decisionLevel << \" \" <<currentDecisionLevel<<std::endl;\n";
        #endif
        #ifdef TRACE_PROPAGATOR
        *out << ind << "std::cout<<\"Unrolling to level: \"<<decisionLevel << \" \" <<currentDecisionLevel<<std::endl;\n";
        *out << ind << "std::cout<<\"Conflict count: \"<<conflictCount<<std::endl;\n";
        *out << ind << "std::cout<<\"Unfolding incomplete propagation\"<<std::endl;\n";
        #endif

        *out << ind++ << "for(int literealToProp : remainingPropagatingLiterals){\n";

            *out << ind << "int var = literealToProp > 0 ? literealToProp : -literealToProp;\n";
            *out << ind << "Tuple* literalNotPropagated = factory.getTupleFromWASPID(var);\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Literal not propagate: \"<<literealToProp;\n";
                *out << ind << "literalNotPropagated->print();\n";
            #endif
            *out << ind << "int internalLit = literealToProp > 0 ? literalNotPropagated->getId() : -literalNotPropagated->getId();\n";
            *out << ind++ << "if(literalNotPropagated!=NULL)\n";
                *out << ind-- << "reasonForLiteral[internalLit].get()->clear();\n";
                // *out << ind-- << "reasonForLiteral[internalLit].clear();\n";


        *out << --ind << "}\n";
        *out << ind << "remainingPropagatingLiterals.clear();\n";
        *out << ind++ << "while(currentDecisionLevel > decisionLevel){\n";
            *out << ind << "int size=levelToIntLiterals[currentDecisionLevel].size();\n";
            *out << ind++ << "while(size-- >0){\n";
                *out << ind << "int var = levelToIntLiterals[currentDecisionLevel][size];\n";
                // *out << ind << "levelToIntLiterals[currentDecisionLevel].pop_back();\n";
                *out << ind << "int uVar = var>0 ? var : -var;\n";
                *out << ind << "Tuple* tuple = factory.getTupleFromInternalID(uVar);\n";
                // *out << ind << "levelToIntLiterals[currentDecisionLevel].pop_back();\n";
                *out << ind << "reasonForLiteral[var].get()->clear();\n";
                 #ifdef TRACE_CONFLICT
                    *out << ind << "std:: cout <<\"Clearing reason\" << var << \" \";printTuple(tuple);\n";
                    *out << ind << "if(reasonForLiteral[var].get() == NULL) std::cout << \"NULL reason\"<<std::endl; else std::cout << \"ReasonFound\"<<reasonForLiteral[var].get()->size()<<std::endl;\n";
                #endif
                
                *out << ind << "const auto& insertResult = tuple->setStatus(Undef);\n";
                *out << ind++ << "if (insertResult.second) {\n";
                    *out << ind << "factory.removeFromCollisionsList(uVar);\n";
                    *out << ind << "insertUndef(insertResult);\n";
                *out << --ind << "}\n";
                for(unsigned ruleId=0; ruleId < program.getRules().size(); ruleId++){
                    const aspc::Rule* rule = &program.getRules()[ruleId];
                    if(!rule->isConstraint() && rule->containsAggregate()){
                        const aspc::Atom* aggrId = &rule->getHead()[0];
                        const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rule->getArithmeticRelationsWithAggregate()[0];
                        const aspc::Literal* aggrSetLit = &aggregateRelation->getAggregate().getAggregateLiterals()[0];
                        unsigned sumVar = 0;
                        if(!aggregateRelation->getAggregate().isSum())
                            continue;
                        if(!builder->isAggrSetPredicate(aggrSetLit->getPredicateName())){
                            std::string var = aggregateRelation->getAggregate().getAggregateVariables()[0];
                            for(unsigned i = 0; i < aggrSetLit->getAriety(); i++){
                                if(aggrSetLit->getTermAt(i)==var){
                                    sumVar=i;
                                    break;
                                }
                            }
                        }
                        *out << ind++ << "if(tuple->getPredicateName() == _"<<aggrSetLit->getPredicateName()<<"){\n";
                            if(aggrId->getAriety() == 0){
                                *out << ind << "int itAggrId = factory.find({},_"<<aggrId->getPredicateName()<<")->getId();\n";
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
                                        *out << ind << "const std::vector<int>* aggrIds = &"<<sign<<mapName<<".getValuesVec({"<<terms<<"});\n";
                                        *out << ind++ << "for(unsigned i=0;i<aggrIds->size();i++){\n";
                                            *out << ind << "int itAggrId = aggrIds->at(i);\n";
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
        *out << ind << "falseLits.clear();\n";
        #ifdef TRACE_PROPAGATOR
        *out << ind << "std::cout <<\"Unroll Completed\"<<std::endl;\n";
        #endif
        //*out << ind << "trace_msg(eagerprop,2,\"Unrolling ended\");\n";

    *out << --ind << "}\n";
    // ---------------------- executeProgramOnFacts() --------------------------------------//
    if (mode == LAZY_MODE) {
        *out << ind << "void Executor::executeProgramOnFacts(const std::vector<int> & facts) {}\n";
        *out << ind++ << "void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {\n";
    } else {
        *out << ind << "void Executor::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {}\n";
        *out << ind++ << "void Executor::executeProgramOnFacts(const std::vector<int> & facts,std::vector<int>& propagatedLiterals,bool fromPropagator) {\n";
    }
    //data structure init
    //*out << ind << "trace_msg(eagerprop,2,\"Computing propagation\");\n";

    if (mode == LAZY_MODE) {
        *out << ind << "init();\n";
        *out << ind << "clear();\n";
    } else {
        // mode == EAGER_MODE

        //facts[0] is the decision level for eager mode (-1 is facts level)
        *out << ind << "currentDecisionLevel=solver->getCurrentDecisionLevel();\n";
        #ifdef TRACE_PROPAGATOR
            *out << ind << "int decisionLevel = facts[0];\n";
            *out << ind << "std::cout<<\"Execute program on facts: decision level \"<<decisionLevel<<std::endl;\n";
            *out << ind << "std::cout<<\"Current Decision Level: \"<<currentDecisionLevel<<std::endl;\n";
        #endif
        #ifdef EAGER_DEBUG
                *out << ind << "std::cout<<\"Execute program on facts: decision level \"<<decisionLevel<<std::endl;\n";
        #endif
        *out << ind << "clearPropagations();\n";
    }


    //  *out << ind << "std::cout<<\"facts reading\"<<std::endl;\n";

    //  feed facts
    //  *out << ind << "std::cout<<\"facts\\n\";\n";
    if (mode == LAZY_MODE) {
        *out << ind++ << "for(unsigned i=0;i<facts.size();i++) {\n";
        *out << ind << "onLiteralTrue(facts[i]);\n";
        *out << --ind << "}\n";
    } else {
        // mode == EAGER_MODE
        #ifdef TRACE_PROPAGATOR
            *out << ind << "std::cout<<\"OnFacts \"<<facts.size()<<std::endl;\n";
            *out << ind << "std::cout<<\"facts read\"<<std::endl;\n";
        #endif
        #ifdef TRACE_PROPAGATION
            *out << ind << "if(fromPropagator) std::cout << \"Propagating unfounded set\"<<std::endl;\n";
        #endif
        *out << ind << "std::vector<int> propagationStack;\n";
        *out << ind++ << "for(unsigned i=1;i<facts.size();i++) {\n";
            *out << ind << "int factVar = facts[i]>0 ? facts[i] : -facts[i];\n";
            *out << ind << "int minus = facts[i]<0 ? -1 : 1;\n";
            *out << ind++ << "if(!fromPropagator){\n";
                *out << ind << "onLiteralTrue(facts[i]);\n";
                *out << ind << "propagationStack.push_back(minus*(int)factory.getTupleFromWASPID(factVar)->getId());\n";
                *out << ind << "remainingPropagatingLiterals.erase(facts[i]);\n";
            *out << --ind << "}else{\n";
            ind++;
                //WARNING:  Is assumed that facts comes from unfouded propagator and then they are atoms to propagate as false
                *out << ind << "propUndefined(factory.getTupleFromInternalID(factVar),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                // *out << ind << "propagationStack.push_back(facts[i]);\n";
            *out << --ind << "}\n";

        *out << --ind << "}\n";
        #ifdef TRACE_PROPAGATION
            *out << ind << "if(fromPropagator) std::cout << \"End unfounded propagation\"<<std::endl;\n";
        #endif
        

    }
    // *out << ind++ << "if(!factory.isGenerated()) {\n";
    //     *out << ind << "undefLiteralsReceived();\n";
    // *out << --ind <<"}\n";
    
    // *out << ind << "/*\n";

    if (mode == LAZY_MODE) {
    } else {
        *out << ind++ << "if(!factory.isGenerated()) {\n";
            *out << ind++ << "undefLiteralsReceived();\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"level -1\"<<std::endl;\n";
            #endif

            std::unordered_set<unsigned> compiledRuleIndices;
            while(compiledRuleIndices.size()<program.getRulesSize()){
                const aspc::Rule* rule = NULL;
                int ruleId=0;
                int selectedRuleId = 0;
                for (const aspc::Rule& r : program.getRules()) {
                    if(compiledRuleIndices.count(ruleId)==0){
                        bool noInternalLiteral = true;
                        for(const aspc::Literal& l : r.getBodyLiterals()){
                            if(builder->isAuxPredicate(l.getPredicateName()) || headPreds.count(l.getPredicateName())!=0){
                                noInternalLiteral=false;
                                break;
                            }
                        }
                        if(noInternalLiteral){
                            rule=&r;
                            selectedRuleId=ruleId;
                            break;
                        }else if(r.isConstraint()){
                            rule=&r;
                            selectedRuleId=ruleId;
                        }else if(rule==NULL){
                            rule=&r;
                            selectedRuleId=ruleId;
                        }
                    }
                    ruleId++;
                }
                compiledRuleIndices.insert(selectedRuleId);
                compileEagerRule(*rule,false);
            }
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"end level -1\"<<std::endl;\n";
            #endif

        *out << --ind << "}//close decision level == -1\n";

        // std::cout<<"Gen -1"<<std::endl;
        #ifdef TRACE_PROPAGATOR
            *out << ind << "std::cout<<\"PossibleSumMap size: \"<<possibleSum.size()<<std::endl;\n";
            *out << ind << "std::cout<<\"ActualSumMap size: \"<<actualSum.size()<<std::endl;\n";
        #endif
        *out << ind << "std::vector<int> propagated;\n";
        *out << ind++ << "while(!propagationStack.empty()){\n";
            *out << ind << "int startVar = propagationStack.back();\n";
            *out << ind << "propagated.push_back(startVar);\n";
            *out << ind << "int uStartVar = startVar<0 ? -startVar : startVar;\n";
            *out << ind << "Tuple starter (*factory.getTupleFromInternalID(uStartVar));\n";
            *out << ind << "std::string minus = startVar < 0 ? \"not \" : \"\";\n";

            #ifdef TRACE_CONFLICT
                *out << ind << "std::cout<<\"Starter \";printTuple(&starter);\n";
            #endif

            //*out << ind << "trace_msg(eagerprop,5,minus << starter.toString() << \" as Starter\");\n";
            *out << ind << "propagationStack.pop_back();\n";
            for(const aspc::Rule& r: program.getRules()){
                compileEagerRule(r,true);
            }
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Processed\"<<std::endl;\n";
            #endif

        *out << --ind << "}\n";


    }
    *out << ind << "if(conflictCount > minConflict && propagatedLiterals.size() >= heapSize){/*std::cout<<\"sort heap\"<<std::endl;*/ std::sort_heap(propagatedLiterals.begin(),propagatedLiterals.begin()+heapSize,propComparison);}\n";
#ifdef TRACE_PROP_GEN
    *out << ind << "std::cout<<\"Out execute program on facts\"<<std::endl;\n";
#endif
    // *out << ind << "*/\n";
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
            int BITSETSIZE=keyIndexes.size()*CHAR_BIT*sizeof(int);
            *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";

            //TODO remove duplication
            *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapVariableName << "({";
            for (unsigned k = 0; k < keyIndexes.size(); k++) {
                if (k > 0) {
                    *out << ",";
                }
                *out << keyIndexes[k];
            }
            *out << "});\n";


            *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapVariableName << "({";
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
                    int BITSETSIZE=keyIndexes.size()*CHAR_BIT*sizeof(int);
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapVariableName << "({";
                    for (unsigned k = 0; k < keyIndexes.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << keyIndexes[k];
                    }
                    *out << "});\n";

                    //TODO remove duplication
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapVariableName << "({";
                    for (unsigned k = 0; k < keyIndexes.size(); k++) {
                        if (k > 0) {
                            *out << ",";
                        }
                        *out << keyIndexes[k];
                    }
                    *out << "});\n";


                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapVariableName << "({";
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
                }

                for(std::string aggrVar : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateVariables()){
                    for(unsigned j=0; j<aggregate->getAriety();j++){
                        if(aggrVar == aggregate->getTermAt(j)){
                            aggrVarToAggrSetIndices[aggregate->getPredicateName()].push_back(j);
                            break;
                        }
                    }
                }
                std::string mapName = aggregate->getPredicateName()+"_";
                if (!declaredMaps.count(mapName) && r.getArithmeticRelationsWithAggregate()[0].getAggregate().isSum()){
                    int BITSETSIZE=0;
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapName << "({});\n";
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapName << "({});\n";
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapName << "({});\n";
                    predicateToAuxiliaryMaps[aggregate->getPredicateName()].insert(mapName);
                    predicateToUndefAuxiliaryMaps[aggregate->getPredicateName()].insert(mapName);
                    predicateToFalseAuxiliaryMaps[aggregate->getPredicateName()].insert(mapName);
                    declaredMaps.insert(mapName);
                }
                mapName = aggrId->getPredicateName()+"_";
                if (!declaredMaps.count(mapName)){
                    int BITSETSIZE=0;
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapName << "({});\n";
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapName << "({});\n";
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapName << "({});\n";
                    predicateToAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                    predicateToUndefAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                    predicateToFalseAuxiliaryMaps[aggrId->getPredicateName()].insert(mapName);
                    declaredMaps.insert(mapName);
                }

                // if(domBody!=NULL && domBody->getAriety() != sharedVarAggrIDToBodyIndices[aggrId->getPredicateName()].size()){
                if(domBody!=NULL){
                    std::string indices="";
                    int lenKey=0;
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
                            lenKey++;
                            indices+=std::to_string(k);
                        }
                    }
                    sumAggrSetPredicateToAggrId[aggregate->getPredicateName()].insert({mapName,aggrId->getPredicateName()});
                    if (!declaredMaps.count(mapName)){
                        int BITSETSIZE=lenKey*CHAR_BIT*sizeof(int);
                        *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapName << "({"<<indices<<"});\n";
                        *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapName << "({"<<indices<<"});\n";
                        *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapName << "({"<<indices<<"});\n";
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
                int lenKey=0;
                for(unsigned index : sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                    mapName+=std::to_string(index)+"_";
                    if(indices!="")
                        indices+=",";
                    indices+=std::to_string(index);
                    lenKey++;
                }
                if (!declaredMaps.count(mapName)){
                    int BITSETSIZE=lenKey*CHAR_BIT*sizeof(int);
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapName << "({"<<indices<<"});\n";
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << mapName << "({"<<indices<<"});\n";
                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << mapName << "({"<<indices<<"});\n";
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

            // TODO useless structure ----- review carefully
            std::string mapNameBody=lit->getPredicateName()+"_";
            if(declaringMaps.find(mapNameBody)==declaringMaps.end()){
                declaringMaps[mapNameBody]={indices,lit->getAriety()};
                mapNames[mapNameBody]=lit->getPredicateName();
            }

            std::unordered_set<std::string> bodyVars;
            lit->addVariablesToSet(bodyVars);

            // TODO useless structure ----- review carefully
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
                int BITSETSIZE=declareMap.second.first.size()*CHAR_BIT*sizeof(int);
                *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << declareMap.first << "({";
                for (unsigned k = 0; k < declareMap.second.first.size(); k++) {
                    if (k > 0) {
                        *out << ",";
                    }
                    *out << declareMap.second.first[k];
                }
                *out << "});\n";

                //TODO remove duplication
                *out << ind << "AuxMap<"<<BITSETSIZE<<"> u" << declareMap.first << "({";
                for (unsigned k = 0; k < declareMap.second.first.size(); k++) {
                    if (k > 0) {
                        *out << ",";
                    }
                    *out << declareMap.second.first[k];
                }
                *out << "});\n";


                //TODO remove duplication
                *out << ind << "AuxMap<"<<BITSETSIZE<<"> f" << declareMap.first << "({";
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
                    *out << ind << "Tuple negativeTuple({"<<terms<<"},_"<<lit->getPredicateName()<<");\n";

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
                    *out << ind << "Tuple positiveTuple({"<<terms<<"},_"<<lit->getPredicateName()<<");\n";
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

                *out << ind << "const std::vector<int>* tuples = &p"<<lit->getPredicateName()<<"_";
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
                        //ConstantsManager
                    }
                }
                *out << "});\n";
                *out << ind << "const std::vector<int>* tuplesU = &EMPTY_TUPLES;\n";
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
                            //ConstantsManager
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
            std::string term= lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
            boundTerms+=term;
        }
    }
    if(lit->isBoundedLiteral(boundVariables)){
        if(lit->isNegated()){
            *out << ind << "Tuple negativeTuple({"<<boundTerms<<"},_"<<lit->getPredicateName()<<");\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = factory.find(negativeTuple);\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<" == NULL)\n";
                *out << ind-- << "tuple"<<currentLitIndex<<" = &negativeTuple;\n";
            *out << ind++ << "else{\n";
                //tuple in factory
                *out << ind++ << "if(tuple"<<currentLitIndex<<"->isTrue())\n";
                    *out << ind-- << "tuple"<<currentLitIndex<<" = NULL;\n";
                *out << ind++ << "else if(tuple"<<currentLitIndex<<"->isUndef()){\n";
                    *out << ind++ << "if(tupleU == NULL){\n";
                        *out << ind << "tupleU = tuple"<<currentLitIndex<<";\n";
                        *out << ind << "tupleUNegated=true;\n";
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind++ << "if(tupleU->getPredicateName() != _"<<lit->getPredicateName()<<" || !tupleUNegated || !(*tupleU == *tuple"<<currentLitIndex<<"))\n";
                            *out << --ind << "tuple"<<currentLitIndex<<"=NULL;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        }else{
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = factory.find({"<<boundTerms<<"},_"<<lit->getPredicateName()<<");\n";
            *out << ind++ << "if(tuple"<<currentLitIndex<<"!=NULL){\n";
                *out << ind++ << "if(tuple"<<currentLitIndex<<"->isFalse())\n";
                    *out << --ind << "tuple"<<currentLitIndex<<"=NULL;\n";
                *out << ind++ << "else if(tuple"<<currentLitIndex<<"->isUndef()){\n";
                    *out << ind++ << "if(tupleU == NULL){\n";
                        *out << ind << "tupleU = tuple"<<currentLitIndex<<";\n";
                        *out << ind << "tupleUNegated=false;\n";
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind++ << "if(tupleU->getPredicateName() != _"<<lit->getPredicateName()<<" || tupleUNegated || !(*tupleU == *tuple"<<currentLitIndex<<"))\n";
                            *out << --ind << "tuple"<<currentLitIndex<<"=NULL;\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            *out << --ind << "}\n";
        }
        *out << ind++ << "if(tuple"<<currentLitIndex<<"!=NULL){\n";
        pars++;
    }else{
        std::string type = predicateToOrderdedAux.count(lit->getPredicateName())!=0 ? "const IndexedSet*":"const std::vector<int>*";
        std::string toStruct = predicateToOrderdedAux.count(lit->getPredicateName())!=0 ? "Set":"Vec";
        std::string toEmptyStruct = predicateToOrderdedAux.count(lit->getPredicateName())!=0 ? "_SET":"_VEC";

        bool isSet = printGetValues(lit->getPredicateName(),boundIndices,boundTerms,"p","tuples");
        *out << ind << type << " tuplesU = &EMPTY_TUPLES"<<toEmptyStruct<<";\n";
        *out << ind << "std::vector<const Tuple*> undeRepeated;\n";
        *out << ind++ << "if(tupleU == NULL)\n";
            *out << ind-- << "tuplesU = &u"<<lit->getPredicateName()<<"_";
            for(unsigned k: boundIndices){
                *out << k << "_";
            }
            *out << ".getValues"<<toStruct<<"({"<<boundTerms<<"});\n";
        *out << ind++ << "else if(tupleU->getPredicateName() == _"<<lit->getPredicateName()<<" && !tupleUNegated)\n";
            *out << ind-- << "undeRepeated.push_back(tupleU);\n";

        if(isSet){
            *out << ind << "auto itTrue = tuples->begin();\n";
            *out << ind << "auto itUndef = tuplesU->begin();\n";
        }
        *out << ind++ << "for(unsigned i = 0; i<tuples->size()+tuplesU->size()+undeRepeated.size(); i++){\n";
        pars++;

            // *out << ind << "unsigned currentSize = tuples->size()+tuplesU->size()+undeRepeated.size();\n";
            // *out << ind++ << "if(totalSize>currentSize){\n";
            //     *out << ind << "i-=totalSize-currentSize;\n";
            //     *out << ind << "totalSize=currentSize;\n";
            // *out << --ind << "}\n";
            *out << ind++ << "if(tuplesU!=&EMPTY_TUPLES"<<toEmptyStruct<<")\n";
                *out << ind-- << "tupleU = NULL;\n";
            *out << ind << "const Tuple* tuple"<<currentLitIndex<<" = NULL;\n";
            if(isSet){
                *out << ind++ << "if(i<tuples->size()){\n";
                    *out << ind << "tuple"<<currentLitIndex<<" = factory.getTupleFromInternalID(*itTrue);\n";
                    *out << ind-- << "itTrue++;\n";
                *out << ind++ << "}else if(i<tuples->size()+tuplesU->size()){\n";
                    *out << ind << "tupleU = tuple"<<currentLitIndex<<" = factory.getTupleFromInternalID(*itUndef);\n";
                    *out << ind << "tupleUNegated=false;\n";
                    *out << ind << "itUndef++;\n";

            }else{
                *out << ind++ << "if(i<tuples->size())\n";
                    *out << ind-- << "tuple"<<currentLitIndex<<" = factory.getTupleFromInternalID(tuples->at(i));\n";
                *out << ind++ << "else if(i<tuples->size()+tuplesU->size()){\n";
                    *out << ind << "tupleU = tuple"<<currentLitIndex<<" = factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
                    *out << ind << "tupleUNegated=false;\n";
            }
            *out << --ind << "}else if(!undeRepeated.empty()){\n";
            ind++;
                std::string conditions="";
                for(unsigned k: boundIndices){
                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                    if(conditions!="")
                        conditions+=" && ";
                    conditions+="tupleU->at("+std::to_string(k)+") == "+term;
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

            *out << ind++ << "if(starter.getPredicateName() == _"<<aggrIdAtom->getPredicateName()<<"){\n";
            #ifdef TRACE_PROP_GEN
            *out << ind << "std::cout<<\"Prop rule with aggr\"<<std::endl;\n";
            #endif
            std::unordered_set<std::string> boundVariables;
            unsigned pars=0;
            for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")";
                if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                    *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = starter["<<i<<"];\n";
                    boundVariables.insert(aggrIdAtom->getTermAt(i));
                }else{
                    *out << ind++ << "if("<<term<<" = starter["<<i<<"]){\n";
                    pars++;
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
                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                    *out << ind << "const IndexedSet* tuples = &p"<<mapName<<".getValuesSet(sharedVar);\n";
                    *out << ind << "const IndexedSet* tuplesU = &u"<<mapName<<".getValuesSet(sharedVar);\n";
                }else{
                    *out << ind << "const std::vector<int>* tuples = &p"<<mapName<<".getValuesVec(sharedVar);\n";
                    *out << ind << "const std::vector<int>* tuplesU = &u"<<mapName<<".getValuesVec(sharedVar);\n";
                }
                // string bodyTerms = "";
                // if(bodyPred!=NULL){
                //     for(unsigned i = 0; i<bodyPred->getAriety();i++){
                //         if(bodyTerms!="")
                //             bodyTerms+=",";
                //         bodyTerms+=bodyPred->getTermAt(i);
                //     }
                // }
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"Actual Sum: \"<<actualSum[uStartVar]<<std::endl;\n";
                #endif
                *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                *out << ind++ << "if(startVar < 0){\n";

                    if(aggregateRelation->getAggregate().isSum()){
                        *out << ind << "int& actSum = actualSum[uStartVar];\n";
                        *out << ind++ << "if(actSum>="<<guard<<"){\n";
                    }
                    else
                       *out << ind++ << "if(tuples->size()>="<<guard<<"){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflitct on aggregate start from aggrId false "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(currentDecisionLevel > 0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto i =tuples->begin(); i != tuples->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                            }else{
                                *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                    *out << ind << "int it = tuples->at(i);\n";

                            }
                                *out << ind << "shared_reason.get()->insert(it);\n";
                            *out << --ind << "}\n";
                            *out << ind << "reasonForLiteral[-startVar]=shared_reason;\n";

                            *out << ind << "handleConflict(-startVar, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";
                    if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "if(!tuplesU->empty() && currentDecisionLevel>0){\n";
                                *out << ind++ << "for(auto i = tuples->begin(); i != tuples->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                                    *out << ind << "shared_reason.get()->insert(it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "while(!tuplesU->empty()){\n";
                                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());\n";
                                *out << ind++ << "if(actSum >= "<<guard<<"-currentTuple->at(0)){\n";
                                    *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                        *out << ind << "int itProp =currentTuple->getId();\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}else break;\n";
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
                            *out << ind++ << "if(!tuplesU->empty() && currentDecisionLevel >0){\n";
                                *out << ind++ << "for(auto i = tuples->begin(); i != tuples->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                                    *out << ind << "shared_reason.get()->insert(it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "for(auto itUndef = tuplesU->begin(); itUndef != tuplesU->end(); itUndef++){\n";
                                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*itUndef);\n";
                                *out << ind++ << "if(actSum >= "<<guard<<"-currentTuple->at("<<varIndex<<")){\n";
                                    *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                        *out << ind << "int itProp = currentTuple->getId();\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}else break;\n";
                            *out << --ind << "}\n";
                        }
                    *out << --ind << "}\n";
                    }else{
                        *out << --ind << "}else if(tuples->size() == "<<guard<<" -1){\n";
                        ind++;
                        *out << ind++ << "if(currentDecisionLevel > 0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto i =tuples->begin(); i != tuples->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                            }else{
                                *out << ind++ << "for(unsigned i =0; i< tuples->size(); i++){\n";
                                    *out << ind << "int it = tuples->at(i);\n";
                            }
                                *out << ind << "shared_reason.get()->insert(it);\n";
                            *out << --ind << "}\n";
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                        *out << --ind << "}\n";
                            if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                                *out << ind++ << "while(!tuplesU->empty()){\n";
                                    *out << ind++ << "if(currentDecisionLevel > 0){\n";

                                    if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0)
                                        *out << ind << "int itProp = *tuplesU->begin();\n";
                                    else
                                        *out << ind << "int itProp = tuplesU->at(0);\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0)
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(*tuplesU->begin()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    else
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}\n";
                            }else{
                                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                    *out << ind++ << "for(auto i = tuplesU->begin(); i != tuplesU->end(); i++){\n";
                                        *out << ind << "int itProp = *i;\n";
                                }else{
                                    *out << ind++ << "for(unsigned i =0; i<tuplesU->size(); i++){\n";
                                        *out << ind << "int itProp = tuplesU->at(i);\n";
                                }
                                *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                    *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                                    *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                        *out << ind-- << "itReason.first->second=shared_reason;\n";
                                *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0)
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(*i),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                else
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}\n";
                            }

                        *out << --ind << "}\n";
                    }

                *out << --ind << "}else{\n";
                ind++;
                    if(aggregateRelation->getAggregate().isSum()){
                        *out << ind << "int& actSum = actualSum[uStartVar];\n";
                        *out << ind << "int& posSum = possibleSum[uStartVar];\n";
                        *out << ind++ << "if(actSum+posSum < "<<guard<<"){\n";
                    }else
                        *out << ind++ << "if(tuples->size()+tuplesU->size() < "<<guard<<"){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflitct on aggregate starting from aggrId true "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(currentDecisionLevel > 0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind << "const IndexedSet* tuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                *out << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";

                            }else{
                                *out << ind << "const std::vector<int>* tuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                    *out << ind << "int it = tuplesF->at(i);\n";

                            }
                                *out << ind << "shared_reason.get()->insert(-it);\n";
                            *out << --ind << "}\n";
                            *out << ind << "reasonForLiteral[-startVar]=shared_reason;\n";
                            *out << ind << "handleConflict(-startVar, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";
                    if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "while(!tuplesU->empty()){\n";
                                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());\n";
                                *out << ind++ << "if(actSum < "<<guard<<"-posSum+currentTuple->at(0)){\n";
                                    *out << ind << "int itProp = *tuplesU->begin();\n";

                                    *out << ind++ << "if(shared_reason.get()->empty() && currentDecisionLevel>0){\n";
                                        *out << ind << "const IndexedSet* tuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                        *out << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                            *out << ind << "int it = *i;\n";
                                            *out << ind << "shared_reason.get()->insert(-it);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "shared_reason.get()->insert(startVar);\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    // reason contains aggr_id and all aggr_set false
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}else break;\n";
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
                            *out << ind++ << "for(auto index=tuplesU->begin(); index != tuplesU->end(); index++){\n";
                                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*index);\n";
                                // *out << ind++ << "if(actSum+posSum-currentTuple->at("<<varIndex<<") < "<<guard<<"){\n";
                                *out << ind++ << "if(actSum < "<<guard<<"-posSum+currentTuple->at("<<varIndex<<")){\n";
                                    *out << ind << "int itProp = currentTuple->getId();\n";
                                    *out << ind++ << "if(shared_reason.get()->empty() && currentDecisionLevel>0){\n";
                                        *out << ind << "const IndexedSet* tuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                        *out << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                            *out << ind << "int it = *i;\n";
                                            *out << ind << "shared_reason.get()->insert(-it);\n";
                                        *out << --ind << "}\n";
                                        *out << ind << "shared_reason.get()->insert(startVar);\n";
                                    *out << --ind << "}\n";
                                    *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    // reason contains aggr_id and all aggr_set false
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}else break;\n";
                            *out << --ind << "}\n";
                        }
                    *out << --ind << "}\n";
                    }else{
                        *out << --ind << "}else if(tuples->size() + tuplesU->size() == "<<guard<<"){\n";
                        ind++;
                        if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                            *out << ind++ << "if(tuplesU->size() > 0 && currentDecisionLevel>0){\n";
                                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                    *out << ind << "const IndexedSet* tuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                    *out << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                        *out << ind << "int it = *i;\n";

                                }else{
                                    *out << ind << "const std::vector<int>* tuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                        *out << ind << "int it = tuplesF->at(i);\n";

                                }
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << --ind << "}\n";

                            *out << ind++ << "while(tuplesU->size()>0){\n";
                                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0)
                                    *out << ind << "int itProp = *tuplesU->begin();\n";
                                else
                                    *out << ind << "int itProp = tuplesU->at(0);\n";
                                *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                    *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                // reason contains aggr_id and all aggr_set false
                                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0)
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(*tuplesU->begin()),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                else
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                            *out << --ind << "}\n";
                        }else{
                            *out << ind++ << "if(!tuplesU->empty() && currentDecisionLevel>0){\n";
                                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                    *out << ind << "const IndexedSet* tuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                    *out << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                        *out << ind << "int it = *i;\n";
                                }else{
                                    *out << ind << "const std::vector<int>* tuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                                    *out << ind++ << "for(unsigned i = 0; i < tuplesF->size(); i++){\n";
                                        *out << ind << "int it = tuplesF->at(i);\n";
                                }

                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << --ind << "}\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto index=tuplesU->begin();index != tuplesU->end();index++){\n";
                                    *out << ind << "int itProp = *index;\n";
                            }else{
                                *out << ind++ << "for(unsigned index=0;index<tuplesU->size();index++){\n";
                                    *out << ind << "int itProp = tuplesU->at(index);\n";
                            }
                            *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                // *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){\n";
                                //     *out << ind << "reasonForLiteral[itProp]=shared_reason;\n";
                                // *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                // reason contains aggr_id and all aggr_set false
                                *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                            *out << --ind << "}\n";
                        }
                        *out << --ind << "}\n";
                    }
                *out << --ind << "}\n";
                while (pars>0){
                    *out << --ind << "}\n";
                    pars--;
                }

            *out << --ind << "}//close aggr id starter\n";
            // std::cout<<"Compiled starter aggr id"<<std::endl;

        }
    }
    {
        if(fromStarter)
            *out << ind++ << "if(starter.getPredicateName() == _"<<aggrSetPred->getPredicateName()<<"){\n";
        else *out << ind++ << "{\n";
        #ifdef TRACE_PROPAGATOR
            *out << ind << "std::cout<<\"Propagation start from aggr_set\"<<std::endl;\n";
        #endif
        std::string mapName=aggrSetPred->getPredicateName()+"_";
        for(unsigned i : sharedVarAggrIDToAggrSetIndices[aggrIdAtom->getPredicateName()]){
            mapName+=std::to_string(i)+"_";
        }
        std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
        std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;

            *out << ind << "const std::vector<int>* tuples = &p"<<aggrIdAtom->getPredicateName()<<"_.getValuesVec({});\n";
            *out << ind << "const std::vector<int>* tuplesU = &u"<<aggrIdAtom->getPredicateName()<<"_.getValuesVec({});\n";
            *out << ind << "const std::vector<int>* tuplesF = &f"<<aggrIdAtom->getPredicateName()<<"_.getValuesVec({});\n";
            //OPTIMIZATION Add if starter.isNegated
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Prop for true head\"<<std::endl;\n";
                *out << ind << "std::cout<<\"AggrId true size: \"<<tuples->size()<<std::endl;\n";
                *out << ind << "std::cout<<\"AggrId undef size: \"<<tuplesU->size()<<std::endl;\n";
                *out << ind << "std::cout<<\"AggrId false size: \"<<tuplesF->size()<<std::endl;\n";
            #endif
            *out << ind++ << "for(unsigned i = 0; i<tuples->size(); i++){\n";
            {
                unsigned pars=0;
                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(tuples->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                        std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")";
                        if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                            *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                            boundVariables.insert(aggrIdAtom->getTermAt(i));
                        }else{
                            *out << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                            pars++;
                        }
                }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";

                        *out << "currentTuple->at("<<i<<")";
                    }
                }
                *out << "});\n";
                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                    *out << ind << "const IndexedSet* joinTuples = &p"<<mapName<<".getValuesSet(sharedVar);\n";
                    *out << ind << "const IndexedSet* joinTuplesU = &u"<<mapName<<".getValuesSet(sharedVar);\n";
                }else{
                    *out << ind << "const std::vector<int>* joinTuples = &p"<<mapName<<".getValuesVec(sharedVar);\n";
                    *out << ind << "const std::vector<int>* joinTuplesU = &u"<<mapName<<".getValuesVec(sharedVar);\n";
                }

                *out << ind << "int aggrIdIt=tuples->at(i);\n";
                *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                if(aggregateRelation->getAggregate().isSum()){
                    *out << ind << "int& actSum = actualSum[aggrIdIt];\n";
                    *out << ind << "int& posSum = possibleSum[aggrIdIt];\n";
                    // *out << ind++ << "if(actSum+posSum < "<<guard<<"){\n";
                    *out << ind++ << "if(actSum < "<<guard<<"-posSum){\n";
                }else
                    *out << ind++ << "if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"Conflitct on aggregate starting from true aggr id "<<r.getRuleId()<<"\"<<std::endl;\n";
                    #endif
                    if(fromStarter){
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            *out << ind << "int itProp = tuples->at(i);\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind << "const IndexedSet* joinTuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                *out << ind++ << "for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){\n";
                                    *out << ind << "int it = *j;\n";
                            }else{
                                *out << ind << "const std::vector<int>* joinTuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                                *out << ind++ << "for(unsigned j = 0; j < joinTuplesF->size(); j++){\n";
                                    *out << ind << "int it = joinTuplesF->at(j);\n";
                            }
                                *out << ind << "shared_reason.get()->insert(-it);\n";
                            *out << --ind << "}\n";
                            *out << ind << "reasonForLiteral[-itProp]=shared_reason;\n";
                            *out << ind << "handleConflict(-itProp, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";
                    }else{
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict at level -1\"<<std::endl;\n";
                        #endif
                        *out << ind << "propagatedLiterals.push_back(1);\n";
                    }
                if(aggregateRelation->getAggregate().isSum()){
                    *out << --ind << "}else{\n";
                    ind++;
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        *out << ind++ << "while(!joinTuplesU->empty()){\n";
                            *out << ind << "const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*joinTuplesU->begin());\n";
                            *out << ind << "if(actSum >= "<<guard<<"-posSum+currentJoinTuple->at(0)) {break;}\n";
                            *out << ind << "int itProp = *joinTuplesU->begin();\n";
                            *out << ind++ << "if(shared_reason.get()->empty() && currentDecisionLevel>0){\n";
                                *out << ind << "const IndexedSet* joinTuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                *out << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                                    *out << ind << "shared_reason.get()->insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i);\n";
                                *out << ind << "shared_reason.get()->insert(itAggrId);\n";

                            *out << --ind << "}\n";
                            *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                            // reason contains aggr_id and all aggr_set false
                            *out << ind << "propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
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
                        *out << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                            *out << ind << "const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*index);\n";
                            // *out << ind << "if(actSum+posSum-currentJoinTuple->at("<<varIndex<<") >= "<<guard<<") {index++; continue;}\n";
                            *out << ind << "if(actSum >= "<<guard<<"-posSum+currentJoinTuple->at("<<varIndex<<")) {break;}\n";
                            *out << ind << "int itProp = *index;\n";
                            *out << ind++ << "if(shared_reason.get()->empty() && currentDecisionLevel>0){\n";
                                *out << ind << "const IndexedSet* joinTuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                *out << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                                    *out << ind << "shared_reason.get()->insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i);\n";
                                *out << ind << "shared_reason.get()->insert(itAggrId);\n";
                            *out << --ind << "}\n";
                            *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                            // reason contains body, aggr_id and all aggr_set false
                            *out << ind << "propUndefined(currentJoinTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }
                    *out << --ind << "}\n";
                }else{

                    *out << --ind << "}else if(joinTuples->size() + joinTuplesU->size() == "<<guard<<"){\n";
                    ind++;
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        *out << ind++ << "if(!joinTuplesU->empty() && currentDecisionLevel >0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind << "const IndexedSet* joinTuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                *out << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                            }else{
                                *out << ind << "const std::vector<int>* joinTuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                    *out << ind << "int it = joinTuplesF->at(i);\n";
                            }
                                    *out << ind << "shared_reason.get()->insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i);\n";
                                *out << ind << "shared_reason.get()->insert(itAggrId);\n";
                        *out << --ind << "}\n";
                        *out << ind++ << "while(joinTuplesU->size()>0){\n";
                        if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                            *out << ind << "int itProp = *joinTuplesU->begin();\n";
                        }else{
                            *out << ind << "int itProp = joinTuplesU->at(0);\n";
                        }
                            *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                            // reason contains body, aggr_id and all aggr_set false
                            *out << ind << "propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }else{
                        *out << ind++ << "if(!joinTuplesU->empty() && currentDecisionLevel>0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind << "const IndexedSet* joinTuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                                *out << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                            }else{
                                *out << ind << "const std::vector<int>* joinTuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                                *out << ind++ << "for(unsigned i = 0; i < joinTuplesF->size(); i++){\n";
                                    *out << ind << "int it = joinTuplesF->at(i);\n";
                            }
                                    *out << ind << "shared_reason.get()->insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int itAggrId = tuples->at(i);\n";
                                *out << ind << "shared_reason.get()->insert(itAggrId);\n";
                        *out << --ind << "}\n";
                        if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                            *out << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                                *out << ind << "int itProp = *index;\n";
                        }else{
                            *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size(); index++){\n";
                                *out << ind << "int itProp = joinTuplesU->at(index);\n";
                        }
                            *out << ind++ << "if(currentDecisionLevel > 0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                            // reason contains body, aggr_id and all aggr_set false
                            *out << ind << "propUndefined(factory.getTupleFromInternalID(joinTuplesU->at(index)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }

                    *out << --ind << "}\n";
                }
                while(pars>0){
                    pars--;
                    *out << --ind << "}\n";
                }
            }
            *out << --ind << "}//close true for\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout << \"exit true for loop\"<<std::endl;\n";
                *out << ind << "std::cout<<\"Prop for false head\"<<std::endl;\n";
            #endif
            //OPTIMIZATION Add if !starter.isNegated

            *out << ind++ << "for(unsigned i = 0; i<tuplesF->size(); i++){\n";
            {
                unsigned pars=0;
                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesF->at(i));\n";

                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")";
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }else{
                        *out << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                        pars++;
                    }
                }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred != NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";

                        *out << "currentTuple->at("<<i<<")";
                    }
                }
                *out << "});\n";
                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                    *out << ind << "const IndexedSet* joinTuples = &p"<<mapName<<".getValuesSet(sharedVar);\n";
                    *out << ind << "const IndexedSet* joinTuplesU = &u"<<mapName<<".getValuesSet(sharedVar);\n";
                }else{
                    *out << ind << "const std::vector<int>* joinTuples = &p"<<mapName<<".getValuesVec(sharedVar);\n";
                    *out << ind << "const std::vector<int>* joinTuplesU = &u"<<mapName<<".getValuesVec(sharedVar);\n";
                }
                *out << ind << "int aggrIdIt=tuplesF->at(i);\n";
                *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"ActualSum: \"<<actualSum[aggrIdIt]<<std::endl;\n";
                #endif
                if(aggregateRelation->getAggregate().isSum()){
                    *out << ind << "int& actSum = actualSum[aggrIdIt];\n";
                    *out << ind++ << "if(actSum >= "<<guard<<"){\n";
                }else
                    *out << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"Conflitct on aggregate starting from false aggr id "<<r.getRuleId()<<"\"<<actualSum[aggrIdIt]<<std::endl;\n";
                    #endif
                    if(fromStarter){
                        *out << ind++ << "if(currentDecisionLevel > 0){\n";
                            *out << ind << "int itProp = tuplesF->at(i);\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto j =joinTuples->begin(); j != joinTuples->end(); j++){\n";
                                    *out << ind << "int it = *j;\n";
                            }else{
                                *out << ind++ << "for(unsigned j =0; j< joinTuples->size(); j++){\n";
                                    *out << ind << "int it = joinTuples->at(j);\n";
                            }
                                *out << ind << "shared_reason.get()->insert(it);\n";
                            *out << --ind << "}\n";
                            *out << ind << "reasonForLiteral[itProp]=shared_reason;\n";

                            *out << ind << "handleConflict(itProp, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";
                    }else{
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict at level -1\"<<std::endl;\n";
                        #endif
                        *out << ind << "propagatedLiterals.push_back(1);\n";
                    }
                if(aggregateRelation->getAggregate().isSum())
                    *out << --ind << "}else{\n";
                else
                    *out << -- ind << "}else if(joinTuples->size() == "<<guard<<" -1){\n";
                ind++;
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout << \"aggr propagation\"<<std::endl;\n";
                    #endif
                    if(builder->isAggrSetPredicate(aggrSetPred->getPredicateName())){
                        if(aggregateRelation->getAggregate().isSum()){
                            *out << ind++ << "while(!joinTuplesU->empty()){\n";
                                *out << ind << "int itProp = *joinTuplesU->begin();\n";
                                *out << ind << "const Tuple* currentJoinTuple = factory.getTupleFromInternalID(itProp);\n";
                                // *out << ind++ << "if(actSum+currentJoinTuple->at(0) >= "<<guard<<"){\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "if(currentJoinTuple==NULL)std::cout<<\"NULL tuple to prop\"<<std::endl; else std::cout<<\"check tuple to prop\"<<std::endl;\n";
                                #endif
                                *out << ind << "if(actSum < "<<guard<<"-currentJoinTuple->at(0))break;\n";


                        }else{
                            *out << ind++ << "while(!joinTuplesU->empty()){\n";
                                *out << ind << "int itProp = joinTuplesU->at(0);\n";
                                *out << ind << "const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(0));\n";

                        }

                            // *out << ind++ << "if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){\n";
                            *out << ind++ << "if(shared_reason.get()->empty() && currentDecisionLevel>0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto i =joinTuples->begin(); i != joinTuples->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                            }else{
                                *out << ind++ << "for(unsigned i =0; i< joinTuples->size(); i++){\n";
                                    *out << ind << "int it = joinTuples->at(i);\n";
                            }
                                    *out << ind << "shared_reason.get()->insert(it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int it = tuplesF->at(i);\n";
                                *out << ind << "shared_reason.get()->insert(-it);\n";
                            *out << --ind << "}\n";

                            *out << ind++ << "if(currentDecisionLevel>0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                            *out << ind << "propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }else{
                        if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){

                            *out << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                                *out << ind << "const Tuple* currentJoinTuple = factory.getTupleFromInternalID(*index);\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout << \"aggr propagation first\"<<std::endl;\n";
                                #endif
                                *out << ind << "int itProp = *index;\n";
                        }else{
                            *out << ind++ << "for(unsigned index=0; index<joinTuplesU->size(); index++){\n";
                                *out << ind << "const Tuple* currentJoinTuple = factory.getTupleFromInternalID(joinTuplesU->at(index));\n";
                                *out << ind << "int itProp = joinTuplesU->at(index);\n";
                        }

                        if(aggregateRelation->getAggregate().isSum()){
                            std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
                            unsigned varIndex = 0;
                            for(unsigned var = 0; var<aggrSetPred->getAriety(); var++){
                                if(firstAggrVar == aggrSetPred->getTermAt(var)){
                                    varIndex = var;
                                    break;
                                }
                            }
                            // *out << ind++ << "if(actSum+currentJoinTuple->at("<<varIndex<<") >= "<<guard<<"){\n";
                            *out << ind++ << "if(actSum < "<<guard<<"-currentJoinTuple->at("<<varIndex<<"))break;\n";
                        }
                            // *out << ind++ << "if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout << \"aggr propagation\"<<std::endl;\n";
                            #endif
                            *out << ind++ << "if(shared_reason.get()->empty() && currentDecisionLevel>0){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                            }else{
                                *out << ind++ << "for(unsigned i =0; i< joinTuples->size(); i++){\n";
                                    *out << ind << "int it = joinTuples->at(i);\n";
                            }
                                    *out << ind << "shared_reason.get()->insert(it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "int it = tuplesF->at(i);\n";
                                *out << ind << "shared_reason.get()->insert(-it);\n";
                            *out << --ind << "}\n";
                            //     *out << ind << "reasonForLiteral[-itProp]=shared_reason;\n";

                            // *out << --ind << "}\n";
                            *out << ind++ << "if(currentDecisionLevel>0){\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                            *out << ind << "propUndefined(currentJoinTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }
                *out << --ind << "}\n";
                while (pars>0){
                    *out << --ind << "}\n";
                    pars--;
                }

            }
            *out << --ind << "}//close false for\n";

            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout << \"exit false for loop\"<<std::endl;\n";
            #endif
            *out << ind++ << "for(unsigned i = 0; i<tuplesU->size();){\n";
            {
                unsigned pars=0;
                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")";
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        *out << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }else{
                        *out << ind++ << "if("<<term<<" = currentTuple->at("<<i<<")){\n";
                        pars++;
                    }
                }
                *out << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices[aggrIdAtom->getPredicateName()]){
                        if(first)
                            first=false;
                        else *out <<",";
                        *out << "currentTuple->at("<<i<<")";
                    }
                }
                *out << "});\n";
                if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                    *out << ind << "const IndexedSet* joinTuples = &p"<<mapName<<".getValuesSet(sharedVar);\n";
                    *out << ind << "const IndexedSet* joinTuplesU = &u"<<mapName<<".getValuesSet(sharedVar);\n";
                }else{
                    *out << ind << "const std::vector<int>* joinTuples = &p"<<mapName<<".getValuesVec(sharedVar);\n";
                    *out << ind << "const std::vector<int>* joinTuplesU = &u"<<mapName<<".getValuesVec(sharedVar);\n";
                }
                *out << ind << "int aggrIdIt=tuplesU->at(i);\n";
                *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                if(aggregateRelation->getAggregate().isSum()){
                    *out << ind << "int& actSum = actualSum[aggrIdIt];\n";
                    *out << ind << "int& posSum = possibleSum[aggrIdIt];\n";
                    *out << ind++ << "if(actSum >= "<<guard<<"){\n";
                }else
                    *out << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";
                        *out << ind++ << "if(currentDecisionLevel>0){\n";

                            *out << ind << "int itProp = tuplesU->at(i);\n";
                            // *out << ind++ << "if(reasonForLiteral.count(itProp) == 0 || reasonForLiteral[itProp].get()==NULL || reasonForLiteral[itProp].get()->empty()){\n";
                            if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                                *out << ind++ << "for(auto j = joinTuples->begin(); j != joinTuples->end(); j++){\n";
                                    *out << ind << "int it = *j;\n";
                            }else{
                                *out << ind++ << "for(unsigned j = 0; j < joinTuples->size(); j++){\n";
                                    *out << ind << "int it = joinTuples->at(j);\n";
                            }
                                    *out << ind << "shared_reason.get()->insert(it);\n";
                                *out << --ind << "}\n";
                            //     *out << ind << "reasonForLiteral[itProp]=shared_reason;\n";

                            // *out << --ind << "}\n";
                            *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                            *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                *out << ind-- << "itReason.first->second=shared_reason;\n";
                        *out << --ind << "}\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                if(aggregateRelation->getAggregate().isSum()){
                    // *out << --ind << "}else if(actSum + posSum < "<<guard<<"){\n";
                    *out << --ind << "}else if(actSum < "<<guard<<" - posSum){\n";
                }else
                    *out << --ind << "}else if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                ind++;
                    *out << ind << "int itProp = tuplesU->at(i);\n";
                    // *out << ind++ << "if(reasonForLiteral.count(-itProp) == 0 || reasonForLiteral[-itProp].get()==NULL || reasonForLiteral[-itProp].get()->empty()){\n";
                    *out << ind++ << "if(currentDecisionLevel>0){\n";

                        if(predicateToOrderdedAux.count(aggrSetPred->getPredicateName())!=0){
                            *out << ind << "const IndexedSet* joinTuplesF = &f"<<mapName<<".getValuesSet(sharedVar);\n";
                            *out << ind++ << "for(auto j = joinTuplesF->begin(); j != joinTuplesF->end(); j++){\n";
                                *out << ind << "int it = *j;\n";
                        }else{
                            *out << ind << "const std::vector<int>* joinTuplesF = &f"<<mapName<<".getValuesVec(sharedVar);\n";
                            *out << ind++ << "for(unsigned j = 0; j < joinTuplesF->size(); j++){\n";
                                *out << ind << "int it = joinTuplesF->at(j);\n";
                        }
                                *out << ind << "shared_reason.get()->insert(-it);\n";
                            *out << --ind << "}\n";
                        //     *out << ind << "reasonForLiteral[-itProp]=shared_reason;\n";

                        // *out << --ind << "}\n";
                        *out << ind << "auto itReason = reasonForLiteral.emplace(-itProp,shared_reason);\n";
                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                    *out << --ind << "}\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"Propagating from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                    #endif
                    *out << ind << "propUndefined(currentTuple,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                *out << --ind << "}else{\n";
                ind++;
                    *out << ind << "i++;\n";
                *out << --ind << "}\n";
                while(pars > 0){
                    *out << --ind << "}\n";
                    pars--;
                }
            }
            *out << --ind << "}//close undef for\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout << \"exit aggr set if\"<<std::endl;\n";
            #endif
        *out << --ind << "}//close aggr set starter\n";
    }
}
void CompilationManager::printAtomVariables(const aspc::Atom* atom,std::string tupleName,string pointer,std::unordered_set<std::string>& boundVariables,unsigned& closingPars){
    for(unsigned k=0; k<atom->getAriety(); k++){
        if(atom->isVariableTermAt(k) && boundVariables.count(atom->getTermAt(k))==0){
            *out << ind << "int "<<atom->getTermAt(k)<<" = "<<tupleName<<pointer<<"at("<<k<<");\n";
            boundVariables.insert(atom->getTermAt(k));
        }else{
            std::string term = atom->isVariableTermAt(k) || isInteger(atom->getTermAt(k)) ? atom->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+atom->getTermAt(k)+"\")";
            *out << ind++ << "if("<<tupleName<<pointer<<"at("<<k<<") == "<<term<<"){\n";
            closingPars++;
        }
    }
}
void printRulePropagationStartingFromTrueHead(){

}
bool CompilationManager::printGetValues(std::string predicateName,std::vector<unsigned> boundIndices,std::string boundTerms,std::string mapPrefix,std::string name){
    std::string collisionListType = predicateToOrderdedAux.count(predicateName)!=0 ? "const IndexedSet*" : "const std::vector<int>*";
    std::string toStruct = predicateToOrderdedAux.count(predicateName)!=0 ? "Set" : "Vec";

    *out << ind << collisionListType << " " << name << " = &" << mapPrefix << predicateName << "_";
    for(unsigned index : boundIndices){
        *out << index << "_";
    }
    *out << ".getValues" << toStruct << "({" << boundTerms << "});\n";
    return toStruct == "Set";
}
void CompilationManager::findExitRuleForComponent(std::vector<int> component,AspCore2ProgramBuilder* builder, std::vector<int>& exitRules, std::vector<int>& rules,unordered_set<std::string>& stackPredicates){

    aspc::EagerProgram* rewrittenProgram = &builder->getRewrittenProgram();
    std::unordered_set<int> componentSet;
    for(int predId : component){
        componentSet.insert(predId);
    }

    unsigned ruleId = 0;
    for(const aspc::Rule& r : rewrittenProgram->getRules()){
        if(!r.isConstraint()){
            auto headId = rewrittenProgram->getGeneratorPredicateId(r.getHead()[0].getPredicateName());
            if(componentSet.count(headId)!=0){
                //rule with internal literal in head
                bool isExitRule=true;
                for(const aspc::Literal& l : r.getBodyLiterals()){
                    auto bodyId = rewrittenProgram->getGeneratorPredicateId(l.getPredicateName());
                    if(componentSet.count(bodyId)!=0 && l.isPositiveLiteral()){
                        stackPredicates.insert(l.getPredicateName());
                        isExitRule=false;
                    }

                }
                if(isExitRule){
                    exitRules.push_back(ruleId);
                }else{
                    rules.push_back(ruleId);
                }
            }
        }
        ruleId++;
    }

}
unsigned CompilationManager::printStarter(const aspc::Literal* body,std::unordered_set<std::string>& boundTerms){
    *out << ind++ << "if(starter->getPredicateName() == _"<<body->getPredicateName()<<"){\n";
    unsigned closingPars=1;
    for(unsigned k=0; k<body->getAriety(); k++){
        std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
        if(body->isVariableTermAt(k) && boundTerms.count(term)==0){
            *out << ind << "int "<<term<<" = starter->at("<<k<<");\n";
            boundTerms.insert(term);
        }else{
            *out << ind++ << "if(starter->at("<<k<<") == "<<term<<"){\n";
            closingPars++;
        }
    }
    return closingPars;
}
void CompilationManager::buildUnfoundedInit(const std::vector<int>& component,int componentId, AspCore2ProgramBuilder* builder){
    //init unfoundedSetForComponent
    aspc::EagerProgram* rewrittenProgram = &builder->getRewrittenProgram();
    std::vector<int> exitRules;
    std::vector<int> rules;
    std::unordered_set<std::string> stackPredicates;
    // findExitRuleForComponent(component,builder,exitRules,rules,stackPredicates);
    {
        std::unordered_set<int> componentSet;
        for(int predId : component){
            componentSet.insert(predId);
        }

        unsigned ruleId = 0;
        for(const aspc::Rule& r : rewrittenProgram->getRules()){
            if(!r.isConstraint()){
                auto headId = rewrittenProgram->getPredicateId(r.getHead()[0].getPredicateName());
                if(componentSet.count(headId)!=0){
                    //rule with internal literal in head
                    bool isExitRule=true;
                    for(const aspc::Literal& l : r.getBodyLiterals()){
                        auto bodyId = rewrittenProgram->getPredicateId(l.getPredicateName());
                        if(componentSet.count(bodyId)!=0 && l.isPositiveLiteral()){
                            stackPredicates.insert(l.getPredicateName());
                            isExitRule=false;
                        }

                    }
                    if(isExitRule){
                        exitRules.push_back(ruleId);
                    }else{
                        rules.push_back(ruleId);
                    }
                }
            }
            ruleId++;
        }
    }

    for(int ruleId : rules){
        auto subprogram = builder->getSubProgramsForRule(ruleId);
        for(const aspc::Rule& subRule : subprogram){
            const aspc::Atom* head = NULL;
            if(subRule.isConstraint()){
                const aspc::Literal* lit = &subRule.getBodyLiterals().back();
                if(lit->isNegated() && (stackPredicates.count(lit->getPredicateName())!=0 || builder->isAuxPredicate(lit->getPredicateName()))){
                    head=&lit->getAtom();
                }
            }else{
                head = &subRule.getHead()[0];
            }
            if(head!=NULL){
                *out << ind++ << "{\n";
                    // *out << ind << "predsToUnfoundedSet[&_"<<head->getPredicateName()<<"]=&unfoundedSetForComponent"<<componentId<<";\n";
                    *out << ind << "const std::vector<int>* tuples = &p"<<head->getPredicateName()<<"_.getValuesVec({});\n";
                    *out << ind << "const std::vector<int>* tuplesU = &u"<<head->getPredicateName()<<"_.getValuesVec({});\n";
                    *out << ind++ << "for(unsigned i=0; i<tuples->size()+tuplesU->size(); i++){\n";
                        // *out << ind << "if(i<tuples->size()) unfoundedSetForComponent"<<componentId<<".insert(tuples->at(i));\n";
                        // *out << ind << "else unfoundedSetForComponent"<<componentId<<".insert(tuplesU->at(i-tuples->size()));\n";
                        *out << ind << "int lit = i<tuples->size() ? tuples->at(i) : tuplesU->at(i-tuples->size());\n";
                        *out << ind << "int& founded = foundnessFactory[lit];\n";
                        *out << ind << "if(founded == 0) {founded=-1;unfoundedSetForComponent"<<componentId<<".push_back(lit);}\n";
                        
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            }
        }
    }
    *out << ind << "supportedLiterals"<<componentId<<".resize(factory.size());\n";
}
void CompilationManager::buildGeneratorForRecursiveComponent(std::vector<int> component,AspCore2ProgramBuilder* builder){
    aspc::EagerProgram* rewrittenProgram = &builder->getRewrittenProgram();
    std::unordered_set<std::string> sumAggrSetPredicates;
    for(const aspc::Rule& r : rewrittenProgram->getRules()){
        if(r.containsAggregate()) {
            const aspc::Aggregate* aggr = &r.getArithmeticRelationsWithAggregate()[0].getAggregate();
            if(aggr->isSum()){
                sumAggrSetPredicates.insert(aggr->getAggregateLiterals()[0].getPredicateName());
            }
        }
    }
    std::vector<int> exitRules;
    std::vector<int> rules;
    std::unordered_set<std::string> stackPredicates;
    *out << ind << "//---------------------------------Recursive Component---------------------------------\n";
    findExitRuleForComponent(component,builder,exitRules,rules,stackPredicates);
    *out << ind++ << "{\n";
        *out << ind << "std::vector<int> generationStack;\n";

    for(aspc::Atom fact : builder->getFacts()){
        bool found =false;
        int id = rewrittenProgram->getGeneratorPredicateId(fact.getPredicateName());
        for(int predId : component){
            if(predId==id)
                found=true;
        }
        if(!found) continue;
        *out << ind++ << "{\n";
            *out << ind << "Tuple* fact = factory.addNewInternalTuple({";
            for(unsigned k=0; k<fact.getAriety(); k++){
                if(fact.isVariableTermAt(k)){std::cout << "Error:   Unsafe fact "<<std::endl;exit(180);}
                std::string term = isInteger(fact.getTermAt(k)) ? fact.getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+fact.getTermAt(k)+"\")";
                if(k>0)
                    *out << ",";
                *out << term;
            }
            *out << "},_"<<fact.getPredicateName()<<");\n";
            *out << ind << "const auto& insertResult = fact->setStatus(True);\n";
            *out << ind++ << "if(insertResult.second){\n";
                *out << ind << "factory.removeFromCollisionsList(fact->getId());\n";
                *out << ind << "insertTrue(insertResult);\n";
                *out << ind << "eagerFacts.insert(fact->getId());\n";
                *out << ind << "generationStack.push_back(fact->getId());\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
    }
    for(int ruleId : exitRules){
        bool ruleWithAggId = false;
        for(const aspc::Literal& l : rewrittenProgram->getRule(ruleId).getBodyLiterals()){
            if(builder->isAggregateIdPredicate(l.getPredicateName())){
                ruleWithAggId=true;
                break;
            }
        }
        // sourceProgram->getRules()[ruleId].print();
        *out << ind++ << "{\n";
            unsigned closingPars =0;
            if(!ruleWithAggId)
                closingPars = buildGeneratorForExiteRule(rewrittenProgram->getRule(ruleId),builder->getSubProgramsForRule(ruleId),ruleId,sumAggrSetPredicates,true);
            else
                // rule with aggId in body
                closingPars = buildGeneratorForRuleWithAggId(rewrittenProgram->getRule(ruleId),builder,builder->getSubProgramsForRule(ruleId),ruleId,sumAggrSetPredicates,true);
            while (closingPars>0){
                *out << --ind << "}\n";
                closingPars--;
            }
        *out << --ind << "}\n";
    }
    std::vector<int> rulesAggrSetBody;
    std::vector<int> standardRules;
    for(int ruleId : rules){
        bool found=false;
        const aspc::Rule* r = &rewrittenProgram->getRule(ruleId);
        for(const aspc::Literal& l : r->getBodyLiterals()){
            if(builder->isValuePredicate(l.getPredicateName()) || builder->isDomainPredicate(l.getPredicateName())){
                rulesAggrSetBody.push_back(ruleId);
                found=true;
                break;
            }
        }
        if(!found) standardRules.push_back(ruleId);
    }
    const aspc::Literal* auxVal=NULL;
    const aspc::Literal* domain=NULL;
    for(int ruleId : rulesAggrSetBody){
        bool found=false;
        const aspc::Rule* r = &rewrittenProgram->getRule(ruleId);
        for(const aspc::Literal& l : r->getBodyLiterals()){
            if(auxVal == NULL && builder->isValuePredicate(l.getPredicateName())){
                auxVal=&l;
            }else if(domain==NULL && builder->isDomainPredicate(l.getPredicateName())){
                domain=&l;
            }
        }
    }
    if(!rulesAggrSetBody.empty()){
        *out << ind << "std::map<std::vector<int>,std::vector<int>> possibleSumValues;\n";
        *out << ind << "std::map<std::vector<int>,std::unordered_set<int>> possibleSumValuesSet;\n";
        *out << ind << "Tuple* auxVal = factory.addNewInternalTuple({0},_"<<auxVal->getPredicateName()<<");\n";
        *out << ind << "const auto& insertResult = auxVal->setStatus(True);\n";
        *out << ind++ << "if(insertResult.second){\n";
            *out << ind << "factory.removeFromCollisionsList(auxVal->getId());\n";
            *out << ind << "insertTrue(insertResult);\n";
            *out << ind << "generationStack.push_back(auxVal->getId());\n";
        *out << --ind << "}\n";
        *out << ind << "bool init=true;\n";
    }
    *out << ind++ << "while(!generationStack.empty()){\n";
        *out << ind << "Tuple* starter = factory.getTupleFromInternalID(generationStack.back());\n";
        *out << ind << "generationStack.pop_back();\n";

    if(!rulesAggrSetBody.empty()){
        if(auxVal !=NULL){
            int rId = builder->getRuleForAuxVal(auxVal->getPredicateName());
            aspc::Rule ruleWithAggregate(rewrittenProgram->getRule(rId));
            const aspc::Literal* body=NULL;
            const aspc::Literal* aggregateSet = &ruleWithAggregate.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0];
            const aspc::Aggregate* aggr = &ruleWithAggregate.getArithmeticRelationsWithAggregate()[0].getAggregate();
            if(ruleWithAggregate.getBodyLiterals().size() > 0){
                body = &ruleWithAggregate.getBodyLiterals()[0];
            }

            std::unordered_set<std::string> sharedVariables;
            std::vector<int> sharedVariablesIndex;
            aggregateSet->addVariablesToSet(sharedVariables);
            for(int k=0; body!=NULL && k<body->getAriety(); k++){
                if(body->isVariableTermAt(k) && sharedVariables.count(body->getTermAt(k))!=0){
                    sharedVariablesIndex.push_back(k);
                }
            }

            int ruleWithAuxVal =0;
            int ruleWithDomBody =0;
            for(int ruleId : rulesAggrSetBody){
                const aspc::Rule* r = &rewrittenProgram->getRule(ruleId);
                for(const aspc::Literal& l : r->getBodyLiterals()){
                    if(builder->isDomainPredicate(l.getPredicateName())){
                        ruleWithDomBody=ruleId;
                    }else if(builder->isValuePredicate(l.getPredicateName())){
                        ruleWithAuxVal=ruleId;
                    }
                }
            }

            {//starting from AuxVal
                std::vector<aspc::Rule> subProgram = builder->getSubProgramsForRule(ruleWithAuxVal);
                aspc::Rule* joinRule = &subProgram.back();
                if(joinRule->isConstraint()){
                    unsigned forumulaIndex=0;
                    for(const aspc::Formula* f: joinRule->getFormulas()){
                        if(f->isPositiveLiteral()){
                            const aspc::Literal* l = (const aspc::Literal*)f;
                            // if(l->getPredicateName()==auxVal->getPredicateName()){
                            std::unordered_set<std::string> boundTerms;
                            unsigned closingPars = printStarter(l,boundTerms);
                            const aspc::Atom* currentlySaving = &joinRule->getBodyLiterals().back().getAtom();
                            closingPars+=buildGeneratorForConstraint(joinRule,"saving"+std::to_string(subProgram.size()-1),sumAggrSetPredicates,forumulaIndex,boundTerms);
                            // joinRule->print();
                            // std::cout<<"Sub rules"<<std::endl;
                            for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                                const aspc::Rule* currentSubRule = &subProgram[subRuleId];
                                // currentSubRule->print();
                                const aspc::Atom* head =NULL;
                                if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                                    // std::cout << "previouslySaved"<<std::endl;
                                    if(currentSubRule->isConstraint()){
                                        // std::cout << "constraint"<<std::endl;
                                        if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                                            // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                                            head = &currentSubRule->getBodyLiterals()[1].getAtom();
                                        }
                                    }else{

                                        head = &currentSubRule->getHead()[0];
                                    }
                                }

                                if(head == NULL){
                                    std::cout<<"Error compiling subprogram for rule ";rewrittenProgram->getRule(ruleWithAuxVal).print();
                                    std::exit(180);
                                }else{
                                    closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                                    currentlySaving=head;

                                }
                            }
                            *out << ind << "generationStack.push_back(saving0->getId());\n";
                            std::string sharedVars="";
                            for(unsigned k=0; k<body->getAriety(); k++){
                                std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                if(body->isVariableTermAt(k) && sharedVariables.count(term)!=0){
                                    if(sharedVars!="")
                                        sharedVars+=",";
                                    sharedVars+=term;
                                }
                            }
                            // *out << ind++ << "if(init){\n";
                                // *out << ind << "std::vector<int> sharedVars({"<<sharedVars<<"});\n";
                                // *out << ind++ << "if(possibleSumValuesSet[sharedVars].count(0)==0){\n";
                                //     *out << ind << "possibleSumValues[sharedVars].push_back(0);\n";
                                //     *out << ind << "possibleSumValuesSet[sharedVars].insert(0);\n";
                                // *out << --ind << "}\n";
                            // *out << --ind << "}\n";

                            #ifdef TRACE_PROPAGATOR
                            *out << ind << "saving0->print();\n";
                            #endif
                            while (closingPars>0){
                                // if(closingPars == 1){
                                //     *out << ind << "init =false;\n";
                                // }
                                *out << --ind << "}\n";
                                closingPars--;

                            }
                            // }
                        }
                        forumulaIndex++;
                    }

                }else{
                    std::unordered_set<std::string> boundTerms;
                    const aspc::Literal* body = &joinRule->getBodyLiterals()[0];
                    unsigned closingPars = printStarter(body,boundTerms);
                    const aspc::Atom* currentlySaving = &joinRule->getHead()[0];
                    closingPars+=buildLiteralSaving(&joinRule->getHead()[0],"saving"+std::to_string(subProgram.size()-1));
                    // joinRule->print();
                    // std::cout<<"Sub rules"<<std::endl;
                    for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                        const aspc::Rule* currentSubRule = &subProgram[subRuleId];
                        // currentSubRule->print();
                        const aspc::Atom* head =NULL;
                        if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                            // std::cout << "previouslySaved"<<std::endl;
                            if(currentSubRule->isConstraint()){
                                // std::cout << "constraint"<<std::endl;
                                if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                                    // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                                    head = &currentSubRule->getBodyLiterals()[1].getAtom();
                                }
                            }else{

                                head = &currentSubRule->getHead()[0];
                            }
                        }

                        if(head == NULL){
                            std::cout<<"Error compiling subprogram for rule ";rewrittenProgram->getRule(ruleWithAuxVal).print();
                            std::exit(180);
                        }else{
                            closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                            currentlySaving=head;
                        }
                    }
                    *out << ind << "generationStack.push_back(saving0->getId());\n";

                    std::string sharedVars="";
                        for(unsigned k=0; k<body->getAriety(); k++){
                            std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                            if(body->isVariableTermAt(k) && sharedVariables.count(term)!=0){
                                if(sharedVars!="")
                                    sharedVars+=",";
                                sharedVars+=term;
                            }
                        }
                        // *out << ind++ << "if(init){\n";
                        //     *out << ind << "std::vector<int> sharedVars({"<<sharedVars<<"});\n";
                        //     *out << ind++ << "if(possibleSumValuesSet[sharedVars].count(starter->at(0))==0){\n";
                        //         *out << ind << "possibleSumValues[sharedVars].push_back(starter->at(0));\n";
                        //         *out << ind << "possibleSumValuesSet[sharedVars].insert(starter->at(0));\n";
                        //     *out << --ind << "}\n";
                        // *out << --ind << "}\n";
                    while (closingPars>0){
                        // if(closingPars == 1){
                        //     *out << ind << "init =false;\n";
                        // }
                        *out << --ind << "}\n";
                        closingPars--;

                    }
                }
            }
            {//starting from body
                *out << ind++ << "if(starter->getPredicateName() == _"<<body->getPredicateName()<<"){\n";
                    *out << ind << "Tuple* dom = factory.addNewInternalTuple({";
                    for(int k=0;k<body->getAriety();k++){
                        if(k>0)
                            *out << ",";
                        *out << "starter->at("<<k<<")";
                    }
                    *out << "},_"<<domain->getPredicateName()<<");\n";
                    *out << ind << "const auto& insertResult = dom->setStatus(True);\n";
                    *out << ind++ << "if(insertResult.second){\n";
                        *out << ind << "factory.removeFromCollisionsList(dom->getId());\n";
                        *out << ind << "insertTrue(insertResult);\n";
                        *out << ind << "generationStack.push_back(dom->getId());\n";
                    *out << --ind << "}\n";
                *out << --ind << "}\n";
            }
            {//starting from dom
                std::vector<aspc::Rule> subProgram = builder->getSubProgramsForRule(ruleWithDomBody);
                aspc::Rule* joinRule = &subProgram.back();
                if(joinRule->isConstraint()){
                    unsigned forumulaIndex=0;
                    for(const aspc::Formula* f: joinRule->getFormulas()){
                        if(f->isPositiveLiteral()){
                            const aspc::Literal* l = (const aspc::Literal*)f;
                            // if(l->getPredicateName()==domain->getPredicateName()){
                            std::unordered_set<std::string> boundTerms;
                            unsigned closingPars = printStarter(l,boundTerms);
                            const aspc::Atom* currentlySaving = &joinRule->getBodyLiterals().back().getAtom();
                            closingPars+=buildGeneratorForConstraint(joinRule,"saving"+std::to_string(subProgram.size()-1),sumAggrSetPredicates,forumulaIndex,boundTerms);
                            // joinRule->print();
                            // std::cout<<"Sub rules"<<std::endl;
                            for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                                const aspc::Rule* currentSubRule = &subProgram[subRuleId];
                                // currentSubRule->print();
                                const aspc::Atom* head =NULL;
                                if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                                    // std::cout << "previouslySaved"<<std::endl;
                                    if(currentSubRule->isConstraint()){
                                        // std::cout << "constraint"<<std::endl;
                                        if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                                            // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                                            head = &currentSubRule->getBodyLiterals()[1].getAtom();
                                        }
                                    }else{

                                        head = &currentSubRule->getHead()[0];
                                    }
                                }

                                if(head == NULL){
                                    std::cout<<"Error compiling subprogram for rule ";rewrittenProgram->getRule(ruleWithAuxVal).print();
                                    std::exit(180);
                                }else{
                                    closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                                    currentlySaving=head;

                                }
                            }
                            std::string sharedVars="";
                            for(unsigned k:sharedVariablesIndex){
                                std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                                if(sharedVars!="")
                                    sharedVars+=",";
                                sharedVars+=term;
                            }
                            *out << ind << "std::vector<int> sharedVars({"<<sharedVars<<"});\n";
                            std::string sumTerm = aggr->isSum() ? aggr->getAggregateVariables()[0] : "1";
                            *out << ind << "if(possibleSumValues.count(sharedVars)==0) possibleSumValues[sharedVars].push_back(0);\n";
                            *out << ind << "unsigned actualSumCount=possibleSumValues[sharedVars].size();\n";
                            *out << ind++ << "for(unsigned k = 0; k < actualSumCount; k++){\n";
                            closingPars++;
                                *out << ind << "int currentSum = possibleSumValues[sharedVars][k]+"<<sumTerm<<";\n";
                                *out << ind++ << "if(possibleSumValuesSet[sharedVars].count(currentSum)==0){\n";
                                closingPars++;
                                    *out << ind << "possibleSumValues[sharedVars].push_back(currentSum);\n";
                                    *out << ind << "possibleSumValuesSet[sharedVars].insert(currentSum);\n";
                                    *out << ind << "Tuple* auxVal = factory.addNewInternalTuple({currentSum},_"<<auxVal->getPredicateName()<<");\n";
                                    *out << ind << "const auto& insertResult = auxVal->setStatus(True);\n";
                                    *out << ind++ << "if(insertResult.second){\n";
                                    closingPars++;
                                        *out << ind << "factory.removeFromCollisionsList(auxVal->getId());\n";
                                        *out << ind << "insertTrue(insertResult);\n";
                                        *out << ind << "generationStack.push_back(auxVal->getId());\n";
                            #ifdef TRACE_PROPAGATOR
                            *out << ind << "saving0->print();\n";
                            #endif
                            while (closingPars>0){
                                *out << --ind << "}\n";
                                closingPars--;
                            }
                                // *out << ind << "for(auto pair : possibleSumValuesSet) {std::cout<<pair.first[0]<<\": \"; for(int sum: pair.second) std::cout << sum << \" \"; std::cout << std::endl;}\n";
                            // }
                        }
                        forumulaIndex++;
                    }

                }else{
                    std::unordered_set<std::string> boundTerms;
                    const aspc::Literal* body = &joinRule->getBodyLiterals()[0];
                    unsigned closingPars = printStarter(body,boundTerms);
                    const aspc::Atom* currentlySaving = &joinRule->getHead()[0];
                    closingPars+=buildLiteralSaving(&joinRule->getHead()[0],"saving"+std::to_string(subProgram.size()-1));
                    // joinRule->print();
                    // std::cout<<"Sub rules"<<std::endl;
                    for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                        const aspc::Rule* currentSubRule = &subProgram[subRuleId];
                        // currentSubRule->print();
                        const aspc::Atom* head =NULL;
                        if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                            // std::cout << "previouslySaved"<<std::endl;
                            if(currentSubRule->isConstraint()){
                                // std::cout << "constraint"<<std::endl;
                                if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                                    // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                                    head = &currentSubRule->getBodyLiterals()[1].getAtom();
                                }
                            }else{

                                head = &currentSubRule->getHead()[0];
                            }
                        }

                        if(head == NULL){
                            std::cout<<"Error compiling subprogram for rule ";rewrittenProgram->getRule(ruleWithAuxVal).print();
                            std::exit(180);
                        }else{
                            closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                            currentlySaving=head;
                        }
                    }
                    std::string sharedVars="";
                    for(unsigned k:sharedVariablesIndex){
                        std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                        if(sharedVars!="")
                            sharedVars+=",";
                        sharedVars+=term;
                    }
                    *out << ind << "std::vector<int> sharedVars({"<<sharedVars<<"});\n";
                    std::string sumTerm = aggr->isSum() ? aggr->getAggregateVariables()[0] : "1";
                    *out << ind << "unsigned actualSumCount=possibleSumValues[sharedVars].size();\n";
                    *out << ind++ << "for(unsigned k = 0; k < actualSumCount; k++){\n";
                    closingPars++;
                        *out << ind << "int currentSum = possibleSumValues[sharedVars][k]+"<<sumTerm<<";\n";
                        *out << ind++ << "if(possibleSumValuesSet[sharedVars].count(currentSum)==0){\n";
                        closingPars++;
                            *out << ind << "possibleSumValues[sharedVars].push_back(currentSum);\n";
                            *out << ind << "possibleSumValuesSet[sharedVars].insert(currentSum);\n";
                            *out << ind << "Tuple* auxVal = factory.addNewInternalTuple({currentSum},_"<<auxVal->getPredicateName()<<");\n";
                            *out << ind << "const auto& insertResult = auxVal->setStatus(True);\n";
                            *out << ind++ << "if(insertResult.second){\n";
                            closingPars++;
                                *out << ind << "factory.removeFromCollisionsList(auxVal->getId());\n";
                                *out << ind << "insertTrue(insertResult);\n";
                                *out << ind << "generationStack.push_back(auxVal->getId());\n";
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                }
            }
        }
    }

    for(int ruleId : standardRules){
        const aspc::Rule* r = &rewrittenProgram->getRule(ruleId);
        bool ruleWithAggId = false;
        for(const aspc::Literal& l : r->getBodyLiterals()){
            if(builder->isAggregateIdPredicate(l.getPredicateName()))
                ruleWithAggId =true;
        }
        if(ruleWithAggId){
            unsigned closingPars=0;
            const aspc::Literal* bodyPredicate=NULL;
            for(const aspc::Literal& l : r->getBodyLiterals()){
                if(!builder->isAggregateIdPredicate(l.getPredicateName())){
                    bodyPredicate=&l;
                    break;
                }
            }

            std::vector<aspc::Rule> subProgram = builder->getSubProgramsForRule(ruleId);
            const aspc::Rule* joinRule = &subProgram.back();
            const aspc::Atom* currentlySaving=NULL;
            unsigned litId=subProgram.size();
            std::unordered_set<std::string> boundTerms;


            if(bodyPredicate==NULL){
                //No body Literal and so ground head
                *out << ind++ << "if(starter->getPredicateName() == _"<<bodyPredicate->getPredicateName()<<"){\n";
                closingPars += 1+buildLiteralSaving(&r->getHead()[0],"saving"+std::to_string(litId));
                while(closingPars>0){
                    *out << --ind << "}\n";
                    closingPars--;
                }
            }else{
                *out << ind++ << "if(starter->getPredicateName() == _"<<bodyPredicate->getPredicateName()<<"){\n";
                closingPars++;
                if(joinRule->isConstraint()){
                    //%%%%%%%%%%%%%%%%%%
                    //%%%%%case :- l1,...,ln, not aux
                    //%%%%%%%%%%%%%%%%%%
                    closingPars += buildGeneratorForSimpleRule(bodyPredicate,&joinRule->getBodyLiterals().back().getAtom(),"saving"+std::to_string(litId),sumAggrSetPredicates);
                    currentlySaving=&joinRule->getBodyLiterals().back().getAtom();
                }
                // joinRule->print();
                // std::cout<<"Sub rules"<<std::endl;
                for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                    const aspc::Rule* currentSubRule = &subProgram.at(subRuleId);
                    // currentSubRule->print();
                    const aspc::Atom* head =NULL;
                    if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                        // std::cout << "previouslySaved"<<std::endl;
                        if(currentSubRule->isConstraint()){
                            // std::cout << "constraint"<<std::endl;
                            if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                                // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                                head = &currentSubRule->getBodyLiterals()[1].getAtom();
                            }
                        }else{

                            head = &currentSubRule->getHead()[0];
                        }
                    }

                    if(head == NULL){
                        std::cout<<"Error compiling subprogram for rule ";r->print();
                        std::exit(180);
                    }else{
                        closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                        currentlySaving=head;

                    }
                }
                *out << ind << "generationStack.push_back(saving0->getId());\n";
                #ifdef TRACE_PROPAGATOR
                *out << ind << "saving0->print();\n";
                #endif
                while(closingPars>0){
                    *out << --ind << "}\n";
                    closingPars--;
                }
            }
            continue;
        }
        std::vector<aspc::Rule> subProgram = builder->getSubProgramsForRule(ruleId);
        aspc::Rule* joinRule = &subProgram.back();

        if(joinRule->isConstraint()){
            unsigned forumulaIndex=0;
            for(const aspc::Formula* f: joinRule->getFormulas()){
                if(f->isLiteral()){
                    const aspc::Literal* l = (const aspc::Literal*)f;
                    if(stackPredicates.count(l->getPredicateName())!=0){
                        std::unordered_set<std::string> boundTerms;
                        unsigned closingPars = printStarter(l,boundTerms);
                        const aspc::Atom* currentlySaving = &joinRule->getBodyLiterals().back().getAtom();
                        closingPars+=buildGeneratorForConstraint(joinRule,"saving"+std::to_string(subProgram.size()-1),sumAggrSetPredicates,forumulaIndex,boundTerms);
                        // joinRule->print();
                        // std::cout<<"Sub rules"<<std::endl;
                        for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                            const aspc::Rule* currentSubRule = &subProgram[subRuleId];
                            // currentSubRule->print();
                            const aspc::Atom* head =NULL;
                            if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                                // std::cout << "previouslySaved"<<std::endl;
                                if(currentSubRule->isConstraint()){
                                    // std::cout << "constraint"<<std::endl;
                                    if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                                        // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                                        head = &currentSubRule->getBodyLiterals()[1].getAtom();
                                    }
                                }else{

                                    head = &currentSubRule->getHead()[0];
                                }
                            }

                            if(head == NULL){
                                std::cout<<"Error compiling subprogram for rule ";r->print();
                                std::exit(180);
                            }else{
                                closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                                currentlySaving=head;

                            }
                        }
                        *out << ind << "generationStack.push_back(saving0->getId());\n";
                        #ifdef TRACE_PROPAGATOR
                        *out << ind << "saving0->print();\n";
                        #endif
                        while (closingPars>0){
                            *out << --ind << "}\n";
                            closingPars--;
                        }
                    }
                }
                forumulaIndex++;
            }

        }else{
            std::unordered_set<std::string> boundTerms;
            const aspc::Literal* body = &joinRule->getBodyLiterals()[0];
            unsigned closingPars = printStarter(body,boundTerms);
            const aspc::Atom* currentlySaving = &joinRule->getHead()[0];
            closingPars+=buildLiteralSaving(&joinRule->getHead()[0],"saving"+std::to_string(subProgram.size()-1));
            // joinRule->print();
            // std::cout<<"Sub rules"<<std::endl;
            for(int subRuleId = subProgram.size()-2;subRuleId>=0;subRuleId--){
                const aspc::Rule* currentSubRule = &subProgram[subRuleId];
                // currentSubRule->print();
                const aspc::Atom* head =NULL;
                if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                    // std::cout << "previouslySaved"<<std::endl;
                    if(currentSubRule->isConstraint()){
                        // std::cout << "constraint"<<std::endl;
                        if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                            // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                            head = &currentSubRule->getBodyLiterals()[1].getAtom();
                        }
                    }else{

                        head = &currentSubRule->getHead()[0];
                    }
                }

                if(head == NULL){
                    std::cout<<"Error compiling subprogram for rule ";r->print();
                    std::exit(180);
                }else{
                    closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                    currentlySaving=head;

                }
            }
            *out << ind << "generationStack.push_back(saving0->getId());\n";
            while (closingPars>0){
                *out << --ind << "}\n";
                closingPars--;
            }
        }

    }
    *out << --ind << "}\n";
    *out << --ind << "}//close local scope\n";
    *out << ind << "//---------------------------------Recursive Component---------------------------------\n";
}
unsigned CompilationManager::buildLiteralSaving(const aspc::Atom* head,std::string tupleName,bool asTrue){
    unsigned closingPars=0;
    std::string headTerms = "";
    for(unsigned k=0; k<head->getAriety(); k++){
        std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
        if(headTerms!="")
            headTerms+=",";
        headTerms+=term;
    }
    *out << ind << "Tuple* "<< tupleName << " = factory.addNewInternalTuple({"<<headTerms<<"},_"<<head->getPredicateName()<<");\n";
    if(asTrue)
        *out << ind << "const auto& insertResult = "<<tupleName<<"->setStatus(True);\n";
    else
        *out << ind << "const auto& insertResult = "<<tupleName<<"->setStatus(Undef);\n";
    *out << ind++ << "if(insertResult.second){\n";
    closingPars++;
        *out << ind << "factory.removeFromCollisionsList("<<tupleName<< "->getId());\n";
        if(asTrue)
            *out << ind << "insertTrue(insertResult);\n";
        else
            *out << ind << "insertUndef(insertResult);\n";
        // *out << ind << tupleName << "->print();\n";
    return closingPars;

}
unsigned CompilationManager::buildGeneratorForSimpleRule(const aspc::Literal* body,const aspc::Atom* head,std::string tupleName,std::unordered_set<std::string> sumAggrSetPredicates,bool asTrue){
    unsigned closingPars = 0;
    std::string structType = sumAggrSetPredicates.count(body->getPredicateName())!=0 ? "IndexedSet*" : "std::vector<int>*";
    std::string valuesType = sumAggrSetPredicates.count(body->getPredicateName())!=0 ? "Set" : "Vec";
    *out << ind << "const "<<structType<<" tuples = &p"<<body->getPredicateName()<<"_.getValues"<<valuesType<<"({});\n";
    *out << ind << "const "<<structType<<" tuplesU = &u"<<body->getPredicateName()<<"_.getValues"<<valuesType<<"({});\n";
    if(sumAggrSetPredicates.count(body->getPredicateName())!=0){
        *out << ind << "auto itTrue = tuples->begin();\n";
        *out << ind << "auto itUndef = tuplesU->begin();\n";
        *out << ind++ << "while(itTrue!=tuples->end() || itUndef != tuplesU->end()){\n";
        closingPars++;
            *out << ind << "Tuple* tuple = NULL;\n";
            *out << ind << "if(itTrue!=tuples->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}\n";
            *out << ind << "else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;}\n";
    }else{
        *out << ind++ << "for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){\n";
        closingPars++;
            *out << ind << "Tuple* tuple = NULL;\n";
            *out << ind << "if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));\n";
            *out << ind << "else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
    }
    std::unordered_set<std::string> terms;
    for(unsigned k=0; k<body->getAriety(); k++){
        std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
        if(!body->isVariableTermAt(k) || terms.count(body->getTermAt(k))!=0){
            *out << ind++ << "if(tuple->at("<<k<<") == "<<term<<"){\n";
            closingPars++;
        }else{
            *out << ind << "int "<<term<< " = tuple->at("<<k<<");\n";
            terms.insert(term);
        }
    }

    return closingPars+buildLiteralSaving(head,tupleName,asTrue);
}
unsigned CompilationManager::buildGeneratorForConstraint(aspc::Rule* joinRule,std::string tupleName,std::unordered_set<std::string>sumAggrSetPredicates,unsigned starterIndex,std::unordered_set<std::string> boundVars){
    joinRule->bodyReordering({starterIndex});
    const auto& orderedBody = joinRule->getOrderedBodyByStarter(starterIndex);
    // joinRule->print();
    // std::cout<<"bodyOrdered"<<std::endl;
    unsigned closingPars =0;
    unsigned startI = starterIndex!=joinRule->getBodySize() ? 1 : 0;
    for(unsigned i=startI;i<orderedBody.size();i++){
        if(orderedBody[i]->isBoundedRelation(boundVars)){
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*)orderedBody[i];
            *out << ind++ << "if("<<ineq->getStringRep()<<"){\n";
            closingPars++;
        }else if(orderedBody[i]->isBoundedValueAssignment(boundVars)){
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*)orderedBody[i];
            *out << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";\n";
            boundVars.insert(ineq->getAssignedVariable(boundVars));
        }else if(orderedBody[i]->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)orderedBody[i];
            //skipping aux evaluation
            if(lit->getPredicateName() == joinRule->getBodyLiterals().back().getPredicateName()) continue;

            if(orderedBody[i]->isBoundedLiteral(boundVars)){
                std::string terms = "";
                for(unsigned k=0; k<lit->getAriety(); k++){
                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                    if(terms!="")
                        terms+=",";
                    terms+=term;
                }
                *out << ind << "Tuple* tuple"<<i<<" = factory.find({"<<terms<<"},_"<<lit->getPredicateName()<<");\n";
                if(lit->isNegated()){
                    *out << ind++ << "if(tuple"<<i<<"==NULL || !tuple"<<i<<"->isTrue()){\n";
                }else{
                    *out << ind++ << "if(tuple"<<i<<"!=NULL && !tuple"<<i<<"->isFalse()){\n";
                }
                closingPars++;
            }else{
                std::vector<unsigned> boundIndices;
                std::string boundTerms="";
                for(unsigned k=0; k<lit->getAriety(); k++){
                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                    if(!lit->isVariableTermAt(k) || boundVars.count(term)!=0){
                        boundIndices.push_back(k);
                        if(boundTerms!="")
                            boundTerms+=",";
                        boundTerms+=term;
                    }
                }
                std::string structType = sumAggrSetPredicates.count(lit->getPredicateName())!=0 ? "IndexedSet*" : "std::vector<int>*";
                std::string valuesType = sumAggrSetPredicates.count(lit->getPredicateName())!=0 ? "Set" : "Vec";
                *out << ind << "const "<<structType<<" tuples = &p"<<lit->getPredicateName()<<"_";
                for(unsigned k : boundIndices)
                    *out << k << "_";
                *out << ".getValues"<<valuesType<<"({"<<boundTerms<<"});\n";
                *out << ind << "const "<<structType<<" tuplesU = &u"<<lit->getPredicateName()<<"_";
                for(unsigned k : boundIndices)
                    *out << k << "_";
                *out << ".getValues"<<valuesType<<"({"<<boundTerms<<"});\n";
                if(sumAggrSetPredicates.count(lit->getPredicateName())!=0){
                    *out << ind << "auto itTrue = tuples->begin();\n";
                    *out << ind << "auto itUndef = tuplesU->begin();\n";
                    *out << ind++ << "while(itTrue!=tuples->end() || itUndef != tuplesU->end()){\n";
                    closingPars++;
                        *out << ind << "Tuple* tuple"<<i<<" = NULL;\n";
                        *out << ind << "if(itTrue!=tuples->end()){ tuple"<<i<<"=factory.getTupleFromInternalID(*itTrue);itTrue++;}\n";
                        *out << ind << "else{ tuple"<<i<<"=factory.getTupleFromInternalID(*itUndef);itUndef++;}\n";
                }else{
                    *out << ind++ << "for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){\n";
                    closingPars++;
                        *out << ind << "Tuple* tuple"<<i<<" = NULL;\n";
                        *out << ind << "if(i<tuples->size()) tuple"<<i<<"=factory.getTupleFromInternalID(tuples->at(i));\n";
                        *out << ind << "else tuple"<<i<<"=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
                }
                for(unsigned k=0; k<lit->getAriety(); k++){
                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                    if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))!=0){
                        *out << ind++ << "if(tuple"<<i<<"->at("<<k<<") == "<<term<<"){\n";
                        closingPars++;
                    }else{
                        *out << ind << "int "<<term<< " = tuple"<<i<<"->at("<<k<<");\n";
                        boundVars.insert(term);
                    }
                }
            }
        }
    }

    closingPars+=buildLiteralSaving(&joinRule->getBodyLiterals().back().getAtom(),tupleName);
    const aspc::Atom* savingAtom = &joinRule->getBodyLiterals().back().getAtom();
    if(auxForRecursiveComponent.count(savingAtom->getPredicateName())!=0){
        auto* pair = &auxForRecursiveComponent[savingAtom->getPredicateName()];
        for(unsigned i=0;i<orderedBody.size();i++){
            orderedBody[i]->print(); std::cout << i << std::endl;
            if(orderedBody[i]->isPositiveLiteral()){
                const aspc::Literal* l = (const aspc::Literal*)orderedBody[i];
                if(pair->second.count(l->getPredicateName())!=0){
                    std::string tuple = i==0 && starterIndex!=joinRule->getBodySize() ? "starter" : "tuple"+std::to_string(i);
                    *out << ind++ << "if(supportedAux"<<pair->first<<".size() < factory.size())\n";
                        *out << ind-- << "supportedAux"<<pair->first<<".resize(factory.size());\n";
                    *out << ind << "supportedAux"<<pair->first<<"["<<tuple<<"->getId()].push_back("<<tupleName<<"->getId());\n";
                }
            }
        }
    }
    return closingPars;
}
void CompilationManager::buildAuxValGenerator(std::string predicate,int ruleId,aspc::EagerProgram* sourceProgram){

    aspc::Rule referenceRule(sourceProgram->getRules()[ruleId]);
    const aspc::Aggregate* aggr = &referenceRule.getArithmeticRelationsWithAggregate()[0].getAggregate();
    const aspc::Atom* head=&referenceRule.getHead()[0];
    const aspc::Literal* body=&aggr->getAggregateLiterals()[0];
    std::string structType = aggr->isSum() ? "IndexedSet*" : "std::vector<int>*";
    std::string valuesType = aggr->isSum() ? "Set" : "Vec";
    *out << ind++ << "{\n";
        *out << ind << "std::map<std::vector<int>,std::vector<int>> possibleSumValues;\n";
        *out << ind << "std::map<std::vector<int>,std::unordered_set<int>> possibleSumValuesSet;\n";

        unsigned closingPars=1;
        *out << ind << "const "<<structType<<" tuples = &p"<<body->getPredicateName()<<"_.getValues"<<valuesType<<"({});\n";
        *out << ind << "const "<<structType<<" tuplesU = &u"<<body->getPredicateName()<<"_.getValues"<<valuesType<<"({});\n";
        if(aggr->isSum()){
            *out << ind << "auto itTrue = tuples->begin();\n";
            *out << ind << "auto itUndef = tuplesU->begin();\n";
            *out << ind++ << "while(itTrue!=tuples->end() || itUndef != tuplesU->end()){\n";
            closingPars++;
                *out << ind << "Tuple* tuple = NULL;\n";
                *out << ind << "if(itTrue!=tuples->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}\n";
                *out << ind << "else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;}\n";
        }else{
            *out << ind++ << "for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){\n";
            closingPars++;
                *out << ind << "Tuple* tuple = NULL;\n";
                *out << ind << "if(i<tuples->size()) tuple=factory.getTupleFromInternalID(tuples->at(i));\n";
                *out << ind << "else tuple=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
        }
        std::unordered_set<std::string> terms;
        for(unsigned k=0; k<body->getAriety(); k++){
            std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
            if(!body->isVariableTermAt(k) || terms.count(body->getTermAt(k))!=0){
                *out << ind++ << "if(tuple->at("<<k<<") == "<<term<<"){\n";
                closingPars++;
            }else{
                *out << ind << "int "<<term<< " = tuple->at("<<k<<");\n";
                terms.insert(term);
            }
        }
        std::string sharedVars="";
        for(unsigned k=0; k<head->getAriety(); k++){
            std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
            if(head->isVariableTermAt(k) && terms.count(term)!=0){
                if(sharedVars!="")
                    sharedVars+=",";
                sharedVars+=term;
            }
        }
        *out << ind << "std::vector<int> sharedVars({"<<sharedVars<<"});\n";
        *out << ind++ << "if(possibleSumValues[sharedVars].empty()){ // init with 0\n";
            *out << ind << "possibleSumValues[sharedVars].push_back(0);\n";
            *out << ind << "possibleSumValuesSet[sharedVars].insert(0);\n";
            *out << ind << "Tuple* auxVal = factory.addNewInternalTuple({0},_"<<predicate<<");\n";
            *out << ind << "const auto& insertResult = auxVal->setStatus(True);\n";
            *out << ind++ << "if(insertResult.second){\n";
                *out << ind << "factory.removeFromCollisionsList(auxVal->getId());\n";
                *out << ind << "insertTrue(insertResult);\n";
                // *out << ind << "auxVal->print();\n";
            *out << --ind << "}\n";
        *out << --ind << "}//closing init with 0\n";
        std::string sumTerm = aggr->isSum() ? aggr->getAggregateVariables()[0] : "1";
        *out << ind << "unsigned actualSumCount=possibleSumValues[sharedVars].size();\n";
        *out << ind++ << "for(unsigned k = 0; k < actualSumCount; k++){\n";
        closingPars++;
            *out << ind << "int currentSum = possibleSumValues[sharedVars][k]+"<<sumTerm<<";\n";
            *out << ind++ << "if(possibleSumValuesSet[sharedVars].count(currentSum)==0){\n";
            closingPars++;
                *out << ind << "possibleSumValues[sharedVars].push_back(currentSum);\n";
                *out << ind << "possibleSumValuesSet[sharedVars].insert(currentSum);\n";
                *out << ind << "Tuple* auxVal = factory.addNewInternalTuple({currentSum},_"<<predicate<<");\n";
                *out << ind << "const auto& insertResult = auxVal->setStatus(True);\n";
                *out << ind++ << "if(insertResult.second){\n";
                closingPars++;
                    *out << ind << "factory.removeFromCollisionsList(auxVal->getId());\n";
                    *out << ind << "insertTrue(insertResult);\n";
                    // *out << ind << "auxVal->print();\n";
        while(closingPars>0){
            *out << --ind << "}\n";
            closingPars--;
        }
}
unsigned CompilationManager::buildGeneratorForRuleWithAggId(const aspc::Rule& r,AspCore2ProgramBuilder* builder,std::vector<aspc::Rule>subprogram,int ruleId,std::unordered_set<std::string> sumAggrSetPredicates,bool collect){
    unsigned closingPars=0;
    const aspc::Literal* bodyPredicate=NULL;
    for(const aspc::Literal& l : r.getBodyLiterals()){
        if(!builder->isAggregateIdPredicate(l.getPredicateName())){
            bodyPredicate=&l;
            break;
        }
    }
    //storing simple rule

    // auto itSubProgram = ruleToSubProgram[ruleId];
    // if(itSubProgram==ruleToSubProgram.end())
    //     return closingPars;

    std::vector<aspc::Rule>* subProgram = &subprogram;
    aspc::Rule* joinRule = &subProgram->back();
    const aspc::Atom* currentlySaving=NULL;
    unsigned litId=subprogram.size();
     if(bodyPredicate==NULL){
        //No body Literal and so ground head
        closingPars += buildLiteralSaving(&r.getHead()[0],"saving"+std::to_string(litId));
    }else{
        if(joinRule->isConstraint()){
            //%%%%%%%%%%%%%%%%%%
            //%%%%%case :- l1,...,ln, not aux
            //%%%%%%%%%%%%%%%%%%

            closingPars += buildGeneratorForSimpleRule(bodyPredicate,&joinRule->getBodyLiterals().back().getAtom(),"saving"+std::to_string(litId),sumAggrSetPredicates);
            currentlySaving=&joinRule->getBodyLiterals().back().getAtom();
        }
        // joinRule->print();
        // std::cout<<"Sub rules"<<std::endl;
        for(int subRuleId = subProgram->size()-2;subRuleId>=0;subRuleId--){
            const aspc::Rule* currentSubRule = &subProgram->at(subRuleId);
            // currentSubRule->print();
            const aspc::Atom* head =NULL;
            if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
                // std::cout << "previouslySaved"<<std::endl;
                if(currentSubRule->isConstraint()){
                    // std::cout << "constraint"<<std::endl;
                    if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                        // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                        head = &currentSubRule->getBodyLiterals()[1].getAtom();
                    }
                }else{

                    head = &currentSubRule->getHead()[0];
                }
            }

            if(head == NULL){
                std::cout<<"Error compiling subprogram for rule ";r.print();
                std::exit(180);
            }else{
                closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
                currentlySaving=head;

            }
        }

        if(collect){
            *out << ind << "generationStack.push_back(saving0->getId());\n";
            #ifdef TRACE_PROPAGATOR
            *out << ind << "saving0->print();\n";
            #endif
        }
    }
    return closingPars;
}

unsigned CompilationManager::buildGeneratorForExiteRule(const aspc::Rule& r,std::vector<aspc::Rule>subprogram,int ruleId,std::unordered_set<std::string> sumAggrSetPredicates,bool collect){
    unsigned closingPars=0;
    //storing simple rule

    // auto itSubProgram = ruleToSubProgram[ruleId];
    // if(itSubProgram==ruleToSubProgram.end())
    //     return closingPars;

    std::vector<aspc::Rule>* subProgram = &subprogram;
    aspc::Rule* joinRule = &subProgram->back();
    const aspc::Atom* currentlySaving=NULL;
    unsigned litId=subprogram.size();
    if(joinRule->isConstraint()){
        //%%%%%%%%%%%%%%%%%%
        //%%%%%case :- l1,...,ln, not aux
        //%%%%%%%%%%%%%%%%%%
        std::unordered_set<std::string> boundVars;
        closingPars+=buildGeneratorForConstraint(joinRule,"saving"+std::to_string(litId),sumAggrSetPredicates,joinRule->getBodySize(),boundVars);
        currentlySaving=&joinRule->getBodyLiterals().back().getAtom();
    }else{
    //%%%%%%%%%%%%%%%%%%
        //%%%%%case sup:- body or head :- body
        //%%%%%%%%%%%%%%%%%%
        const aspc::Literal* body = &joinRule->getBodyLiterals()[0];
        const aspc::Atom* head = &joinRule->getHead()[0];
        currentlySaving=head;
        closingPars += buildGeneratorForSimpleRule(body,head,"saving"+std::to_string(litId),sumAggrSetPredicates);
    }
    // joinRule->print();
    // std::cout<<"Sub rules"<<std::endl;
    for(int subRuleId = subProgram->size()-2;subRuleId>=0;subRuleId--){
        const aspc::Rule* currentSubRule = &subProgram->at(subRuleId);
        // currentSubRule->print();
        const aspc::Atom* head =NULL;
        if(currentSubRule->getBodyLiterals()[0].getPredicateName() == currentlySaving->getPredicateName()){
            // std::cout << "previouslySaved"<<std::endl;
            if(currentSubRule->isConstraint()){
                // std::cout << "constraint"<<std::endl;
                if(currentSubRule->getBodyLiterals().size() == 2 && currentSubRule->getBodyLiterals()[1].isNegated()){
                    // currentSubRule->getBodyLiterals()[1].print();std::cout << " nextToSave"<<std::endl;

                    head = &currentSubRule->getBodyLiterals()[1].getAtom();
                }
            }else{

                head = &currentSubRule->getHead()[0];
            }
        }

        if(head == NULL){
            std::cout<<"Error compiling subprogram for rule ";r.print();
            std::exit(180);
        }else{
            closingPars+=buildLiteralSaving(head,"saving"+std::to_string(subRuleId));
            currentlySaving=head;

        }
    }

    if(collect){
        *out << ind << "generationStack.push_back(saving0->getId());\n";
        #ifdef TRACE_PROPAGATOR
        *out << ind << "saving0->print();\n";
        #endif
    }
    return closingPars;
}
void CompilationManager::buildGeneratorForNonRecursiveComponent(std::vector<int> component,AspCore2ProgramBuilder* builder){
    aspc::EagerProgram* rewrittenProgram = &builder->getRewrittenProgram();
    std::unordered_set<std::string> sumAggrSetPredicates;
    for(const aspc::Rule& r : rewrittenProgram->getRules()){
        if(r.containsAggregate()) {
            const aspc::Aggregate* aggr = &r.getArithmeticRelationsWithAggregate()[0].getAggregate();
            if(aggr->isSum()){
                sumAggrSetPredicates.insert(aggr->getAggregateLiterals()[0].getPredicateName());
            }
        }
    }
    for(aspc::Atom fact : builder->getFacts()){
        //Assuming that fact predicates appear in the program
        int id = rewrittenProgram->getGeneratorPredicateId(fact.getPredicateName());
        if(id!=component[0]) continue;
        *out << ind++ << "{\n";
            *out << ind << "Tuple* fact = factory.addNewInternalTuple({";
            for(unsigned k=0; k<fact.getAriety(); k++){
                if(fact.isVariableTermAt(k)){std::cout << "Error:   Unsafe fact "<<std::endl;exit(180);}
                std::string term = isInteger(fact.getTermAt(k)) ? fact.getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+fact.getTermAt(k)+"\")";
                if(k>0)
                    *out << ",";
                *out << term;
            }
            *out << "},_"<<fact.getPredicateName()<<");\n";
            *out << ind << "const auto& insertResult = fact->setStatus(True);\n";
            *out << ind++ << "if(insertResult.second){\n";
                *out << ind << "factory.removeFromCollisionsList(fact->getId());\n";
                *out << ind << "insertTrue(insertResult);\n";
                *out << ind << "eagerFacts.insert(fact->getId());\n";
            *out << --ind << "}\n";
        *out << --ind << "}\n";
    }
    std::string predName = rewrittenProgram->getGenPredicateName(component[0]);
    if(builder->isValuePredicate(predName)){
        buildAuxValGenerator(predName,builder->getRuleForAuxVal(predName),rewrittenProgram);
    }else if(builder->isDomainPredicate(predName)){
        *out << ind++ << "{\n";
        unsigned closingPars = 1;
        for(const aspc::Rule& r : rewrittenProgram->getRules()){
            if(r.containsAggregate() && r.getBodyLiterals().size() == 1){
                if(builder->isDomainPredicateForPredicate(predName,r.getBodyLiterals()[0].getPredicateName())){
                    aspc::Atom head(predName,r.getBodyLiterals()[0].getTerms());
                    closingPars += buildGeneratorForSimpleRule(&r.getBodyLiterals()[0],&head,"domPred",sumAggrSetPredicates,true);
                    break;
                }
            }
        }
        while (closingPars>0){
            closingPars--;
            *out << --ind << "}\n";
        }

    }else{
        int ruleId=0;
        // std::cout << "searching rules for component"<<std::endl;
        for(const aspc::Rule& r : rewrittenProgram->getRules()){
            if(!r.isConstraint() && r.getHead()[0].getPredicateName() == predName){
                bool ruleWithAggId = false;
                for(const aspc::Literal& l:r.getBodyLiterals()){
                    if(builder->isAggregateIdPredicate(l.getPredicateName())){
                        ruleWithAggId=true;
                        break;
                    }
                }
                // std::cout << "Rule found for component"<<std::endl;
                *out << ind++ << "{\n";
                unsigned closingPars =1;

                if(r.containsAggregate()){
                    //storing aggr_ids
                    const aspc::Literal* body = !r.getBodyLiterals().empty() ? &r.getBodyLiterals()[0] : NULL;
                    const aspc::Atom* head = &r.getHead()[0];

                    if(body != NULL){
                        closingPars += buildGeneratorForSimpleRule(body,head,"aggr_id",sumAggrSetPredicates);
                    }else{
                        *out << ind << "Tuple* aggr_id = factory.addNewInternalTuple({},_"<<head->getPredicateName()<<");\n";
                        *out << ind << "const auto& insertResult = aggr_id->setStatus(Undef);\n";
                        *out << ind++ << "if(insertResult.second){\n";
                        closingPars++;
                            *out << ind << "factory.removeFromCollisionsList(aggr_id->getId());\n";
                            *out << ind << "insertUndef(insertResult);\n";
                    }
                }else if(!ruleWithAggId){
                    closingPars += buildGeneratorForExiteRule(r,builder->getSubProgramsForRule(ruleId),ruleId,sumAggrSetPredicates);
                }else{
                    closingPars += buildGeneratorForRuleWithAggId(r,builder,builder->getSubProgramsForRule(ruleId),ruleId,sumAggrSetPredicates);
                }
                while (closingPars>0){
                    closingPars--;
                    *out << --ind << "}\n";
                }
            }
            ruleId++;
        }
    }

}
void CompilationManager::buildGeneratorActualAndPossibleSum(AspCore2ProgramBuilder* builder,const aspc::Program& program){
    for(const aspc::Rule& r : program.getRules()){
        if(r.containsAggregate()){
            const aspc::Aggregate* aggr = &r.getArithmeticRelationsWithAggregate()[0].getAggregate();
            if(aggr->isSum()){
                *out << ind++ << "{\n";
                unsigned closingPars=1;
                const aspc::Atom* aggrId = &r.getHead()[0];
                const aspc::Literal* aggrSet = &aggr->getAggregateLiterals()[0];
                std::unordered_set<std::string> boundVars;
                if(aggrId->getAriety()==0){
                    *out << ind << "Tuple* aggr_id = factory.find({},_"<<aggrId->getPredicateName()<<");\n";
                }else{
                    *out << ind << "const std::vector<int>* tuples = &p"<<aggrId->getPredicateName()<<"_.getValuesVec({});\n";
                    *out << ind << "const std::vector<int>* tuplesU = &u"<<aggrId->getPredicateName()<<"_.getValuesVec({});\n";
                    *out << ind++ << "for(unsigned i = 0; i < tuples->size() + tuplesU->size(); i++){\n";
                    closingPars++;
                        *out << ind << "Tuple* aggr_id = NULL;\n";
                        *out << ind << "if(i<tuples->size()) aggr_id=factory.getTupleFromInternalID(tuples->at(i));\n";
                        *out << ind << "else aggr_id=factory.getTupleFromInternalID(tuplesU->at(i-tuples->size()));\n";
                    for(unsigned k=0; k<aggrId->getAriety(); k++){
                        std::string term = aggrId->isVariableTermAt(k) || isInteger(aggrId->getTermAt(k)) ? aggrId->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+aggrId->getTermAt(k)+"\")";
                        if(!aggrId->isVariableTermAt(k) || boundVars.count(aggrId->getTermAt(k))!=0){
                            *out << ind++ << "if(aggr_id->at("<<k<<") == "<<term<<"){\n";
                            closingPars++;
                        }else{
                            *out << ind << "int "<<term<< " = aggr_id->at("<<k<<");\n";
                            boundVars.insert(term);
                        }
                    }
                }
                std::string boundTerms="";
                std::string boundIndices="";
                for(unsigned k :sharedVarAggrIDToAggrSetIndices[aggrId->getPredicateName()]){
                    std::string term = aggrSet->getTermAt(k);
                    if(boundTerms!="")
                        boundTerms+=",";
                    boundTerms+=term;
                    boundIndices+=std::to_string(k)+"_";
                }

                *out << ind << "const IndexedSet* aggrSet = &p"<<aggrSet->getPredicateName()<<"_"<<boundIndices<<".getValuesSet({"<<boundTerms<<"});\n";
                *out << ind << "const IndexedSet* aggrSetU = &u"<<aggrSet->getPredicateName()<<"_"<<boundIndices<<".getValuesSet({"<<boundTerms<<"});\n";
                *out << ind << "auto itTrue = aggrSet->begin();\n";
                *out << ind << "auto itUndef = aggrSetU->begin();\n";
                *out << ind << "int& sum = possibleSum[aggr_id->getId()];\n";

                *out << ind++ << "while(itTrue!=aggrSet->end() || itUndef != aggrSetU->end()){\n";
                closingPars++;
                    *out << ind << "Tuple* tuple = NULL;\n";
                    *out << ind << "bool undefTuple = false;\n";
                    *out << ind << "if(itTrue!=aggrSet->end()){ tuple=factory.getTupleFromInternalID(*itTrue);itTrue++;}\n";
                    *out << ind << "else{ tuple=factory.getTupleFromInternalID(*itUndef);itUndef++;undefTuple=true;}\n";

                    for(unsigned k=0; k<aggrSet->getAriety(); k++){
                        std::string term = aggrSet->isVariableTermAt(k) || isInteger(aggrSet->getTermAt(k)) ? aggrSet->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+aggrSet->getTermAt(k)+"\")";
                        if(!aggrSet->isVariableTermAt(k) || boundVars.count(aggrSet->getTermAt(k))!=0){
                            *out << ind++ << "if(tuple->at("<<k<<") == "<<term<<"){\n";
                            closingPars++;
                        }else{
                            *out << ind << "int "<<term<< " = tuple->at("<<k<<");\n";
                            boundVars.insert(term);
                        }
                    }
                    *out << ind << "sum+="<<aggr->getAggregateVariables()[0]<<";\n";
                while (closingPars>0){
                    closingPars--;
                    *out << --ind << "}\n";
                }

            }
        }
    }
}
void CompilationManager::buildAggrSetOrdering(const AspCore2ProgramBuilder* builder){

    if(predicateToOrderdedAux.size()>0){
        *out << ind << "std::vector<int> ordered_ids;\n";
        *out << ind << "std::vector<int> tuplesIdOrdered;\n";
        *out << ind << "std::map<int, Tuple*> idToTuples;\n";
        *out << ind << "int currentIdIndex=0;\n";
    }
    for(auto& pair : predicateToOrderdedAux){
        *out << ind++ << "{\n";
            // *out<<ind<<"std::cout<<\"Ordering\"<<std::endl;\n";
            *out << ind << "const IndexedSet tuples = u"<<pair.first<<"_.getValuesSet({});\n";
            *out << ind << "ordered_ids.reserve(tuples.size());\n";
            *out << ind << "tuplesIdOrdered.reserve(tuples.size());\n";
            *out << ind++ << "for(int id :tuples){\n";
                *out << ind << "tuplesIdOrdered.push_back(id);\n";
                *out << ind << "ordered_ids.push_back(id);\n";
                *out << ind << "idToTuples[id]=factory.getTupleFromInternalID(id);\n";
                *out << ind << "factory.removeFromCollisionsList(id);\n";
                *out << ind << "idToTuples[id]->setStatus(UNKNOWN);\n";

            *out << --ind << "}\n";
            *out << ind << "std::stable_sort(tuplesIdOrdered.begin(),tuplesIdOrdered.end(),compTuple);\n";
            *out << ind++ << "for(int id: tuplesIdOrdered){\n";
                *out << ind << "Tuple* t=idToTuples[id];\n";
                *out << ind << "factory.setId(t,ordered_ids[currentIdIndex++]);\n";
                *out << ind << "const auto& insertResult = t->setStatus(Undef);\n";
                *out << ind++ << "if (insertResult.second) {\n";
                    *out << ind << "factory.removeFromCollisionsList(t->getId());\n";
                    *out << ind << "insertUndef(insertResult);\n";
                *out << --ind << "}\n";

            *out << --ind << "}\n";
            #ifdef TRACE_PROPAGATOR
                *out << ind++ << "for(int id :u"<<pair.first<<"_.getValuesSet({})){\n";
                    *out << ind << "std::cout<<id<<\" \";factory.getTupleFromInternalID(id)->print();\n";
                *out << --ind << "}\n";
            #endif
            *out << ind << "ordered_ids.clear();\n";
            *out << ind << "tuplesIdOrdered.clear();\n";
            *out << ind << "idToTuples.clear();\n";
            *out << ind << "currentIdIndex=0;\n";
        *out << --ind << "}\n";
    }

}
void CompilationManager::buildGenerator(AspCore2ProgramBuilder* builder,const aspc::Program& program){

    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_agg_id_0) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_agg_id_1) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_aux_0) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_inPath) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_node) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_reached) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_start) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_sup_0) << std::endl;\n";
    // *out << ind << "std::cout << (std::bitset<64>)reinterpret_cast<size_t>(&_sup_1) << std::endl;\n";
    //Graph with aggregate rewriting predicates
    aspc::EagerProgram& rewrittenProgram = builder->getRewrittenProgram();
    GraphWithTarjanAlgorithm& graph = rewrittenProgram.getGeneratorDG();
    std::vector<std::vector<int>> scc = graph.SCC();
    std::unordered_map<int,std::string> waitingComponents;
    std::unordered_set<std::string> generated;


    for(int componentId=scc.size()-1;componentId>=0;componentId--){
        bool recursive = scc[componentId].size() > 1;
        if(!recursive){
            for(int adj : graph.getAdjForNode(scc[componentId][0])){
                if(adj == scc[componentId][0]){
                    recursive=true;
                    break;
                }
            }
        }
        *out << ind << "std::cout<<\"Component "<<componentId<<"\"<<std::endl;\n";
        if(recursive){
            buildGeneratorForRecursiveComponent(scc[componentId],builder);
        }
        else{
            buildGeneratorForNonRecursiveComponent(scc[componentId],builder);
        }

    }
    GraphWithTarjanAlgorithm& programGraph = rewrittenProgram.getPositiveDG();
    std::vector<std::vector<int>> programScc = programGraph.SCC();
    bool allocateFoundnessFactory=true;
    for(int componentId=programScc.size()-1;componentId>=0;componentId--){
        bool recursive = programScc[componentId].size() > 1;
        if(!recursive){
            for(int adj : programGraph.getAdjForNode(programScc[componentId][0])){
                if(adj == programScc[componentId][0]){
                    recursive=true;
                    break;
                }
            }
        }
        if(recursive){
            if(allocateFoundnessFactory){
                allocateFoundnessFactory=false;
                *out << ind << "foundnessFactory.resize(factory.size());\n";
            }
            buildUnfoundedInit(programScc[componentId],componentId,builder);
        }

    }
    // std::cout << "Printing Sum Generation" << std::endl;
    buildAggrSetOrdering(builder);
    // *out << ind << "std::cout << \"actual and possible sums\"<<std::endl;\n";
    // *out << ind << "std::cout << \"Factory size: \";factory.printSize();\n";
    buildGeneratorActualAndPossibleSum(builder,program);
    // *out << ind << "std::cout << \"end\"<<std::endl;\n";

    #ifdef TRACE_PROPAGATOR
        std::cout << "Printing generated literals" << std::endl;
    #endif

}
void CompilationManager::compileEagerSimpleRule(const aspc::Rule& r,bool fromStarter){
    const aspc::Literal* body = &r.getBodyLiterals()[0];
    const aspc::Atom* head = &r.getHead()[0];

    if(fromStarter){
        *out << ind++ << "if(starter.getPredicateName() == _"<<body->getPredicateName()<<"){\n";
        {
            std::unordered_set<std::string> boundVariables;
            unsigned closingPars=0;
            printAtomVariables(&body->getAtom(),"starter",".",boundVariables,closingPars);
            *out << ind << "Tuple* head = factory.find({";
            for(unsigned k=0; k<head->getAriety(); k++){
                std::string term = head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                if(k>0)
                    *out << ",";
                *out << term;
            }
            *out << "}, _"<<head->getPredicateName()<<");\n";
            *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
            *out << ind++ << "if(startVar > 0){\n";
                //rule propagation starting from true body
                *out << ind++ << "if(head == NULL || (!head->isTrue() && !head->isUndef())){\n";
                    //head false found for true body
                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                        *out << ind << "int it = head->getId();\n";
                        *out << ind << "shared_reason.get()->insert(startVar);\n";
                        *out << ind << "reasonForLiteral[it]=shared_reason;\n";
                        *out << ind << "handleConflict(it, propagatedLiterals);\n";
                    *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                    *out << ind << "return;\n";
                *out << --ind << "}else if(head !=NULL && head->isUndef()){\n";
                ind++;
                    //undefined head for true body
                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                        *out << ind << "int it = head->getId();\n";
                        *out << ind << "shared_reason.get()->insert(startVar);\n";
                        *out << ind << "auto itReason = reasonForLiteral.emplace(it,shared_reason);\n";
                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                        #ifdef TRACE_REASON
                            *out << ind << "std::cout << \"Reason of \"<<head->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                        #endif
                    *out << --ind << "}\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                    #endif
                    *out << ind << "propUndefined(head,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                *out << --ind << "}\n";
            *out << --ind << "}else{\n";
            ind++;
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"Propagation starting from false body\"<<std::endl;\n";
                #endif
                //propagation starting for negative body
                std::unordered_set<std::string> headVariables;
                for(unsigned i=0;i<head->getAriety();i++)
                    if(head->isVariableTermAt(i))
                        headVariables.insert(head->getTermAt(i));

                if(body->isBoundedLiteral(headVariables)){
                    // unique body for head
                    *out << ind++ << "if(head != NULL && head->isTrue()){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict: unsupported head atom "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            *out << ind << "int it = head->getId();\n";
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << ind << "reasonForLiteral[-it]=shared_reason;\n";
                            *out << ind << "handleConflict(-it, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";

                        *out << ind << "return;\n";
                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind++ << "if(head != NULL && head->isUndef()){\n";

                            *out << ind++ << "if(currentDecisionLevel>0){\n";
                                *out << ind << "int it = head->getId();\n";
                                *out << ind << "shared_reason.get()->insert(startVar);\n";
                                *out << ind << "auto itReason = reasonForLiteral.emplace(-it,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                                #ifdef TRACE_REASON
                                    *out << ind << "std::cout << \"Reason of \"<<head->toString()<<\": {\"<<std::endl;\n";
                                    *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                    *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                #endif
                            *out << --ind << "}\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                }else{
                    std::vector<unsigned> boundIndices;
                    std::string boundTerms;
                    for(unsigned i=0;i<body->getAriety();i++){
                        if(!body->isVariableTermAt(i) || headVariables.count(body->getTermAt(i))!=0){
                            boundIndices.push_back(i);
                            if(boundTerms!="")
                                boundTerms+=", ";
                            std::string term = body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            boundTerms+=term;
                        }
                    }
                    bool isSet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                    printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"Evaluating\"<<std::endl;\n";
                        *out << ind << "if(head == NULL) std::cout << \"Null head \"<<std::endl;\n";
                        *out << ind << "else if(head->isFalse()) std::cout << \"False head \"<<std::endl;\n";
                    #endif
                    *out << ind++ << "if(head != NULL && head->isTrue()){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"head is true\"<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(tuples->size() == 0 && tuplesU->size() == 0){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict: unable to find support for true head "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                            *out << ind++ << "if(currentDecisionLevel>0){\n";
                                *out << ind << "int itHead = head->getId();\n";
                                printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                                if(isSet){
                                    *out << ind++ << "for(auto i=tuplesF->begin();i != tuplesF->end();i++){\n";
                                        *out << ind << "int it = *i;\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                        *out << ind << "int it = tuplesF->at(i);\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                }
                                *out << ind << "reasonForLiteral[-itHead]=shared_reason;\n";


                                *out << ind << "handleConflict(-itHead, propagatedLiterals);\n";
                            *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";

                        *out << --ind << "}else if(tuples->size() == 0 && tuplesU->size() == 1){\n";
                        ind++;
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"Propagation: prop support for head "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            //last possible support for true head
                            if(isSet){
                                *out << ind++ << "if(currentDecisionLevel>0){\n";
                                    *out << ind << "int itProp = *tuplesU->begin();\n";
                                    printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                                    *out << ind++ << "for(auto i=tuplesF->begin();i!=tuplesF->end();i++){\n";
                                        *out << ind << "int it = *i;\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "int it = head->getId();\n";
                                    *out << ind << "shared_reason.get()->insert(it);\n";

                                    *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                    *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                        *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    #ifdef TRACE_REASON
                                        *out << ind << "std::cout << \"Reason of \"<<factory.getTupleFromInternalID(*tuplesU->begin())->toString()<<\": {\"<<std::endl;\n";
                                        *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                        *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                    #endif
                                *out << --ind << "}\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                                *out << ind << "propUndefined(factory.getTupleFromInternalID(*tuplesU->begin()),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                            }else{
                                *out << ind++ << "if(currentDecisionLevel>0){\n";
                                    *out << ind << "int itProp = tuplesU->at(0);\n";
                                    printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                                    *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                        *out << ind << "int it = tuplesF->at(i);\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "int it = head->getId();\n";
                                    *out << ind << "shared_reason.get()->insert(it);\n";
                                    *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                    *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                        *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    #ifdef TRACE_REASON
                                        *out << ind << "std::cout << \"Reason of \"<<factory.getTupleFromInternalID(tuplesU->at(0))->toString()<<\": {\"<<std::endl;\n";
                                        *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                        *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                    #endif
                                *out << --ind << "}\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                                *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(0)),false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                            }
                        *out << --ind << "}\n";
                    *out << --ind << "}else if( head != NULL && head->isUndef() ){\n";
                    ind++;
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"head is undef\"<<std::endl;\n";
                        #endif
                        //undef head
                        *out << ind++ << "if(tuples->size() == 0 && tuplesU->size() == 0){\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"Propagation: head without support "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind++ << "if(currentDecisionLevel>0){\n";
                                *out << ind << "int itHead = head->getId();\n";
                                printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                                if(isSet){
                                    *out << ind++ << "for(auto i=tuplesF->begin();i!=tuplesF->end();i++){\n";
                                        *out << ind << "int it = *i;\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind++ << "for(unsigned i=0;i<tuplesF->size();i++){\n";
                                        *out << ind << "int it = tuplesF->at(i);\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                }
                                *out << ind << "auto itReason = reasonForLiteral.emplace(-itHead,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                                #ifdef TRACE_REASON
                                    *out << ind << "std::cout << \"Reason of \"<<head->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                    *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                #endif
                            *out << --ind << "}\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propUndefined(head,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                }
            *out << --ind << "}\n";
            while (closingPars>0){
                *out << --ind << "}\n";
                closingPars--;
            }


        }
        *out << --ind << "}else if(starter.getPredicateName() == _"<<head->getPredicateName()<<"){\n";
        ind++;
        {
            std::unordered_set<std::string> boundVariables;
            unsigned closingPars=0;
            printAtomVariables(head,"starter",".",boundVariables,closingPars);
            *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";

            if(body->isBoundedLiteral(boundVariables)){
                *out << ind << "Tuple* currentBody = factory.find({";
                for(unsigned k=0; k<body->getAriety(); k++){
                    std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                    if(k>0)
                        *out << ",";
                    *out << term;
                }
                *out << "}, _"<<body->getPredicateName()<<");\n";
                *out << ind++ << "if(startVar > 0){\n";
                    *out << ind++ << "if(currentBody->isFalse()){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict: unable to find support for true head "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            *out << ind << "int it = currentBody->getId();\n";
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << ind << "reasonForLiteral[it]=shared_reason;\n";
                            *out << ind << "handleConflict(it, propagatedLiterals);\n";
                        *out << --ind << "} else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";
                    *out << --ind << "}else if(currentBody->isUndef()){\n";
                    ind++;
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            *out << ind << "int it = currentBody->getId();\n";
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << ind << "auto itReason = reasonForLiteral.emplace(it,shared_reason);\n";
                                *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                    *out << ind-- << "itReason.first->second=shared_reason;\n";
                            #ifdef TRACE_REASON
                                *out << ind << "std::cout << \"Reason of \"<<currentBody->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                *out << ind << "std::cout << \"}\"<<std::endl;\n";
                            #endif
                        *out << --ind << "}\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind << "propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                    *out << --ind << "}\n";
                *out << --ind << "}else{\n";
                ind++;
                    *out << ind++ << "if(currentBody->isTrue()){\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict: support found for false head "<<r.getRuleId()<<"\"<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            *out << ind << "int it = currentBody->getId();\n";
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << ind << "reasonForLiteral[-it]=shared_reason;\n";
                            *out << ind << "handleConflict(-it, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";
                    *out << --ind << "}else if(currentBody->isUndef()){\n";
                    ind++;
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            *out << ind << "int it = currentBody->getId();\n";
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << ind << "auto itReason = reasonForLiteral.emplace(-it,shared_reason);\n";
                            *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                *out << ind-- << "itReason.first->second=shared_reason;\n";
                            #ifdef TRACE_REASON
                                *out << ind << "std::cout << \"Reason of \"<<currentBody->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                *out << ind << "std::cout << \"}\"<<std::endl;\n";
                            #endif
                        *out << --ind << "}\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                        *out << ind << "propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                    *out << --ind << "}\n";

                *out << --ind << "}\n";
            }else{
                std::vector<unsigned> boundIndices;
                std::string boundTerms;
                for(unsigned k=0; k<body->getAriety(); k++){
                    if(!body->isVariableTermAt(k) || boundVariables.count(body->getTermAt(k))!=0){
                        boundIndices.push_back(k);
                        if(boundTerms!="")
                            boundTerms+=",";
                        std::string term = body->isVariableTermAt(k) || isInteger(body->getTermAt(k)) ? body->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(k)+"\")";
                        boundTerms+=term;
                    }
                }
                bool isSet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                *out << ind++ << "if(startVar > 0){\n";
                    *out << ind++ << "if(tuples->size()==0){\n";
                        *out << ind++ << "if(tuplesU->size() == 0){\n";
                            //no support for true head
                            *out << ind++ << "if(currentDecisionLevel>0){\n";
                            printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                            if(isSet){
                                *out << ind++ << "for(auto i=tuplesF->begin(); i!=tuplesF->end(); i++){\n";
                                    *out << ind << "int it = *i;\n";
                                    *out << ind << "shared_reason.get()->insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "reasonForLiteral[-startVar]=shared_reason;\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"conflict on rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                                *out << ind << "handleConflict(-startVar, propagatedLiterals);\n";
                                *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                                *out << ind << "return;\n";

                            }else{
                                *out << ind++ << "for(unsigned i=0; i<tuplesF->size(); i++){\n";
                                    *out << ind << "int it = tuplesF->at(i);\n";
                                    *out << ind << "shared_reason.get()->insert(-it);\n";
                                *out << --ind << "}\n";
                                *out << ind << "reasonForLiteral[-startVar]=shared_reason;\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"conflict on rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                                *out << ind << "handleConflict(-startVar, propagatedLiterals);\n";
                                *out << --ind << "}else propagatedLiterals.push_back(1);\n";

                                *out << ind << "return;\n";
                            }
                        *out << --ind << "}else if(tuplesU->size()==1){\n";
                        ind++;
                            if(isSet){
                                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());\n";
                                bool checkFormat=checkTupleFormat(*body,"currentTuple",true);
                                *out << ind++ << "if(currentDecisionLevel>0){\n";
                                    *out << ind << "int itProp = currentTuple->getId();\n";
                                    printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                                    *out << ind++ << "for(auto i=tuplesF->begin(); i!=tuplesF->end(); i++){\n";
                                        *out << ind << "int it = *i;\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "shared_reason.get()->insert(startVar);\n";
                                    *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                    *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                        *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    #ifdef TRACE_REASON
                                        *out << ind << "std::cout << \"Reason of \"<<currentTuple->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                        *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                    #endif
                                *out << --ind << "}\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                                *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                if(checkFormat)
                                *out << --ind << "}\n";
                            }else{
                                *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));\n";
                                bool checkFormat=checkTupleFormat(*body,"currentTuple",true);
                                *out << ind++ << "if(currentDecisionLevel>0){\n";
                                    *out << ind << "int itProp = currentTuple->getId();\n";
                                    printGetValues(body->getPredicateName(),boundIndices,boundTerms,"f","tuplesF");
                                    *out << ind++ << "for(unsigned i=0; i<tuplesF->size(); i++){\n";
                                        *out << ind << "int it = tuplesF->at(i);\n";
                                        *out << ind << "shared_reason.get()->insert(-it);\n";
                                    *out << --ind << "}\n";
                                    *out << ind << "shared_reason.get()->insert(startVar);\n";
                                    *out << ind << "auto itReason = reasonForLiteral.emplace(itProp,shared_reason);\n";
                                    *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                        *out << ind-- << "itReason.first->second=shared_reason;\n";
                                    
                                    #ifdef TRACE_CONFLICT

                                        *out << ind << "if(!itReason.second && !itReason.first->second.get()->empty()) std::cout << \"Reason not updated\"<<std::endl;\n";
                                        *out << ind << "std::cout << \"Reason of \";printTuple(currentTuple);std::cout<<\": {\"<<std::endl;\n";
                                        *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); printTuple(factory.getTupleFromInternalID(id));}\n";
                                        *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                    #endif
                                *out << --ind << "}\n";
                                #ifdef TRACE_PROPAGATOR
                                    *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                #endif
                                *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                if(checkFormat)
                                *out << --ind << "}\n";
                            }
                        *out << --ind << "}\n";
                    *out << --ind << "}\n";
                *out << --ind << "}else{\n";
                ind++;
                    *out << ind++ << "if(tuples->size()>0){\n";
                        //support found for false head
                        *out << ind++ << "if(currentDecisionLevel>0){\n";
                            if(isSet){
                                *out << ind << "int it = *tuples->begin();\n";
                            }else{
                                *out << ind << "int it = tuples->at(0);\n";
                            }
                            *out << ind << "shared_reason.get()->insert(startVar);\n";
                            *out << ind << "reasonForLiteral[-it]=shared_reason;\n";
                            *out << ind << "handleConflict(-it, propagatedLiterals);\n";
                        *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                        *out << ind << "return;\n";

                    *out << --ind << "}else{\n";
                    ind++;
                        *out << ind << "shared_reason.get()->insert(startVar);\n";
                        if(isSet){
                            if(internalPredicates.count(body->getPredicateName())!=0){
                                *out << ind++ << "while(!tuplesU->empty()){\n";
                                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                                        *out << ind << "int it = *tuplesU->begin();\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-it,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                        #ifdef TRACE_REASON
                                            *out << ind << "std::cout << \"Reason of \"<<factory.getTupleFromInternalID(*tuplesU->begin())->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                        #endif
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(*tuplesU->begin()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}\n";
                            }else{
                                *out << ind++ << "for(auto itUndef = tuplesU->begin(); itUndef!=tuplesU->end();itUndef++){\n";
                                    *out << ind << "int it = *itUndef;\n";
                                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-it,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                        #ifdef TRACE_REASON
                                            *out << ind << "std::cout << \"Reason of \"<<factory.getTupleFromInternalID(it)->toString()<<\": {\"<<std::endl;\n";
                                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                        #endif
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(it),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}\n";

                            }
                        }else{
                            if(internalPredicates.count(body->getPredicateName())!=0){
                                *out << ind++ << "while(!tuplesU->empty()){\n";
                                    *out << ind << "int it = tuplesU->back();\n";
                                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-it,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                        #ifdef TRACE_REASON
                                            *out << ind << "std::cout << \"Reason of \"<<factory.getTupleFromInternalID(it)->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                        #endif
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(it),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}\n";
                            }else{
                                *out << ind++ << "for(unsigned i = 0; i<tuplesU->size();i++){\n";
                                    *out << ind << "int it = tuplesU->at(i);\n";
                                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                                        *out << ind << "auto itReason = reasonForLiteral.emplace(-it,shared_reason);\n";
                                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                                        #ifdef TRACE_REASON
                                            *out << ind << "std::cout << \"Reason of \"<<factory.getTupleFromInternalID(it)->toString()<<\": {\"<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                                        #endif
                                    *out << --ind << "}\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(factory.getTupleFromInternalID(it),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                *out << --ind << "}\n";
                            }
                        }
                    *out << --ind << "}\n";
                *out << --ind << "}\n";

            }
            while (closingPars>0){
                *out << --ind << "}\n";
                closingPars--;
            }

        }
        *out << --ind << "}\n";
    }else{
        *out << ind++ << "{\n";
        {
            bool isHeadSet = printGetValues(head->getPredicateName(),{},"","p","trueHeads");
            if(isHeadSet){
                *out << ind++ << "for(auto itTrueHead = trueHeads->begin();itTrueHead != trueHeads->end(); itTrueHead++){\n";
                    *out << ind << "const Tuple* currentHead = factory.getTupleFromInternalID(*itTrueHead);\n";
                    *out << ind << "if(eagerFacts.count(currentHead->getId())!=0) continue;\n";
                    std::unordered_set<std::string> boundVariables;
                    unsigned closingPars=0;
                    printAtomVariables(head,"currentHead","->",boundVariables,closingPars);
                    if(body->isBoundedLiteral(boundVariables)){
                        *out << ind << "Tuple* currentBody = factory.find({";
                        for(unsigned k=0; k<body->getAriety(); k++){
                            if(k>0)
                                *out << ",";
                            *out << body->getTermAt(k);
                        }
                        *out << "}, _"<<body->getPredicateName()<<");\n";
                        *out << ind++ << "if(!currentBody->isUndef() && !currentBody->isTrue()){\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"Conflict: at level -1 "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}else if(currentBody->isUndef()){\n";
                        ind++;
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }else{
                        std::vector<unsigned> boundIndices;
                        std::string boundTerms;
                        for(unsigned i=0;i<body->getAriety();i++){
                            if(!body->isVariableTermAt(i) || boundVariables.count(body->getTermAt(i))!=0){
                                boundIndices.push_back(i);
                                if(boundTerms!="")
                                    boundTerms+=", ";
                                boundTerms += body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            }
                        }
                        bool isBodySet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                        printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                        *out << ind++ << "if(tuples->size()==0){\n";
                            *out << ind++ << "if(tuplesU->size() == 0){\n";
                                //no support for true head
                                *out << ind << "propagatedLiterals.push_back(1);\n";
                                *out << ind << "return;\n";
                            *out << --ind << "}else if(tuplesU->size()==1){\n";
                            ind++;
                                if(isBodySet){
                                    *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());\n";
                                    bool checkFormat=checkTupleFormat(*body,"currentTuple",true);
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    if(checkFormat)
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));\n";
                                    bool checkFormat=checkTupleFormat(*body,"currentTuple",true);
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    if(checkFormat)
                                    *out << --ind << "}\n";
                                }
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";

                    }
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                *out << --ind << "}\n";
            }else{
                *out << ind++ << "for(unsigned i = 0;i < trueHeads->size(); i++){\n";
                    *out << ind << "const Tuple* currentHead = factory.getTupleFromInternalID(trueHeads->at(i));\n";
                    *out << ind << "if(eagerFacts.count(currentHead->getId())!=0) continue;\n";

                    std::unordered_set<std::string> boundVariables;
                    unsigned closingPars=0;
                    printAtomVariables(head,"currentHead","->",boundVariables,closingPars);
                    if(body->isBoundedLiteral(boundVariables)){
                        *out << ind << "Tuple* currentBody = factory.find({";
                        for(unsigned k=0; k<body->getAriety(); k++){
                            if(k>0)
                                *out << ",";
                            *out << body->getTermAt(k);
                        }
                        *out << "}, _"<<body->getPredicateName()<<");\n";
                        *out << ind++ << "if(!currentBody->isUndef() && !currentBody->isTrue()){\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"Conflict: at level -1 "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}else if(currentBody->isUndef()){\n";
                        ind++;
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propUndefined(currentBody,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }else{
                        std::vector<unsigned> boundIndices;
                        std::string boundTerms;
                        for(unsigned i=0;i<body->getAriety();i++){
                            if(!body->isVariableTermAt(i) || boundVariables.count(body->getTermAt(i))!=0){
                                boundIndices.push_back(i);
                                if(boundTerms!="")
                                    boundTerms+=", ";
                                boundTerms+=body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            }
                        }
                        bool isBodySet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                        printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                        *out << ind++ << "if(tuples->size()==0){\n";
                            *out << ind++ << "if(tuplesU->size() == 0){\n";
                                //no support for true head
                                *out << ind << "propagatedLiterals.push_back(1);\n";
                                *out << ind << "return;\n";
                            *out << --ind << "}else if(tuplesU->size()==1){\n";
                            ind++;
                                if(isBodySet){
                                    *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(*tuplesU->begin());\n";
                                    bool checkFormat=checkTupleFormat(*body,"currentTuple",true);
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    if(checkFormat)
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind << "const Tuple* currentTuple = factory.getTupleFromInternalID(tuplesU->at(0));\n";
                                    bool checkFormat=checkTupleFormat(*body,"currentTuple",true);
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                    #endif
                                    *out << ind << "propUndefined(currentTuple,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    if(checkFormat)
                                    *out << --ind << "}\n";
                                }
                            *out << --ind << "}\n";
                        *out << --ind << "}\n";

                    }
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                *out << --ind << "}\n";
            }
        }
        {
            bool isHeadSet = printGetValues(head->getPredicateName(),{},"","f","falseHeads");
            if(isHeadSet){
                *out << ind++ << "for(auto itFalseHead = falseHeads->begin();itFalseHead != falseHeads->end(); itFalseHead++){\n";
                    *out << ind << "const Tuple* currentHead = factory.getTupleFromInternalID(*itFalseHead);\n";
                    std::unordered_set<std::string> boundVariables;
                    unsigned closingPars=0;
                    printAtomVariables(head,"currentHead","->",boundVariables,closingPars);
                    if(body->isBoundedLiteral(boundVariables)){
                        *out << ind << "Tuple* currentBody = factory.find({";
                        for(unsigned k=0; k<body->getAriety(); k++){
                            if(k>0)
                                *out << ",";
                            *out << body->getTermAt(k);
                        }
                        *out << "}, _"<<body->getPredicateName()<<");\n";
                        *out << ind++ << "if(currentBody->isTrue()){\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"Conflict: at level -1 "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}else if(currentBody->isUndef()){\n";
                        ind++;
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }else{
                        std::vector<unsigned> boundIndices;
                        std::string boundTerms;
                        for(unsigned i=0;i<body->getAriety();i++){
                            if(!body->isVariableTermAt(i) || boundVariables.count(body->getTermAt(i))!=0){
                                boundIndices.push_back(i);
                                if(boundTerms!="")
                                    boundTerms+=", ";
                                boundTerms+=body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            }
                        }
                        bool isBodySet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                        printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                        *out << ind++ << "if(tuples->size()>0){\n";
                            //no support for true head
                            *out << ind << "propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            if(isBodySet){
                                if(internalPredicates.count(body->getPredicateName())!=0){
                                    *out << ind++ << "while(!tuplesU->empty()){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(*tuplesU->begin()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind++ << "for(auto itUndef = tuplesU->begin(); itUndef!=tuplesU->end();itUndef++){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(*itUndef),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }
                            }else{
                                if(internalPredicates.count(body->getPredicateName())!=0){
                                    *out << ind++ << "while(!tuplesU->empty()){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind++ << "for(unsigned i = 0; i<tuplesU->size();i++){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }
                            }
                        *out << --ind << "}\n";
                    }
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                *out << --ind << "}\n";
            }else{
                *out << ind++ << "for(unsigned i = 0;i < falseHeads->size(); i++){\n";
                    *out << ind << "const Tuple* currentHead = factory.getTupleFromInternalID(falseHeads->at(i));\n";
                    std::unordered_set<std::string> boundVariables;
                    unsigned closingPars=0;
                    printAtomVariables(head,"currentHead","->",boundVariables,closingPars);
                    if(body->isBoundedLiteral(boundVariables)){
                        *out << ind << "Tuple* currentBody = factory.find({";
                        for(unsigned k=0; k<body->getAriety(); k++){
                            if(k>0)
                                *out << ",";
                            *out << body->getTermAt(k);
                        }
                        *out << "}, _"<<body->getPredicateName()<<");\n";
                        *out << ind++ << "if(currentBody->isTrue()){\n";
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"Conflict: at level -1 "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}else if(currentBody->isUndef()){\n";
                        ind++;
                            #ifdef TRACE_PROPAGATOR
                                *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                            #endif
                            *out << ind << "propUndefined(currentBody,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << --ind << "}\n";
                    }else{
                        std::vector<unsigned> boundIndices;
                        std::string boundTerms;
                        for(unsigned i=0;i<body->getAriety();i++){
                            if(!body->isVariableTermAt(i) || boundVariables.count(body->getTermAt(i))!=0){
                                boundIndices.push_back(i);
                                if(boundTerms!="")
                                    boundTerms+=", ";
                                boundTerms+=body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            }
                        }
                        bool isBodySet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                        printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                        *out << ind++ << "if(tuples->size()>0){\n";
                            //no support for true head
                            *out << ind << "propagatedLiterals.push_back(1);\n";
                            *out << ind << "return;\n";
                        *out << --ind << "}else{\n";
                        ind++;
                            if(isBodySet){
                                if(internalPredicates.count(body->getPredicateName())!=0){
                                    *out << ind++ << "while(!tuplesU->empty()){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(*tuplesU->begin()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind++ << "for(auto itUndef = tuplesU->begin(); itUndef!=tuplesU->end();itUndef++){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(*itUndef),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }
                            }else{
                                if(internalPredicates.count(body->getPredicateName())!=0){
                                    *out << ind++ << "while(!tuplesU->empty()){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->back()),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }else{
                                    *out << ind++ << "for(unsigned i = 0; i<tuplesU->size();i++){\n";
                                        #ifdef TRACE_PROPAGATOR
                                            *out << ind << "std::cout<<\"propagation from rule: "<<r.getRuleId()<<"\"<<std::endl;\n";
                                        #endif
                                        *out << ind << "propUndefined(factory.getTupleFromInternalID(tuplesU->at(i)),false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                                    *out << --ind << "}\n";
                                }
                            }
                        *out << --ind << "}\n";
                    }
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                *out << --ind << "}\n";
            }

        }
        {
            bool isHeadSet = printGetValues(head->getPredicateName(),{},"","u","undefHeads");
            if(isHeadSet){
                *out << ind << "std::vector<std::pair<const Tuple*,bool>> props"<<r.getRuleId()<<";\n";
                *out << ind++ << "for(auto itUndefHead = undefHeads->begin(); itUndefHead != undefHeads->end(); itUndefHead++){\n";
                    *out << ind << "const Tuple* currentHead = factory.getTupleFromInternalID(*itUndefHead);\n";
                    std::unordered_set<std::string> boundVariables;
                    unsigned closingPars=0;
                    printAtomVariables(head,"currentHead","->",boundVariables,closingPars);
                    if(body->isBoundedLiteral(boundVariables)){
                        *out << ind << "const Tuple* currentBody = factory.find({";
                        for(unsigned i=0; i<body->getAriety(); i++){
                            if(i>0)
                                *out << ", ";
                            *out << body->getTermAt(i);
                        }
                        *out << "}, _"<<body->getPredicateName()<<");\n";
                        *out << ind++ << "if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))\n";
                            *out << ind-- << "props"<<r.getRuleId()<<".push_back({currentHead,true});\n";
                        *out << ind++ << "else if(currentBody!=NULL && currentBody->isTrue())\n";
                            *out << ind-- << "props"<<r.getRuleId()<<".push_back({currentHead,false});\n";
                    }else{
                        std::vector<unsigned> boundIndices;
                        std::string boundTerms;
                        for(unsigned i=0; i<body->getAriety(); i++){
                            if(!body->isVariableTermAt(i) || boundVariables.count(body->getTermAt(i))!=0){
                                boundIndices.push_back(i);
                                if(boundTerms!="")
                                    boundTerms+=", ";
                                boundTerms+=body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            }
                        }
                        bool isBodySet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                        printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                        *out << ind++ << "if(tuples->size() > 0)\n";
                            *out << ind-- << "props"<<r.getRuleId()<<".push_back({currentHead,false});\n";
                        *out << ind++ << "else if(tuplesU->size()==0)\n";
                            *out << ind-- << "props"<<r.getRuleId()<<".push_back({currentHead,true});\n";
                    }
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                *out << --ind << "}\n";
                *out << ind++ << "for(auto pair : props"<<r.getRuleId()<<")\n";
                    *out << ind-- << "propUndefined(pair.first,false,propagationStack,pair.second,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";


            }else{
                *out << ind++ << "for(unsigned i = 0; i < undefHeads->size();){\n";
                    *out << ind << "const Tuple* currentHead = factory.getTupleFromInternalID(undefHeads->at(i));\n";
                    std::unordered_set<std::string> boundVariables;
                    unsigned closingPars=0;
                    printAtomVariables(head,"currentHead","->",boundVariables,closingPars);
                    if(body->isBoundedLiteral(boundVariables)){
                        *out << ind << "const Tuple* currentBody = factory.find({";
                        for(unsigned i=0; i<body->getAriety(); i++){
                            if(i>0)
                                *out << ", ";
                            *out << body->getTermAt(i);
                        }
                        *out << "}, _"<<body->getPredicateName()<<");\n";
                        *out << ind++ << "if(currentBody == NULL || (!currentBody->isTrue() && !currentBody->isUndef()))\n";
                            *out << ind-- << "propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << ind++ << "else if(currentBody!=NULL && currentBody->isTrue())\n";
                            *out << ind-- << "propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << ind << "else i++;\n";
                    }else{
                        std::vector<unsigned> boundIndices;
                        std::string boundTerms;
                        for(unsigned i=0; i<body->getAriety(); i++){
                            if(!body->isVariableTermAt(i) || boundVariables.count(body->getTermAt(i))!=0){
                                boundIndices.push_back(i);
                                if(boundTerms!="")
                                    boundTerms+=", ";
                                boundTerms+=body->isVariableTermAt(i) || isInteger(body->getTermAt(i)) ? body->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+body->getTermAt(i)+"\")";
                            }
                        }
                        bool isBodySet = printGetValues(body->getPredicateName(),boundIndices,boundTerms,"p","tuples");
                        printGetValues(body->getPredicateName(),boundIndices,boundTerms,"u","tuplesU");
                        *out << ind++ << "if(tuples->size() > 0)\n";
                            *out << ind-- << "propUndefined(currentHead,false,propagationStack,false,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << ind++ << "else if(tuplesU->size()==0)\n";
                            *out << ind-- << "propUndefined(currentHead,false,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                        *out << ind << "else i++;\n";
                        }
                    while (closingPars>0){
                        *out << --ind << "}\n";
                        closingPars--;
                    }
                *out << --ind << "}\n";

            }
        }
        *out << --ind << "}\n";
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
        compileEagerSimpleRule(r,fromStarter);
        return;
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
                std::string sign = "startVar > 0";
                if(starter < r.getBodySize()){
                    start = &((aspc::Literal*)r.getFormulas()[starter])->getAtom();
                    startJoining=1;
                    if(r.getFormulas()[starter]->isLiteral() && !r.getFormulas()[starter]->isPositiveLiteral())
                        sign="startVar < 0";
                }else{
                    start = &r.getHead()[0];
                }

                *out << ind++ << "if(starter.getPredicateName() == _"<<start->getPredicateName()<<" && "<<sign<<"){\n";
                //*out << ind << "trace_msg(eagerprop,5,\"Evaluating constraint: "<<r.getRuleId()<<"\");\n";
                #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Constraint propagation\"<<std::endl;\n";
                #endif

                closingPars++;
                // if(checkTupleFormat(aspc::Literal(sign=="",*start),"starter",false))
                //     closingPars++;
                for(unsigned k = 0; k<start->getAriety(); k++){
                    if(start->isVariableTermAt(k) && boundVariables.count(start->getTermAt(k))==0){
                        *out << ind << "int "<<start->getTermAt(k)<<" = starter["<<k<<"];\n";
                        boundVariables.insert(start->getTermAt(k));
                    }else{
                        std::string term = start->isVariableTermAt(k) || isInteger(start->getTermAt(k)) ? start->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+start->getTermAt(k)+"\")";
                        *out << ind++ << "if("<<term<<" == starter["<<k<<"]){\n";
                        closingPars++;
                    }
                }

            }else{
                *out << ind++ << "{\n";
                closingPars++;
            }
            *out << ind << "const Tuple* tupleU = NULL;\n";
            *out << ind << "bool tupleUNegated = false;\n";
            *out << ind << "std::vector<std::pair<const Tuple*,bool>> internalProps;\n";
            unsigned remainingPars=closingPars;
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
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Evaluate propagation "<<r.getRuleId()<<"\"<<std::endl;\n";
            #endif
            *out << ind++ << "if(tupleU != NULL){\n";
                if(fromStarter){
                    *out << ind << "int itUndef = tupleU->getId();\n";
                    *out << ind << "int var = tupleUNegated ? 1 : -1;\n";
                    *out << ind << "var*=itUndef;\n";
                    #ifdef TRACE_PROPAGATOR
                        *out << ind << "std::cout<<\"compute reason for \"<<var<<std::endl;\n";
                        *out << ind << "if(reasonForLiteral.count(var) != 0) if(reasonForLiteral[var].get() == NULL)std::cout<<\"InMap But NULL\"<<std::endl; else std::cout<<\"InMap not null\"<<std::endl;\n";
                        *out << ind << "if(reasonForLiteral.count(var) == 0) std::cout<<\"NewReason\"<<std::endl;\n";
                    #endif
                    *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                        for(unsigned index = 0; index<oredered_body.size();index++){
                            if(oredered_body[index]->isLiteral()){
                                const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                                if(index>0 || startJoining == 0){
                                    *out << ind++ << "if(factory.find(*tuple"<<index<<") != NULL && tuple"<<index<<"!=tupleU){\n";
                                    *out << ind << "int it = tuple"<<index<<"->getId();\n";
                                }else{
                                    *out << ind++ << "{\n";
                                    *out << ind << "int it = starter.getId();\n";
                                }
                                    std::string sign = l->isNegated() ? "-1" : "1";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<\"add to reason of \"<<var<<\": \"<<it*"<<sign<<"<<std::endl;\n";
                                    #endif
                                    *out << ind << "shared_reason.get()->insert(it*"<<sign<<");\n";
                                *out << --ind << "}\n";
                            }
                        }

                        *out << ind << "auto itReason = reasonForLiteral.emplace(var,shared_reason);\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Saving reason of \"<<var<<std::endl;\n";
                        #endif
                        *out << ind++ << "if(!itReason.second && itReason.first->second.get()->empty())\n";
                            *out << ind-- << "itReason.first->second=shared_reason;\n";
                        #ifdef TRACE_REASON
                            *out << ind << "std::cout << \"Reason of \"<<tupleU->toString()<<\": {\"<<itReason.first->second.get()->size()<<std::endl;\n";
                            *out << ind << "for(int i=0;i<itReason.first->second.get()->size();i++){if(i>0) std::cout <<\",\"; int id = itReason.first->second.get()->at(i) > 0 ? itReason.first->second.get()->at(i) : -itReason.first->second.get()->at(i); std::cout << factory.getTupleFromInternalID(id)->toString();}\n";
                            *out << ind << "std::cout << \"}\"<<std::endl;\n";
                        #endif
                    *out << --ind << "}\n";
                }
                #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Constraint propagation "<<r.getRuleId()<<"\"<<std::endl;\n";
                #endif
                bool conditions=false;
                for(std::string pred : internalPredicates){
                    if(!conditions){
                        *out << ind++ << "if(";
                        conditions=true;
                    }else{
                        *out << " && ";
                    }
                    *out << "tupleU->getPredicateName() != _"<<pred;
                }
                if(conditions){
                    *out << ")\n";
                }
                *out << ind << "bool conflict = propUndefined(tupleU,tupleUNegated,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                if(conditions){
                    *out << --ind << "else internalProps.push_back({tupleU,tupleUNegated});\n";
                }
                // *out << ind << "UnorderedSet<int> rrrrrr;\n";
                // *out << ind << "std::unordered_set<int> visitedLiteralssssssss;\n";
                // *out << ind << "int it = tupleU->getId();\n";
                // *out << ind << "int sign = tupleUNegated == true ? 1 : -1;\n";
                // *out << ind << "explainExternalLiteral(it*sign,rrrrrr,visitedLiteralssssssss,true);\n";
            *out << --ind << "}else{\n";
            ind++;
            #ifdef TRACE_PROPAGATOR
                *out << ind << "std::cout<<\"Conflict On Constraint "<<r.getRuleId()<<"\"<<std::endl;\n";
            #endif
                if(fromStarter){
                    *out << ind << "std::shared_ptr<VectorAsSet<int>> shared_reason = std::make_shared<VectorAsSet<int>>();\n";
                    *out << ind++ << "if(currentDecisionLevel>0){\n";
                        for(unsigned index = 1; index<oredered_body.size();index++){
                            if(oredered_body[index]->isLiteral()){
                                const aspc::Literal* l =  (aspc::Literal*)oredered_body[index];
                                *out << ind++ << "if(tuple"<<index<<"!=NULL){\n";
                                    *out << ind << "int it = tuple"<<index<<"->getId();\n";
                                    #ifdef TRACE_PROPAGATOR
                                        *out << ind << "std::cout<<it<<\" \";tuple"<<index<<"->print();\n";
                                    #endif
                                    std::string sign = l->isNegated() ? "-1" : "1";
                                    *out << ind << "shared_reason.get()->insert(it*"<<sign<<");\n";
                                *out << --ind << "}\n";
                            }
                        }
                        *out << ind << "reasonForLiteral[-startVar]=shared_reason;\n";
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"call handle conflict\"<<std::endl;\n";
                        #endif
                        *out << ind << "handleConflict(-startVar, propagatedLiterals);\n";
                        *out << ind << "for(int i=0; i<internalProps.size(); i++) {int id =internalProps[i].second ? internalProps[i].first->getId() : -internalProps[i].first->getId();reasonForLiteral[id].get()->clear();}\n";

                    *out << --ind << "}else propagatedLiterals.push_back(1);\n";
                    *out << ind << "return;\n";
                }else{
                        #ifdef TRACE_PROPAGATOR
                            *out << ind << "std::cout<<\"Conflict at level -1\"<<std::endl;\n";
                        #endif
                    *out << ind << "propagatedLiterals.push_back(1);\n";
                }
            *out << --ind << "}\n";
            while(closingPars>0){
                closingPars--;
                *out << --ind << "}\n";
                if(closingPars == remainingPars){
                    *out << ind++ << "for(auto pair : internalProps)\n";
                        *out << ind-- << "propUndefined(pair.first,pair.second,propagationStack,true,propagatedLiterals,remainingPropagatingLiterals, solver, propComparison, minConflict, minHeapSize, maxHeapSize, heapSize);\n";
                }
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
                            *out << ind++ << "if(tupleU && tupleU->getPredicateName() == _"<<l->getPredicateName()<<"){\n;";
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
                            *out << "}, _" << l->getPredicateName() << ", true);\n";
                            *out << ind++ << "if(tupleU && tupleU->getPredicateName() == _"<<l->getPredicateName()<<"){\n;";
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
                            *out << "}, _" << l->getPredicateName() << ", true);\n";
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
                            *out << ind++ << "if(tupleU && !tupleUNegated && tupleU->getPredicateName() == _"<<l->getPredicateName()<<") {\n";
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


                *out << "}, _" << r.getHead().front().getPredicateName() << "));\n";
                *out << ind++ << "if(insertResult.second){\n";

                if (p.hasConstraint()) {
                    for (unsigned i = 0; i < body.size(); i++) {
                        if (body[joinOrder[i]]->isPositiveLiteral()) {
                            *out << ind << "insertResult.first->addPositiveReason(tuple" << i << ");\n";
                        } else if (body[joinOrder[i]]->isLiteral()) {
                            aspc::Literal* l = (aspc::Literal*) body[joinOrder[i]];
                            *out << ind << "insertResult.first->addNegativeReason(Tuple({";
                            printLiteralTuple(l);
                            *out << "}, _" << l->getPredicateName() << ", true));\n";
                        }
                    }
                }

                for (const std::string& auxMapName : predicateToAuxiliaryMaps[r.getHead().front().getPredicateName()]) {
                    *out << ind << "p" << auxMapName << ".insert2(*w" << r.getHead().front().getPredicateName() << ".getTuples().back());\n";
                }

                *out << --ind << "}\n";
            } else {
                #ifdef TRACE_PROPAGATOR
                    *out << ind << "std::cout<<\"constraint failed\"<<std::endl;\n";
                #endif
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
                                    *out << "}, _" << l->getPredicateName() << ", true);\n";
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
                    // *out << ind << "std::cout<<\"constraint failed\"<<std::endl;\n";

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
                                    int BITSETSIZE = coveredVariableIndexes.size()*CHAR_BIT*sizeof(int);
                                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> p" << mapVariableName << "({";
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
                                    int BITSETSIZE = coveredVariableIndexes.size()*CHAR_BIT*sizeof(int);
                                    *out << ind << "AuxMap<"<<BITSETSIZE<<"> " << mapVariableName << "({";
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