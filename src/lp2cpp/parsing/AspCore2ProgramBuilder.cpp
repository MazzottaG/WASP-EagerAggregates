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
 *  Copyright 2016 Bernardo Cuteri, Francesco Ricca.
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
 * File:   AspCore2ProgramBuilder.cpp
 * Author: bernardo
 *
 * Created on June 16, 2016, 2:53 PM
 */

#include "AspCore2ProgramBuilder.h"
#include <iostream>
#include <cstring>
#include <bits/unordered_map.h>
#include "../language/ArithmeticRelation.h"
#include "../language/Aggregate.h"
#include "../language/ArithmeticRelationWithAggregate.h"
#include "../utils/SharedFunctions.h"
#include "../utils/AggrSetPredicate.h"

using namespace std;

AspCore2ProgramBuilder::AspCore2ProgramBuilder() : naf(false), inequalitySign(aspc::UNASSIGNED),inequalitySignAggregate(aspc::UNASSIGNED) {
}

void AspCore2ProgramBuilder::buildExpression() {
    if (buildingTerms.size() == 1) {
        expression = aspc::ArithmeticExpression(buildingTerms[0]);
    } else {
        expression = aspc::ArithmeticExpression(buildingTerms[0], buildingTerms[1], arithOp);
    }
    buildingTerms.clear();
}

void AspCore2ProgramBuilder::onAggregate(bool negation) {
    isNegated=negation;
}

void AspCore2ProgramBuilder::clearAggregateFields(){

    aggreagateLiterals.clear();
    aggregateVariables.clear();
    aggregateFunction="None";
    aggreagateInequalities.clear();
    inequalitySign=aspc::UNASSIGNED;
    isNegated=false;
    isLower=false;
    buildingAggregate=false;
}
void AspCore2ProgramBuilder::onAggregateElement() {

    buildingAggregate=false;
}

void AspCore2ProgramBuilder::onAggregateFunction(char* function) {
    this->aggregateFunction=function;
    buildingAggregate=true;
}

void AspCore2ProgramBuilder::onAggregateGroundTerm(char* groundTerm, bool negated) {

}

void AspCore2ProgramBuilder::onAggregateLowerGuard() {

    inequalitySignAggregate = inequalitySign;
    guard = expression;
    //guard alreay built aggregate not read
    isLower=true;
}

void AspCore2ProgramBuilder::onAggregateNafLiteral() {

    if(predicateName == ""){

        if (buildingTerms.size() == 1) {
            aggreagateInequalities.push_back(aspc::ArithmeticRelation(expression, aspc::ArithmeticExpression(buildingTerms[0]), inequalitySign));
        } else {
            aggreagateInequalities.push_back(aspc::ArithmeticRelation(expression, aspc::ArithmeticExpression(buildingTerms[0], buildingTerms[1], arithOp), inequalitySign));
        }
    }else{

        this->aggreagateLiterals.push_back(aspc::Literal(naf,aspc::Atom(predicateName,buildingTerms)));
        predicateName="";
    }

    buildingTerms.clear();

}

void AspCore2ProgramBuilder::onAggregateUnknownVariable() {

}

void AspCore2ProgramBuilder::onAggregateUpperGuard() {
    inequalitySignAggregate = inequalitySign;
    this->buildExpression();
    guard=expression;
    isLower=false;
}

void AspCore2ProgramBuilder::onAggregateVariableTerm(char* variableTerm) {
    this->aggregateVariables.push_back(variableTerm);

}

void AspCore2ProgramBuilder::onArithmeticOperation(char op) {

    //std::cout<<"on arithmetic operation"<<std::endl;
    arithOp = op;
}

void AspCore2ProgramBuilder::onAtom(bool) {

    //std::cout<<"on atom"<<std::endl;
}

void AspCore2ProgramBuilder::onBody() {


    //std::cout<<"on body"<<std::endl;
}

void AspCore2ProgramBuilder::onBodyLiteral() {

    if (inequalitySign != aspc::UNASSIGNED) {
        if(aggregateFunction != "None"){

            inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(isLower,guard,aspc::Aggregate(aggreagateLiterals,aggreagateInequalities,aggregateVariables,aggregateFunction),inequalitySignAggregate,isNegated));
            clearAggregateFields();
        }
        else if (buildingTerms.size() == 1) {
            inequalities.push_back(aspc::ArithmeticRelation(expression, aspc::ArithmeticExpression(buildingTerms[0]), inequalitySign));
        } else {
            inequalities.push_back(aspc::ArithmeticRelation(expression, aspc::ArithmeticExpression(buildingTerms[0], buildingTerms[1], arithOp), inequalitySign));
        }

    } else {

        buildingBody.push_back(aspc::Literal(naf, aspc::Atom(predicateName, buildingTerms)));
        if (arietyMap.count(predicateName)) {
            //assert((*arietyMap)[predicateName] == buildingTerms->size());
        } else {
            arietyMap[predicateName] = buildingTerms.size();
        }
    }
    inequalitySign = aspc::UNASSIGNED;
    buildingTerms.clear();
    naf = false;
}

void AspCore2ProgramBuilder::onBuiltinAtom() {

}

void AspCore2ProgramBuilder::onChoiceAtom() {

}

void AspCore2ProgramBuilder::onChoiceElement() {

}

void AspCore2ProgramBuilder::onChoiceElementAtom() {

}

void AspCore2ProgramBuilder::onChoiceElementLiteral() {

}

void AspCore2ProgramBuilder::onChoiceLowerGuard() {

}

void AspCore2ProgramBuilder::onChoiceUpperGuard() {

}
// void AspCore2ProgramBuilder::onConstraintFirstRewriting() {

//     aspc::Rule constraint(buildingHead, buildingBody, inequalities,std::vector<aspc::ArithmeticRelationWithAggregate>(inequalitiesWithAggregate), true,!analyzeDependencyGraph);
//     rewrittenProgram.addRule(constraint);
//     clearData();
// }
void AspCore2ProgramBuilder::onConstraint() {

    int size=program.getRules().size();

    std::unordered_set<std::string> boundVariables;
    for (const aspc::Literal& l : buildingBody) {
        for(int term=0;term<l.getAriety();term++){
            if(l.isVariableTermAt(term)){
                boundVariables.insert(l.getTermAt(term));
            }
        }
        int currentBodyId = predicateIDs.size();
        unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
        if (i != predicateIDs.end())
            currentBodyId = i->second;
        else {
            predicateIDs[l.getPredicateName()] = currentBodyId;
            vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
        }
    }
    for(const aspc::ArithmeticRelationWithAggregate& aggrRelation : inequalitiesWithAggregate){
        for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
            for(int term=0;term<l.getAriety();term++){
                if(l.isVariableTermAt(term)){
                    boundVariables.insert(l.getTermAt(term));
                }
            }
            int currentBodyId = predicateIDs.size();
            unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
            if (i != predicateIDs.end())
                currentBodyId = i->second;
            else {
                predicateIDs[l.getPredicateName()] = currentBodyId;
                vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
            }
        }
    }
    for (const aspc::Literal& l : buildingBody) {
        program.addPredicate(l.getPredicateName(), l.getAriety());
    }
    for(const aspc::ArithmeticRelation& inequality : inequalities){
        if(inequality.isBoundedValueAssignment(boundVariables)){
            boundVariables.insert(inequality.getAssignedVariable(boundVariables));
        }
    }
    aspc::Rule constraint(buildingHead, buildingBody, inequalities,std::vector<aspc::ArithmeticRelationWithAggregate>(inequalitiesWithAggregate), true,!analyzeDependencyGraph);
    program.addRule(constraint);

    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();

}
// void AspCore2ProgramBuilder::normalizeArithmeticRelationsWithAggregate(){
//     for(aspc::ArithmeticRelationWithAggregate& relation: inequalitiesWithAggregate){
//         std::unordered_set<std::string> sharedVars;
//         for(const aspc::Literal& l: relation.getAggregate().getAggregateLiterals()){
//             for(int i=0;i<l.getAriety();i++){
//                 if(l.isVariableTermAt(i)){
//                     sharedVars.insert(l.getTermAt(i));
//                 }
//             }
//         }
//         std::unordered_set<std::string> trueSharedVar;
//         for(std::string v : sharedVars){
//             bool found=false;
//             for(const aspc::Literal& l : buildingBody){
//                 if(l.getVariables().count(v) > 0){
//                     found=true;
//                     break;
//                 }
//             }
//             if(found)
//                 trueSharedVar.insert(v);
//         }
//         relation.normalizeAggregateRelations(trueSharedVar);
//     }

// }

void AspCore2ProgramBuilder::onDirective(char*, char*) {

}

void AspCore2ProgramBuilder::onEqualOperator() {
    inequalitySign = aspc::EQ;
    if(aggregateFunction == "None" || buildingAggregate)
        buildExpression();
}

void AspCore2ProgramBuilder::onExistentialAtom() {

}

void AspCore2ProgramBuilder::onExistentialVariable(char*) {

}

void AspCore2ProgramBuilder::onFunction(char*, int) {

}

void AspCore2ProgramBuilder::onGreaterOperator() {
    inequalitySign = aspc::GT;
    if(aggregateFunction == "None"|| buildingAggregate)
        buildExpression();
}

void AspCore2ProgramBuilder::onGreaterOrEqualOperator() {

    inequalitySign = aspc::GTE;
    if(aggregateFunction == "None"|| buildingAggregate)
        buildExpression();
}

void AspCore2ProgramBuilder::onHead() {
}

void AspCore2ProgramBuilder::onHeadAtom() {

    buildingHead.push_back(aspc::Atom(predicateName, buildingTerms));
    if (arietyMap.count(predicateName)) {
        //assert((*arietyMap)[predicateName] == buildingTerms->size());
    } else {
        arietyMap[predicateName] = buildingTerms.size();
    }
    buildingTerms.clear();
}

void AspCore2ProgramBuilder::onLessOperator() {

    inequalitySign = aspc::LT;
    if(aggregateFunction == "None" || buildingAggregate)
        buildExpression();
}

void AspCore2ProgramBuilder::onLessOrEqualOperator() {

    inequalitySign = aspc::LTE;
    if(aggregateFunction == "None"|| buildingAggregate)
        buildExpression();
}

void AspCore2ProgramBuilder::onNafLiteral(bool naf) {
        this->naf = naf;
}

void AspCore2ProgramBuilder::onPredicateName(char* predicateName) {

    //why the following does not work?
    //this->predicateName = predicateName;
    this->predicateName = predicateName;
}

void AspCore2ProgramBuilder::onQuery() {

}
//build aggr_set and aggr_id rule
// std::vector<aspc::Literal> AspCore2ProgramBuilder::rewriteAggregate(std::vector<aspc::Literal >& bodyLiterals,const std::unordered_set<string>& bodyVars,const aspc::ArithmeticRelationWithAggregate& aggrRelation,bool generateAuxVal){
// }
// std::vector<std::string> AspCore2ProgramBuilder::getSupPredicatesForHead(std::string head){
// }
// bool AspCore2ProgramBuilder::isSupPredicateForHead(std::string sup,std::string head){
// }
// const aspc::Literal* AspCore2ProgramBuilder::getSupportingHead(std::string pred){
// }
// void AspCore2ProgramBuilder::rewriteRule(int ruleIndex,bool addDomBody){
// }
// void AspCore2ProgramBuilder::onRuleFirstRewriting(){
// }
void AspCore2ProgramBuilder::onRule() {
    if (buildingBody.empty() && inequalitiesWithAggregate.empty()) {
        program.addFact(buildingHead.back());
    } else {
        aspc::Rule rule = aspc::Rule(buildingHead, buildingBody, inequalities,inequalitiesWithAggregate, true,!analyzeDependencyGraph);
        program.addRule(rule);

        //adding edges to dependency graph
        for (const aspc::Atom& a : buildingHead) {
            int currentHeadId = predicateIDs.size();
            unordered_map<string, int>::iterator i = predicateIDs.find(a.getPredicateName());
            if (i != predicateIDs.end())
                currentHeadId = i->second;
            else {
                predicateIDs[a.getPredicateName()] = currentHeadId;
                vertexByID[currentHeadId] = Vertex(currentHeadId, a.getPredicateName());
            }
            vertexByID[currentHeadId].rules.push_back(rule.getRuleId());
            for (const aspc::Literal& l : buildingBody) {
                int currentBodyId = predicateIDs.size();
                unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
                if (i != predicateIDs.end())
                    currentBodyId = i->second;
                else {
                    predicateIDs[l.getPredicateName()] = currentBodyId;
                    vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                }

                vertexByID[currentBodyId].rules.push_back(rule.getRuleId());
                graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
            }
            for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: inequalitiesWithAggregate){
                for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
                    int currentBodyId = predicateIDs.size();
                    unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
                    if (i != predicateIDs.end())
                        currentBodyId = i->second;
                    else {
                        predicateIDs[l.getPredicateName()] = currentBodyId;
                        vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                    }
                    vertexByID[currentBodyId].rules.push_back(rule.getRuleId());
                    graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
                }
            }
        }

    }
    //add predicates to program
    for (const aspc::Atom& a : buildingHead) {
        program.addPredicate(a.getPredicateName(), a.getAriety());
    }
    for (const aspc::Literal& l : buildingBody) {
        program.addPredicate(l.getPredicateName(), l.getAriety());
    }
    for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: inequalitiesWithAggregate){
        for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
            program.addAggregatePredicate(l.getPredicateName(), l.getAriety());
        }
    }
    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
}

void AspCore2ProgramBuilder::onTerm(int) {

}

void AspCore2ProgramBuilder::onTerm(char* value) {
    buildingTerms.push_back(value);

}

void AspCore2ProgramBuilder::onTermDash() {
    buildingTerms.back()="-"+buildingTerms.back();

}

void AspCore2ProgramBuilder::onTermParams() {

}

void AspCore2ProgramBuilder::onTermRange(char*, char*) {

}

void AspCore2ProgramBuilder::onUnequalOperator() {

    inequalitySign = aspc::NE;
    //if(aggregateFunction!="None")
        buildExpression();

}

void AspCore2ProgramBuilder::onUnknownVariable() {
    buildingTerms.push_back("_");
}

void AspCore2ProgramBuilder::onWeakConstraint() {

}

void AspCore2ProgramBuilder::onWeightAtLevels(int, int, int) {

}
// void AspCore2ProgramBuilder::labelComponents(std::unordered_set<unsigned>& labeledComponent,const std::vector<std::vector<int>>& scc,const aspc::Program& programToLabel){
// }
// void AspCore2ProgramBuilder::analyzeInputProgram(){
// }
// void AspCore2ProgramBuilder::buildConstraintDuplicateHeads(){
// }
void AspCore2ProgramBuilder::clearData(){
    buildingHead.clear();
    buildingBody.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
}

//aggregateBodyVariables must contains also variables appearing in the aggregate guard
// std::pair<bool,std::pair<std::string,AggrSetPredicate>> AspCore2ProgramBuilder::buildBody(std::unordered_set<std::string> aggregateBodyVariables,const aspc::Rule& r,std::string auxValPred,std::vector<std::string> auxValTerm,int ruleId){
// }
// std::pair<bool,std::pair<std::string,AggrSetPredicate>> AspCore2ProgramBuilder::buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation,std::string domPred,std::vector<std::string> domTerm,int ruleId){
// }
// void AspCore2ProgramBuilder::rewriteConstraint(const aspc::Rule& r){
// }
// std::vector<std::string> AspCore2ProgramBuilder::writeAggrIdRule(std::pair<bool,std::pair<std::string,AggrSetPredicate>> body,std::pair<bool,std::pair<std::string,AggrSetPredicate>> aggrSet,const aspc::Rule& r){
// }
// void AspCore2ProgramBuilder::rewriteRuleWithCompletion(const aspc::Rule& r,int ruleId){
// }
// void AspCore2ProgramBuilder::addManualDependecy(){
// }
aspc::EagerProgram & AspCore2ProgramBuilder::getRewrittenProgram() {
    return rewrittenProgram;
}
aspc::EagerProgram & AspCore2ProgramBuilder::getCompilingProgram() {
    return programWithCompletion;
}
const std::vector<std::vector<int>>&  AspCore2ProgramBuilder::getSubPrograms() {
    return rewrittenRuleToCompletionSubProgram;
}
std::vector<aspc::Rule>  AspCore2ProgramBuilder::getSubProgramsForRule(int id) {
    std::vector<aspc::Rule> res;
    for(int rId: rewrittenRuleToCompletionSubProgram[id]){
        res.push_back(programWithCompletion.getRule(rId));
    }
    return res;
}
// aspc::ArithmeticRelationWithAggregate AspCore2ProgramBuilder::buildAggrSetRule(const aspc::Rule& r,std::string& domPred){
// }
// aspc::Literal AspCore2ProgramBuilder::buildBodyRule(const aspc::Rule& r,const aspc::ArithmeticRelationWithAggregate& newAggregate,std::string& auxValPredName){
// }
// void AspCore2ProgramBuilder::rewritSourceProgram(){
// }
bool AspCore2ProgramBuilder::splitProgram(std::unordered_set<int>& fakeLazyRuleIndices,const std::vector<std::vector<int>>& scc){
    const auto & rules = program.getRules();
    //Check if it is stratified or not
    bool isStratified=true;
    for(int component = 0 ; component < scc.size() && isStratified; component++){
        std::unordered_set<std::string> componentPredicateNames;
        for(int i=0;i<scc[component].size();i++){
            auto it = vertexByID.find(scc[component][i]);
            if(it != vertexByID.end()){
                componentPredicateNames.insert(it->second.name);
            }
        }
        for(std::string headPredicate : componentPredicateNames){
            for(std::string bodyPredicate : componentPredicateNames){
                for(int i=0; i < rules.size() && isStratified; i++){
                    if(!rules[i].isConstraint() && rules[i].getHead()[0].getPredicateName() == headPredicate){
                        for(const aspc::Literal& l : rules[i].getBodyLiterals()){
                            if(l.isNegated() && l.getPredicateName() == bodyPredicate){
                                isStratified=false;
                                break;
                            }
                        }
                    }
                }
                if(!isStratified) break;
            }
            if(!isStratified) break;
        }
    }

    if(!isStratified){std::cout<<"WARNING:  Compiling program is not stratified and correctness is not guranteed"<<std::endl;}
    if(isStratified && scc.size() > 0){
        //find fake lazy subProgram
        std::unordered_map<int,int> predicateToComponent;
        for(int component = 0 ; component < scc.size(); component++){
            for( int predicateId : scc[component]){
                predicateToComponent[predicateId]=component;
            }
        }
        std::vector<int> stackComponents;
        std::unordered_set<int> labeledComponents;
        for(int i=0; i < rules.size(); i++){
            if(rules[i].isConstraint()){
                // rules[i].print();
                for(const aspc::Literal& l : rules[i].getBodyLiterals()){
                    // l.print();
                    auto it = predicateIDs.find(l.getPredicateName());
                    if(it!=predicateIDs.end() && predicateToComponent.count(it->second)!=0){
                        int component = predicateToComponent[it->second];
                        if(labeledComponents.count(component) == 0){
                            labeledComponents.insert(component);
                            stackComponents.push_back(component);
                        }            

                    }
                }
            }
        }

        while (!stackComponents.empty()){
            int component = stackComponents.back();
            stackComponents.pop_back();
            for(int predId : scc[component]){

                auto it = vertexByID.find(predId);
                if(it!=vertexByID.end()){
                    for(int i=0; i < rules.size(); i++){
                        if(!rules[i].isConstraint() && rules[i].getHead()[0].getPredicateName() == it->second.name){
                            for(const aspc::Literal& l : rules[i].getBodyLiterals()){
                                auto itToLabel = predicateIDs.find(l.getPredicateName());
                                if(itToLabel!=predicateIDs.end()){
                                    int componentToLabel = predicateToComponent[itToLabel->second];
                                    if(labeledComponents.count(componentToLabel) == 0){
                                        labeledComponents.insert(componentToLabel);
                                        stackComponents.push_back(componentToLabel);
                                    }            
                                }
                            }           
                        }
                    }    
                }            
            }
        }

        for(int i=0; i < rules.size(); i++){
            if(!rules[i].isConstraint()){
                auto it = predicateIDs.find(rules[i].getHead()[0].getPredicateName());
                if(it!=predicateIDs.end()){
                    if(labeledComponents.count(predicateToComponent[it->second]) == 0){
                        fakeLazyRuleIndices.insert(i);
                    }
                }
            }
        }
    }
    return isStratified;
}
void AspCore2ProgramBuilder::buildCompilablePrograms(){

    std::vector<std::vector<int>> scc = graphWithTarjanAlgorithm.SCC();
    std::unordered_set<int> fakeLazyRuleIndices;
    splitProgram(fakeLazyRuleIndices,scc);
    
    auto rules = program.getRules();
    for(int ruleIndex : fakeLazyRuleIndices){
        endProgram.addRule(rules[ruleIndex],true);
    }
    for(int i=0; i < rules.size(); i++){
        if(fakeLazyRuleIndices.count(i)==0){
            if(!rules[i].isConstraint()){
                printingPredicate.insert(rules[i].getHead()[0].getPredicateName());
            }
            if(!rules[i].containsAggregate()){
                rewrittenProgram.addRule(rules[i]);
                rewrittenProgram.addGeneratorDependenciesForRule(rules[i]);
            }else{
                //Rule Rewriting
                //Build body rules
                clearData();
                std::unordered_set<std::string> bodyVariables;
                for(const aspc::Literal& l : rules[i].getBodyLiterals()){
                    l.addVariablesToSet(bodyVariables);
                }
                for(const aspc::ArithmeticRelation& ineq: rules[i].getArithmeticRelations()){
                    ineq.addVariablesToSet(bodyVariables);
                }

                bool addedValuePredicate=false;
                //adding value predicate for bound value assignment with aggregate
                const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &rules[i].getArithmeticRelationsWithAggregate()[0];
                if(!aggregateRelation->isBoundedRelation(bodyVariables)){
                    if(!aggregateRelation->isBoundedValueAssignment(bodyVariables) || aggregateRelation->isNegated() || aggregateRelation->getComparisonType() != aspc::EQ){
                        std::cout << "ERROR: Aggregate Relation not bound"<<std::endl;
                        exit(180);
                    }

                    //aggregate as bound value assignment 
                    std::string assignedVariable = aggregateRelation->getAssignedVariable(bodyVariables);
                    if(assignedVariable == ""){
                        std::cout << "ERROR: Unable to find assigned variable for aggregate"<<std::endl;
                        exit(180);
                    }else{
                        std::string valuePredicatName = "aux_val"+std::to_string(valuesPredicates.size());
                        valuesPredicates.insert(valuePredicatName);
                        internalPredicates.insert(valuePredicatName);

                        rules[i].addBodyLiteral(aspc::Literal(false,aspc::Atom(valuePredicatName,{assignedVariable})));
                        addedValuePredicate=true;
                    }
                }
                //body literal data
                AssignedBody assignedBody;
                std::string bodyPredicateName = "";

                std::unordered_set<std::string> sharedVars;

                std::unordered_set<std::string> aggregateBodyVariables;
                aggregateRelation->addVariablesToSet(aggregateBodyVariables);                
                for(const aspc::Atom& head : rules[i].getHead()){
                    for(int k=0; k<head.getAriety(); k++){
                        if(head.isVariableTermAt(k) && sharedVars.count(head.getTermAt(k))==0){
                            sharedVars.insert(head.getTermAt(k));
                            assignedBody.addTerm(head.getTermAt(k));
                        }
                    }
                }
                for(const aspc::Literal& l : rules[i].getBodyLiterals()){
                    for(int k=0; k<l.getAriety(); k++){
                        if(l.isVariableTermAt(k) && aggregateBodyVariables.count(l.getTermAt(k))!=0){
                            if(sharedVars.count(l.getTermAt(k))==0){
                                sharedVars.insert(l.getTermAt(k));
                                assignedBody.addTerm(l.getTermAt(k));
                            }
                        } 
                    }
                    buildingBody.push_back(l);
                    assignedBody.addLiteral(l);
                }
                for(const aspc::ArithmeticRelation& ineq: rules[i].getArithmeticRelations()){
                    for(const aspc::ArithmeticExpression exp : std::vector<aspc::ArithmeticExpression>({ineq.getLeft(),ineq.getRight()})){
                        for(std::string term : exp.getAllTerms()){
                            if(isVariable(term) && aggregateBodyVariables.count(term)!=0){
                                if(sharedVars.count(term)==0){
                                    sharedVars.insert(term);
                                    assignedBody.addTerm(term);
                                }
                            }
                        }
                    }
                    inequalities.push_back(ineq);
                    assignedBody.addInequality(ineq);
                }
                bool iffCase = rules[i].getBodyLiterals().size() == 1 && rules[i].getArithmeticRelations().size() == 0 /*&& !addedValuePredicate*/;
                if(iffCase){
                    const aspc::Literal* l = &rules[i].getBodyLiterals()[0];
                    if(l->isNegated()) iffCase = false;
                    else{
                        if(l->getTerms().size() != assignedBody.getTerms().size()) iffCase=false;
                        else{
                            for(int i=0;i<assignedBody.getTerms().size() && iffCase;i++){
                                bool found=false;
                                for(int j=0;j<l->getAriety();j++){
                                    if(assignedBody.getTerms()[i]==l->getTerms()[j]){
                                        found=true;
                                        break;
                                    }
                                }
                                if(!found) iffCase = false;
                            }
                            for(int i=0;i<l->getAriety() && iffCase;i++){
                                bool found=false;
                                for(int j=0;j<assignedBody.getTerms().size();j++){
                                    if(assignedBody.getTerms()[j]==l->getTerms()[i]){
                                        found=true;
                                        break;
                                    }
                                }
                                if(!found) iffCase = false;
                            }
                            if(iffCase){
                                bodyPredicateName=l->getPredicateName();
                                assignedBody.clearLiterals();
                                assignedBody.clearIneqs();
                                assignedBody.setTerms(l->getTerms());
                            }
                        }
                    }
                }
                if(!iffCase && rules[i].getBodyLiterals().size() > 0){
                    //check for already declared body predicate
                    for(auto pair: bodyPredicateToAssignedBody){
                        if(pair.second == assignedBody){
                            bodyPredicateName = pair.first;
                            assignedBody = pair.second;
                            break;
                        }
                    }
                    if(bodyPredicateName==""){
                        bodyPredicateName = "body_"+std::to_string(bodyPredicates.size());
                        bodyPredicates.insert(bodyPredicateName);
                        
                        bodyPredicateToAssignedBody[bodyPredicateName]=assignedBody;
                        buildingHead.push_back(aspc::Atom(bodyPredicateName,assignedBody.getTerms()));
                        aspc::Rule bodyRule(buildingHead,buildingBody,inequalities,true);
                        rewrittenProgram.addGeneratorDependenciesForRule(bodyRule);
                        rewrittenProgram.addRule(bodyRule);
                    }
                }

                clearData();

                //build rule for aggregate set
                AssignedBody aggregateSetAssignedBody;
                std::string aggregateSetPredicateName="";
                
                std::unordered_set<std::string> distinctAggregateSetTerms;
                for(std::string variable:aggregateRelation->getAggregate().getAggregateVariables()){
                    if(distinctAggregateSetTerms.count(variable)==0){
                        distinctAggregateSetTerms.insert(variable);
                        aggregateSetAssignedBody.addTerm(variable);
                    }
                }
                for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
                    aggregateSetAssignedBody.addLiteral(l);
                    buildingBody.push_back(l);
                    for(int k=0;k<l.getAriety();k++){
                        if(l.isVariableTermAt(k) && bodyVariables.count(l.getTermAt(k))!=0){
                            if(distinctAggregateSetTerms.count(l.getTermAt(k))==0){
                                distinctAggregateSetTerms.insert(l.getTermAt(k));
                                aggregateSetAssignedBody.addTerm(l.getTermAt(k));
                            }
                        }                        
                    }
                }

                for(const aspc::ArithmeticRelation& ineq : aggregateRelation->getAggregate().getAggregateInequalities()){
                    aggregateSetAssignedBody.addInequality(ineq);
                    inequalities.push_back(ineq);
                    for(const aspc::ArithmeticExpression& exp : std::vector<aspc::ArithmeticExpression>({ineq.getLeft(),ineq.getRight()})){
                        for(std::string variable: exp.getAllTerms()){
                            if(isVariable(variable) && bodyVariables.count(variable)!=0){
                                if(distinctAggregateSetTerms.count(variable)==0){
                                    distinctAggregateSetTerms.insert(variable);
                                    aggregateSetAssignedBody.addTerm(variable);
                                }
                            }
                        }
                    }
                }
                //check domBody predicate needed
                bool neededDomBodyPredicate=false;
                std::unordered_set<std::string> positiveAggrVars;
                for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
                    if(l.isPositiveLiteral())
                        l.addVariablesToSet(positiveAggrVars);
                }
                for(const aspc::ArithmeticRelation& ineq : aggregateRelation->getAggregate().getAggregateInequalities()){
                    if(ineq.isBoundedValueAssignment(positiveAggrVars)){
                        positiveAggrVars.insert(ineq.getAssignedVariable(positiveAggrVars));
                    }
                }
                int size=0;
                while(size!=positiveAggrVars.size()){
                    size = positiveAggrVars.size();
                    for(const aspc::ArithmeticRelation& ineq : aggregateRelation->getAggregate().getAggregateInequalities()){
                        if(ineq.isBoundedValueAssignment(positiveAggrVars)){
                            positiveAggrVars.insert(ineq.getAssignedVariable(positiveAggrVars));
                        }
                    }
                }
                
                for(const aspc::Literal& l : aggregateRelation->getAggregate().getAggregateLiterals()){
                    if(l.isNegated() && !l.isBoundedLiteral(positiveAggrVars)){
                        neededDomBodyPredicate=true;
                        break;
                    }
                }
                for(const aspc::ArithmeticRelation& ineq : aggregateRelation->getAggregate().getAggregateInequalities()){
                    if(!ineq.isBoundedRelation(positiveAggrVars)){
                        neededDomBodyPredicate=true;
                        break;
                    }
                }
                // for(const aspc::ArithmeticRelation& ineq : aggregateRelation->getAggregate().getAggregateInequalities()){
                //     for(const aspc::ArithmeticExpression& exp : {ineq.getLeft(),ineq.getRight()}){
                //         for(std::string term : exp.getAllTerms()){
                //             if(positiveAggrVars.count(term)==0){
                //                 neededDomBodyPredicate=true;
                //                 break;
                //             }
                //         }
                //         if(neededDomBodyPredicate) break;
                //     }
                //     if(neededDomBodyPredicate) break;
                // }
                if(neededDomBodyPredicate){
                    std::string domBodyPredicate="";
                    if(predicateToDomainPredicate.count(bodyPredicateName)==0){
                        domBodyPredicate="dom_pred_"+std::to_string(domainPredicates.size());
                        domainPredicates.insert(domBodyPredicate);
                        internalPredicates.insert(domBodyPredicate);
                        predicateToDomainPredicate[bodyPredicateName]=domBodyPredicate;
                        rewrittenProgram.addGeneratorDependecy(domBodyPredicate,bodyPredicateName);
                    }else{
                        domBodyPredicate=predicateToDomainPredicate[bodyPredicateName];
                    }
                    aggregateSetAssignedBody.addLiteral(aspc::Literal(false,aspc::Atom(domBodyPredicate,assignedBody.getTerms())));
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(domBodyPredicate,assignedBody.getTerms())));
                }
                iffCase = buildingBody.size() == 1 && inequalities.size() == 0 /*&& !neededDomBodyPredicate*/;
                if(iffCase){
                    aspc::Literal* l = &buildingBody[0];
                    if(l->isNegated()) iffCase=false;
                    else{
                        if(l->getTerms().size() != aggregateSetAssignedBody.getTerms().size()) iffCase=false;
                        else{
                            for(int i=0;i<aggregateSetAssignedBody.getTerms().size() && iffCase;i++){
                                bool found=false;
                                for(int j=0;j<l->getAriety();j++){
                                    if(aggregateSetAssignedBody.getTerms()[i]==l->getTerms()[j]){
                                        found=true;
                                        break;
                                    }
                                }
                                if(!found) iffCase = false;
                            }
                            for(int i=0;i<l->getAriety() && iffCase;i++){
                                bool found=false;
                                for(int j=0;j<aggregateSetAssignedBody.getTerms().size();j++){
                                    if(aggregateSetAssignedBody.getTerms()[j]==l->getTerms()[i]){
                                        found=true;
                                        break;
                                    }
                                }
                                if(!found) iffCase = false;
                            }
                            if(iffCase){
                                aggregateSetPredicateName=l->getPredicateName();
                                aggregateSetAssignedBody.clearLiterals();
                                aggregateSetAssignedBody.clearIneqs();
                                aggregateSetAssignedBody.setTerms(l->getTerms());
                            }
                        }
                    }
                }
                if(!iffCase){
                    for(auto pair: aggregateSetPredicateToAssignedBody){
                        if(pair.second == aggregateSetAssignedBody){
                            aggregateSetPredicateName=pair.first;
                            aggregateSetAssignedBody=pair.second;
                            break;
                        }
                    }
                    if(aggregateSetPredicateName==""){
                        aggregateSetPredicateName = "agg_set_"+std::to_string(aggregateSetPredicates.size());
                        aggregateSetPredicates.insert(aggregateSetPredicateName);
                        aggregateSetPredicateToAssignedBody[aggregateSetPredicateName]=aggregateSetAssignedBody;
                        buildingHead.push_back(aspc::Atom(aggregateSetPredicateName,aggregateSetAssignedBody.getTerms()));
                        aspc::Rule aggrSetRule(buildingHead,buildingBody,inequalities,true);
                        rewrittenProgram.addGeneratorDependenciesForRule(aggrSetRule);
                        rewrittenProgram.addRule(aggrSetRule);
                    }
                    
                }
                
                //build aggr_id rules
                if(aggregateRelation->getComparisonType() == aspc::EQ){
                    clearData();
                    aspc::ComparisonType first = aggregateRelation->isNegated() ? aspc::GT : aspc::GTE;
                    inequalitiesWithAggregate.push_back(
                        aspc::ArithmeticRelationWithAggregate(
                            false,
                            aggregateRelation->getGuard(),
                            aspc::Aggregate(
                                {aspc::Literal(false,aspc::Atom(aggregateSetPredicateName,aggregateSetAssignedBody.getTerms()))},
                                {},
                                aggregateRelation->getAggregate().getAggregateVariables(),
                                aggregateRelation->getAggregate().getAggregateFunction()),
                                first,
                                false
                        )
                    );
                    std::string aggIdPredicateNameGTE = "agg_id_"+std::to_string(aggIdPredicates.size());
                    if(bodyPredicateName!=""){
                        aggIdPredicateToBodyPredicate[aggIdPredicateNameGTE]=bodyPredicateName;
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                        rewrittenProgram.addGeneratorDependecy(aggIdPredicateNameGTE,bodyPredicateName);
                    }else{
                        rewrittenProgram.addGeneratorNode(aggIdPredicateNameGTE);
                    }
                    aggIdPredicates.insert(aggIdPredicateNameGTE);
                    buildingHead.push_back(aspc::Atom(aggIdPredicateNameGTE,assignedBody.getTerms()));
                    aspc::Rule aggIdRuleGTE(buildingHead,buildingBody,{},inequalitiesWithAggregate,true,false);
                    rewrittenProgram.addRule(aggIdRuleGTE);
                    clearData();
                    aspc::ComparisonType second = aggregateRelation->isNegated() ? aspc::LT : aspc::LTE;
                    
                    inequalitiesWithAggregate.push_back(
                        aspc::ArithmeticRelationWithAggregate(
                            false,
                            aggregateRelation->getGuard(),
                            aspc::Aggregate(
                                {aspc::Literal(false,aspc::Atom(aggregateSetPredicateName,aggregateSetAssignedBody.getTerms()))},
                                {},
                                aggregateRelation->getAggregate().getAggregateVariables(),
                                aggregateRelation->getAggregate().getAggregateFunction()),
                                second,
                                false
                        )
                    );
                    std::string aggIdPredicateNameLTE = "agg_id_"+std::to_string(aggIdPredicates.size());
                    if(bodyPredicateName!=""){
                        aggIdPredicateToBodyPredicate[aggIdPredicateNameLTE]=bodyPredicateName;
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                        rewrittenProgram.addGeneratorDependecy(aggIdPredicateNameLTE,bodyPredicateName);
                    }else{
                        rewrittenProgram.addGeneratorNode(aggIdPredicateNameLTE);
                    }
                    aggIdPredicates.insert(aggIdPredicateNameLTE);
                    buildingHead.push_back(aspc::Atom(aggIdPredicateNameLTE,assignedBody.getTerms()));
                    aspc::Rule aggIdRuleLTE(buildingHead,buildingBody,{},inequalitiesWithAggregate,true,false);
                    rewrittenProgram.addRule(aggIdRuleLTE);
                    
                    if(addedValuePredicate){
                        std::string valPredicate = "aux_val"+std::to_string(valuesPredicates.size()-1);
                        rewrittenProgram.addGeneratorDependecy(valPredicate,aggregateSetPredicateName);
                        valuesPredicateToRule[valPredicate]=rewrittenProgram.size()-1;
                    }
                    
                    clearData();
                    if(aggregateRelation->isNegated()){

                        for(const aspc::Atom& head : rules[i].getHead())
                            buildingHead.push_back(head);
                        if(bodyPredicateName!=""){
                            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                            rewrittenProgram.addGeneratorDependecy(buildingHead[0].getPredicateName(),bodyPredicateName);
                        }
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggIdPredicateNameGTE,assignedBody.getTerms())));
                        aspc::Rule ruleGT (buildingHead,buildingBody,{},true);
                        rewrittenProgram.addRule(ruleGT);
                        clearData();

                        for(const aspc::Atom& head : rules[i].getHead())
                            buildingHead.push_back(head);
                        if(bodyPredicateName!=""){
                            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                            rewrittenProgram.addGeneratorDependecy(buildingHead[0].getPredicateName(),bodyPredicateName);
                        }
                        buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggIdPredicateNameLTE,assignedBody.getTerms())));
                        aspc::Rule ruleLT (buildingHead,buildingBody,{},true);
                        rewrittenProgram.addRule(ruleLT);
                    }else{
                        for(const aspc::Atom& head : rules[i].getHead())
                        buildingHead.push_back(head);
                        if(bodyPredicateName!=""){
                            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                            rewrittenProgram.addGeneratorDependecy(buildingHead[0].getPredicateName(),bodyPredicateName);
                        }
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggIdPredicateNameGTE,assignedBody.getTerms())));
                        buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggIdPredicateNameLTE,assignedBody.getTerms())));
                        aspc::Rule rule (buildingHead,buildingBody,{},true);
                        rewrittenProgram.addRule(rule);
                    }
                    
                }else{
                    clearData();
                    inequalitiesWithAggregate.push_back(
                        aspc::ArithmeticRelationWithAggregate(
                            false,
                            aggregateRelation->getGuard(),
                            aspc::Aggregate(
                                {aspc::Literal(false,aspc::Atom(aggregateSetPredicateName,aggregateSetAssignedBody.getTerms()))},
                                {},
                                aggregateRelation->getAggregate().getAggregateVariables(),
                                aggregateRelation->getAggregate().getAggregateFunction()),
                                aggregateRelation->getComparisonType(),
                                aggregateRelation->isNegated()
                        )
                    );
                    inequalitiesWithAggregate.back().setPlusOne(aggregateRelation->isPlusOne());
                    std::string aggIdPredicateName = "agg_id_"+std::to_string(aggIdPredicates.size());
                    if(bodyPredicateName!=""){
                        aggIdPredicateToBodyPredicate[aggIdPredicateName]=bodyPredicateName;
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                        rewrittenProgram.addGeneratorDependecy(aggIdPredicateName,bodyPredicateName);
                    }else{
                        rewrittenProgram.addGeneratorNode(aggIdPredicateName);
                    }
                    aggIdPredicates.insert(aggIdPredicateName);
                    buildingHead.push_back(aspc::Atom(aggIdPredicateName,assignedBody.getTerms()));
                    aspc::Rule aggIdRuleGTE(buildingHead,buildingBody,{},inequalitiesWithAggregate,true,false);
                    rewrittenProgram.addRule(aggIdRuleGTE);
                    
                    if(addedValuePredicate){
                        std::string valPredicate = "aux_val"+std::to_string(valuesPredicates.size()-1);
                        rewrittenProgram.addGeneratorDependecy(valPredicate,aggregateSetPredicateName);
                        valuesPredicateToRule[valPredicate]=rewrittenProgram.size()-1;
                    }

                    clearData();
                    for(const aspc::Atom& head : rules[i].getHead())
                        buildingHead.push_back(head);
                    if(bodyPredicateName!=""){
                        rewrittenProgram.addGeneratorDependecy(buildingHead[0].getPredicateName(),bodyPredicateName);
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicateName,assignedBody.getTerms())));
                    }
                    buildingBody.push_back(aspc::Literal(aggregateRelation->isNegated(),aspc::Atom(aggIdPredicateName,assignedBody.getTerms())));
                    aspc::Rule rule (buildingHead,buildingBody,{},true);
                    rewrittenProgram.addRule(rule);
                }
            }
        }
    }
    

}
void AspCore2ProgramBuilder::computeCompletion(){
    // std::cout << "Completion" << std::endl;
    std::unordered_map<int,std::unordered_set<std::string>> recursiveComponents = rewrittenProgram.getRecursiveComponents();
    std::unordered_map<std::string,int> rulesCountForPredicate = rewrittenProgram.getRulesCountForPredicates();
    std::unordered_map<std::string,int> predicateToAriety;

    for(int i=0;i<rewrittenProgram.size();i++){
        const aspc::Rule* r = &rewrittenProgram.getRule(i);
        if(!r->isConstraint())
            internalPredicates.insert(r->getHead()[0].getPredicateName());
        rewrittenRuleToCompletionSubProgram.push_back(std::vector<int>());
        if(!r->isConstraint() && !r->containsAggregate()){
            const aspc::Atom* head = &r->getHead()[0];
            predicateToAriety[head->getPredicateName()]=head->getAriety();
            if(r->getBodyLiterals().size() == 1 && r->getArithmeticRelations().size() == 0){
                const aspc::Literal* l = &r->getBodyLiterals()[0];
                if(l->isPositiveLiteral()){
                    bool sameVariables = false;
                    for(int k=0; k<l->getAriety() && !sameVariables; k++){
                        if(!l->isVariableTermAt(k))
                            sameVariables=true;
                        for(int k1=0; k1<l->getAriety() && !sameVariables; k1++)
                            if(k!=k1 && l->isVariableTermAt(k) && l->isVariableTermAt(k1) && l->getTermAt(k)==l->getTermAt(k1))
                                sameVariables=true;
                    }
                    if(!sameVariables){
                        std::string headPredicate = head->getPredicateName();
                        if(rulesCountForPredicate[head->getPredicateName()]>1){
                            std::string sup = "sup_"+std::to_string(supPredicates.size());
                            supPredicates.insert(sup);
                            internalPredicates.insert(sup);

                            predicateToSupportPredicates[head->getPredicateName()].push_back(sup);
                            clearData();
                            buildingBody.push_back(aspc::Literal(false,aspc::Atom(sup,head->getTerms())));
                            buildingBody.push_back(aspc::Literal(true,*head));
                            aspc::Rule constraintSup(buildingHead,buildingBody,inequalities,true);
                            rewrittenRuleToCompletionSubProgram[i].push_back(programWithCompletion.size());
                            programWithCompletion.addRule(constraintSup);
                            headPredicate = sup;
                        }
                        aspc::Rule rule({aspc::Atom(headPredicate,head->getTerms())},{aspc::Literal(r->getBodyLiterals()[0])},{},true);
                        rewrittenRuleToCompletionSubProgram[i].push_back(programWithCompletion.size());
                        programWithCompletion.addRule(rule);
                        continue;
                    }
                }
                
            }
            std::unordered_set<std::string> distinctTerms;
            std::vector<std::string> terms;

            for(int k=0; k<head->getAriety();k++){
                if(head->isVariableTermAt(k) && distinctTerms.count(head->getTermAt(k))==0){
                    distinctTerms.insert(head->getTermAt(k));
                    terms.push_back(head->getTermAt(k));
                }
            }

            for(const aspc::Literal& l : r->getBodyLiterals()){
                if(l.isPositiveLiteral()){
                    for(int k=0; k<l.getAriety();k++){
                        if(l.isVariableTermAt(k) && distinctTerms.count(l.getTermAt(k))==0){
                            distinctTerms.insert(l.getTermAt(k));
                            terms.push_back(l.getTermAt(k));
                        }
                    }     
                }
            }
            int size = 0;
            while (size != distinctTerms.size()){
                size = distinctTerms.size();
                for(const aspc::ArithmeticRelation& ineq: r->getArithmeticRelations()){
                    if(ineq.isBoundedValueAssignment(distinctTerms)){
                        std::string assignedVar = ineq.getAssignedVariable(distinctTerms);
                        distinctTerms.insert(assignedVar);
                        terms.push_back(assignedVar);
                    }
                }
            }

            bool isRecursive = false;
            for(auto component: recursiveComponents){
                if(component.second.count(head->getPredicateName())!=0){
                    isRecursive=true;
                    break;
                }
            }
            
            bool iffCase = !isRecursive && rulesCountForPredicate[head->getPredicateName()]<2; 
            if(iffCase){
                if(head->getTerms().size() != terms.size()) iffCase=false;
                else{
                    for(int i=0;i<terms.size() && iffCase;i++){
                        bool found=false;
                        for(int j=0;j<head->getAriety();j++){
                            if(terms[i]==head->getTerms()[j]){
                                found=true;
                                break;
                            }
                        }
                        if(!found) iffCase = false;
                    }
                    for(int i=0;i<head->getAriety() && iffCase;i++){
                        bool found=false;
                        for(int j=0;j<terms.size();j++){
                            if(terms[j]==head->getTerms()[i]){
                                found=true;
                                break;
                            }
                        }
                        if(!found) iffCase = false;
                    }
                }
            }

            std::string auxPredicateName = "aux_"+std::to_string(auxPredicates.size());
            if(!iffCase){
                // head :- aux
                std::string headPredicate = head->getPredicateName();
                if(rulesCountForPredicate[headPredicate]>1){
                    std::string sup = "sup_"+std::to_string(supPredicates.size());
                    supPredicates.insert(sup);
                    internalPredicates.insert(sup);
                    predicateToSupportPredicates[headPredicate].push_back(sup);
                    clearData();
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(sup,head->getTerms())));
                    buildingBody.push_back(aspc::Literal(true,*head));
                    aspc::Rule constraintSup(buildingHead,buildingBody,inequalities,true);
                    rewrittenRuleToCompletionSubProgram[i].push_back(programWithCompletion.size());
                    programWithCompletion.addRule(constraintSup);
                    headPredicate=sup;
                }
                 
                clearData();
                buildingHead.push_back(aspc::Atom(headPredicate,head->getTerms()));
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicateName,terms)));
    
                aspc::Rule auxRule(buildingHead,buildingBody,{},true);
                rewrittenRuleToCompletionSubProgram[i].push_back(programWithCompletion.size());
                programWithCompletion.addRule(auxRule);
    
                auxPredicates.insert(auxPredicateName);
                internalPredicates.insert(auxPredicateName);
            }else{
                auxPredicateName = head->getPredicateName();
                terms = head->getTerms();
            }

            for(const aspc::Literal& l : r->getBodyLiterals()){
                clearData();
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicateName,terms)));
                buildingBody.push_back(aspc::Literal(!l.isNegated(),aspc::Atom(l.getAtom())));
    
                aspc::Rule auxBodyLitConstraint(buildingHead,buildingBody,{},true);
                programWithCompletion.addRule(auxBodyLitConstraint);

            }
            
            clearData();
            for(const aspc::Literal& l : r->getBodyLiterals())
                buildingBody.push_back(l);
            for(const aspc::ArithmeticRelation& ineq : r->getArithmeticRelations())
                inequalities.push_back(ineq);
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(auxPredicateName,terms)));
            aspc::Rule constraint(buildingHead,buildingBody,inequalities,true);
            rewrittenRuleToCompletionSubProgram[i].push_back(programWithCompletion.size());
            programWithCompletion.addRule(constraint);
        }else{
            rewrittenRuleToCompletionSubProgram[i].push_back(programWithCompletion.size());
            programWithCompletion.addRule(*r);
        }
    }
    for(auto pair : predicateToSupportPredicates){
        int ariety = predicateToAriety[pair.first];
        std::vector<std::string> terms;
        for(int k=0; k<ariety; k++){
            terms.push_back("X"+std::to_string(k));
        }
        clearData();
        buildingBody.push_back(aspc::Literal(false,aspc::Atom(pair.first,terms)));
        for(std::string pred : pair.second){
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(pred,terms)));
        }
        aspc::Rule supportConstraint(buildingHead,buildingBody,{},true);
        programWithCompletion.addRule(supportConstraint);
    }
    // std::cout<<"End completion"<<std::endl;
}
std::unordered_set<std::string> AspCore2ProgramBuilder::getInternalPredicates()const{
    return internalPredicates;
}
void AspCore2ProgramBuilder::buildProgram(){
    for(int r=0; r<programWithCompletion.size();r++){
        const aspc::Rule* rule = &programWithCompletion.getRule(r);
        for (const aspc::Atom& a : rule->getHead()) {
            compilableProgram.addPredicate(a.getPredicateName(), a.getAriety());
        }
        for (const aspc::Literal& l : rule->getBodyLiterals()) {
            compilableProgram.addPredicate(l.getPredicateName(), l.getAriety());
        }
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: rule->getArithmeticRelationsWithAggregate()){
            for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                compilableProgram.addAggregatePredicate(l.getPredicateName(), l.getAriety());
            }
        }
        compilableProgram.addRule(programWithCompletion.getRule(r));
    }
}
aspc::Program & AspCore2ProgramBuilder::getProgram() {
    if(!rewritten){
        std::cout << "buildCompilablePrograms" << std::endl;
        buildCompilablePrograms();
        std::cout << "computeCompletion" << std::endl;
        computeCompletion();
        std::cout << "buildProgram" << std::endl;
        buildProgram();
        std::cout << "rewritten" << std::endl;
        rewritten=true;
        // programWithCompletion.print();
        // std::cout << "\n\n"<<std::endl;
        // rewrittenProgram.print();
        // std::cout << "\n\n"<<std::endl;
    }

    return compilableProgram;
}
// bool AspCore2ProgramBuilder::isPredicateBodyNoCompletion(int predId)const{
// }
// void AspCore2ProgramBuilder::buildGraphNoCompletion(){
// }
const map<string, unsigned> & AspCore2ProgramBuilder::getArietyMap() {
    return arietyMap;
}
// GraphWithTarjanAlgorithm& AspCore2ProgramBuilder::getSourceGraphWithTarjanAlgorithm() {
//     return rewrittenProgram.getPositiveDG();
// }

GraphWithTarjanAlgorithm& AspCore2ProgramBuilder::getGraphWithTarjanAlgorithm() {
    return programWithCompletion.getDG();
}
// const unordered_map<int, Vertex>& AspCore2ProgramBuilder::getSourceVertexByIDMap() const {
//     return vertexByID;
// }
// const unordered_map<string, int>& AspCore2ProgramBuilder::getSourcePredicateIDsMap() const {
//     return predicateIDs;
// }

// const unordered_map<int, Vertex>& AspCore2ProgramBuilder::getVertexByIDMap() const {
// }

// const unordered_map<string, int>& AspCore2ProgramBuilder::getPredicateIDsMap() const {
// }



