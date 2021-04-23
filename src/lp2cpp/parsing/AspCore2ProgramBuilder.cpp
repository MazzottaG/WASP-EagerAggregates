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
    for (const aspc::Literal& l : buildingBody) {
        program.addPredicate(l.getPredicateName(), l.getAriety());

    }
    for(const aspc::ArithmeticRelation& inequality : inequalities){
        if(inequality.isBoundedValueAssignment(boundVariables)){
            boundVariables.insert(inequality.getAssignedVariable(boundVariables));
        }
    }
    if(!inequalitiesWithAggregate.empty()){
        aspc::ArithmeticRelationWithAggregate aggrRelation(isLower,inequalitiesWithAggregate[0].getGuard(),inequalitiesWithAggregate[0].getAggregate(),inequalitiesWithAggregate[0].getComparisonType(),inequalitiesWithAggregate[0].isNegated());
        aggrRelation.setPlusOne(inequalitiesWithAggregate[0].isPlusOne());
        // inequalitiesWithAggregate[0].print();
        // aggrRelation.print();
        bool isPlusOne = inequalitiesWithAggregate[0].isPlusOne();
        std::string aggrSetPred = "aggr_set"+std::to_string(aggrSetPredicateToBody.size());
        std::string aggrIdPred = "aggr_id"+std::to_string(aggrIdPredicate.size());
        std::string domBodyPred = "body"+std::to_string(aggrSetPredicateToBody.size());
        std::unordered_set<std::string> bodyVars;
        std::vector<aspc::Literal> bodyLiterals;
        std::vector<aspc::ArithmeticRelation> bodyInequalities;
        
        for(aspc::Literal l : buildingBody){
            aggrSetPredicateToBody[aggrSetPred].push_back(l);
            l.addVariablesToSet(bodyVars);
            bodyLiterals.push_back(l);
        }

        for(aspc::ArithmeticRelation ineq : inequalities){
            aggrSetPredicateToInequality[aggrSetPred].push_back(ineq);
            if(ineq.isBoundedValueAssignment(bodyVars)){
                bodyVars.insert(ineq.getAssignedVariable(bodyVars));
            }
            bodyInequalities.push_back(ineq);
        }

        buildingBody.clear();
        inequalities.clear();
        inequalitiesWithAggregate.clear();
        UnorderedSet<std::string> aggrSetVars;
        UnorderedSet<std::string> domBodyVars;
        std::vector<std::string> headTerms;
        std::vector<std::string> domBodyTerms;
        
        for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
            for(unsigned i=0; i<l.getAriety(); i++){
                if(l.isVariableTermAt(i) && bodyVars.count(l.getTermAt(i))!=0){
                    if(!aggrSetVars.contains(l.getTermAt(i))){
                        aggrSetVars.insert(l.getTermAt(i));
                        headTerms.push_back(l.getTermAt(i));
                    }
                    if(!domBodyVars.contains(l.getTermAt(i))){
                        domBodyVars.insert(l.getTermAt(i));
                        domBodyTerms.push_back(l.getTermAt(i));
                    }
                }
            }
            buildingBody.push_back(l);
        }
        for(const std::string& term : aggrRelation.getGuard().getAllTerms()){
            if(isVariable(term) && bodyVars.count(term)!=0 && !domBodyVars.contains(term)){
                domBodyVars.insert(term);
                domBodyTerms.push_back(term); 
            }
        }
        for(const aspc::ArithmeticRelation& ineq : aggrRelation.getAggregate().getAggregateInequalities()){
            inequalities.push_back(ineq);
        }
        for(const std::string& var : aggrRelation.getAggregate().getAggregateVariables()){
            if(!aggrSetVars.contains(var)){
                aggrSetVars.insert(var);
                headTerms.push_back(var);
            }
        }
        aspc::Atom aggrAtom(aggrSetPred,headTerms);
        buildingHead.push_back(aggrAtom);
        onRule();
        buildingHead.clear();
        buildingBody.clear();
        inequalities.clear();
        inequalitiesWithAggregate.clear();
        aspc::Atom domBodyAtom(domBodyPred,domBodyTerms);
        if(!bodyLiterals.empty()){
            for(aspc::Literal l : bodyLiterals){
                buildingBody.push_back(l);
            }
            for(aspc::ArithmeticRelation ineq : bodyInequalities){
                inequalities.push_back(ineq);
            }
            buildingHead.push_back(domBodyAtom);
            onRule();
            domBodyPredicate[domBodyPred].push_back(program.getRulesSize());

        }
        
        buildingHead.clear();
        buildingBody.clear();
        inequalities.clear();
        inequalitiesWithAggregate.clear();
        if(!bodyLiterals.empty())
            buildingBody.push_back(aspc::Literal(false,domBodyAtom));
        aspc::ComparisonType compType = aggrRelation.getComparisonType();
        bool eq=false;
        if(compType == aspc::EQ){
            eq=true;
            if(aggrRelation.isNegated())
                compType=aspc::GT;
            else
                compType=aspc::GTE;
        }

        aspc::ArithmeticRelationWithAggregate rewritedAggregate(isLower,aggrRelation.getGuard(),aspc::Aggregate({aspc::Literal(false,aggrAtom)},{},aggrRelation.getAggregate().getAggregateVariables(),aggrRelation.getAggregate().getAggregateFunction()),compType,false);
        if(!eq)
            rewritedAggregate.setPlusOne(aggrRelation.isPlusOne());
        rewritedAggregate.print();
        std::cout<<std::endl;
        inequalitiesWithAggregate.push_back(rewritedAggregate);
        aspc::Atom aggrIdAtom(aggrIdPred,domBodyTerms);
        buildingHead.push_back(aggrIdAtom);
        aggrIdPredicate.insert(aggrIdPred);
        onRule();
        if(eq){

            buildingHead.clear();
            buildingBody.clear();
            inequalities.clear();
            inequalitiesWithAggregate.clear();
            compType = aggrRelation.isNegated() ? aspc::LT : aspc::LTE;
            if(!bodyLiterals.empty())
                buildingBody.push_back(aspc::Literal(false,domBodyAtom));
        
            aspc::ArithmeticRelationWithAggregate rewritedAggregate2(isLower,aggrRelation.getGuard(),aspc::Aggregate({aspc::Literal(false,aggrAtom)},{},aggrRelation.getAggregate().getAggregateVariables(),aggrRelation.getAggregate().getAggregateFunction()),compType,false);
            // rewritedAggregate.setPlusOne(aggrRelation.isNegated());
            rewritedAggregate2.setNegated(false);
            rewritedAggregate2.print();
            std::cout<<std::endl;

            inequalitiesWithAggregate.push_back(rewritedAggregate2);
            std::string pred="aggr_id"+std::to_string(aggrIdPredicate.size());
            aspc::Atom addedAggrIdAtom(pred,domBodyTerms);
            buildingHead.push_back(addedAggrIdAtom);
            aggrIdPredicate.insert(pred);
            domBodyPredicate[domBodyPred].push_back(program.getRulesSize());
            onRule();
                
        }
        buildingHead.clear();
        buildingBody.clear();
        inequalities.clear();
        inequalitiesWithAggregate.clear();
        
        if(!eq || !aggrRelation.isNegated()){
            if(!bodyLiterals.empty())
                buildingBody.push_back(aspc::Literal(false,domBodyAtom));
            if(eq)
                buildingBody.push_back(aspc::Literal(false,aggrIdAtom));
            else
                buildingBody.push_back(aspc::Literal(aggrRelation.isNegated(),aggrIdAtom));
            if(eq && !aggrRelation.isNegated()){
                buildingBody.push_back(aspc::Literal(true,aspc::Atom("aggr_id"+std::to_string(aggrIdPredicate.size()-1),domBodyTerms)));
            }    
            onConstraint();
        }else{
            if(!bodyLiterals.empty())
                buildingBody.push_back(aspc::Literal(false,domBodyAtom));
            buildingBody.push_back(aspc::Literal(false,aggrIdAtom));
            onConstraint();
            buildingHead.clear();
            buildingBody.clear();
            inequalities.clear();
            inequalitiesWithAggregate.clear();
            if(!bodyLiterals.empty())
                buildingBody.push_back(aspc::Literal(false,domBodyAtom));
            buildingBody.push_back(aspc::Literal(true,aspc::Atom("aggr_id"+std::to_string(aggrIdPredicate.size()-1),domBodyTerms)));
            onConstraint();
            
        }
        return;
    }
    aspc::Rule constraint(buildingHead, buildingBody, inequalities,std::vector<aspc::ArithmeticRelationWithAggregate>(inequalitiesWithAggregate), true);
    constraint.print();
    for(const aspc::Literal& l : constraint.getBodyLiterals())
        addRulesToPredicate(program.getRules().size(),l.getPredicateName());
    program.addRule(constraint);
    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();

}
void AspCore2ProgramBuilder::normalizeArithmeticRelationsWithAggregate(){
    for(aspc::ArithmeticRelationWithAggregate& relation: inequalitiesWithAggregate){
        std::unordered_set<std::string> sharedVars;
        for(const aspc::Literal& l: relation.getAggregate().getAggregateLiterals()){
            for(int i=0;i<l.getAriety();i++){
                if(l.isVariableTermAt(i)){
                    sharedVars.insert(l.getTermAt(i));
                }
            }
        }
        std::unordered_set<std::string> trueSharedVar;
        for(std::string v : sharedVars){
            bool found=false;
            for(const aspc::Literal& l : buildingBody){
                // l.print();
                // std::cout<<"building body"<<std::endl;
                if(l.getVariables().count(v) > 0){
                    found=true;
                    break;
                }
            }
            if(found)
                trueSharedVar.insert(v);
        }
        relation.normalizeAggregateRelations(trueSharedVar);
    }
    
}

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
    //std::cout<<"GT"<<std::endl; 
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

    //std::cout<<"on less op"<<std::endl;
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

void AspCore2ProgramBuilder::rewriteRule(){

    if(!inequalitiesWithAggregate.empty()){
        onRuleRewrited();
        return;
    }
    
    std::vector<aspc::Atom> originalHead(buildingHead);
    std::vector<aspc::Literal> originalBody(buildingBody);
    std::vector<aspc::ArithmeticRelation> orginalInequalities(inequalities);

    unsigned actualRuleSize=program.getRules().size();
    std::unordered_set<std::string> ruleVariables;
    std::vector<std::string> auxTerms;
    for(const aspc::Atom& a : originalHead){
        for(unsigned k=0; k<a.getAriety(); k++){
            if(a.isVariableTermAt(k) && ruleVariables.count(a.getTermAt(k))==0){
                auxTerms.push_back(a.getTermAt(k));
                ruleVariables.insert(a.getTermAt(k));
            }
        }
    }
    for(const aspc::Literal& l : originalBody){
        for(unsigned k=0; k<l.getAriety(); k++){
            if(l.isVariableTermAt(k) && ruleVariables.count(l.getTermAt(k))==0){
                auxTerms.push_back(l.getTermAt(k));
                ruleVariables.insert(l.getTermAt(k));
            }
        }
    }

    unsigned auxId = auxiliaryPredicate.size();
    std::string auxName ="aux"+std::to_string(auxId); 
    auxiliaryPredicate[auxName]=auxId;
    aspc::Literal aux(false,aspc::Atom(auxName,auxTerms));
    auxToTerms[auxId]=auxTerms;
    std::vector<aspc::Literal> body;
    std::unordered_set<std::string> positiveVars;
    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
    buildingBody.push_back(aux);
    buildingHead.push_back(originalHead[0]);
    auxiliaryPredicateToRules[auxId].push_back(program.getRules().size());
    onRuleRewrited();
    for(const aspc::ArithmeticRelation& inequality : orginalInequalities){
        auxPredicateToInequality[auxName].push_back(inequality);
    }
    for(const aspc::Literal& l : originalBody){
        buildingBody.clear();
        buildingHead.clear();
        inequalities.clear();
        inequalitiesWithAggregate.clear();

        auxPredicateToBody[auxName].push_back(l);
        aspc::Literal bodyLiteral(l);
        bodyLiteral.setNegated(!bodyLiteral.isNegated());
        buildingBody.push_back(aux);
        buildingBody.push_back(bodyLiteral);
        auxiliaryPredicateToRules[auxId].push_back(program.getRules().size());
        onConstraint();
        body.push_back(bodyLiteral);
        if(!bodyLiteral.isNegated()){
            for(unsigned k = 0; k < bodyLiteral.getAriety(); k++){
                if(bodyLiteral.isVariableTermAt(k)){
                    positiveVars.insert(bodyLiteral.getTermAt(k));
                }
            }
        }
    }
    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
    for(aspc::Literal l : originalBody){
        buildingBody.push_back(l);
    }
    for(aspc::ArithmeticRelation ineq:orginalInequalities){
        inequalities.push_back(ineq);
    }
    aux.setNegated(true);
    buildingBody.push_back(aux);
    onConstraint();
}    
void AspCore2ProgramBuilder::onRuleRewrited() {
    if (buildingBody.empty() && inequalitiesWithAggregate.empty()) {
        program.addFact(buildingHead.back());
        
    } else {
        aspc::Rule rule = aspc::Rule(buildingHead, buildingBody, inequalities,inequalitiesWithAggregate, true);
        rule.print();
        for(const aspc::Literal& l : rule.getBodyLiterals())
            addRulesToPredicate(program.getRules().size(),l.getPredicateName());
    
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
                //vertexByID[currentBodyId].rules.push_back(rule.getRuleId());
                graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
            }
        }
    }
    //add predicates to program
    for (const aspc::Atom& a : buildingHead) {
        program.addPredicate(a.getPredicateName(), a.getAriety());
        // internalPredicatesId.insert(predicateIDs[a.getPredicateName()]);
    }
    for (const aspc::Literal& l : buildingBody) {
        program.addPredicate(l.getPredicateName(), l.getAriety());
    }

    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
}
void AspCore2ProgramBuilder::onRule() {
    if (buildingBody.empty() && inequalitiesWithAggregate.empty()) {
        program.addFact(buildingHead.back());
        
    } else {
        rewriteRule();
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

aspc::Program & AspCore2ProgramBuilder::getProgram() {
    return program;
}

const map<string, unsigned> & AspCore2ProgramBuilder::getArietyMap() {
    return arietyMap;
}

GraphWithTarjanAlgorithm& AspCore2ProgramBuilder::getGraphWithTarjanAlgorithm() {
    return graphWithTarjanAlgorithm;
}

const unordered_map<int, Vertex>& AspCore2ProgramBuilder::getVertexByIDMap() const {
    return vertexByID;
}

const unordered_map<string, int>& AspCore2ProgramBuilder::getPredicateIDsMap() const {
    return predicateIDs;
}



