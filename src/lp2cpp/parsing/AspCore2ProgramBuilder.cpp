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

void AspCore2ProgramBuilder::preprocessConstraint(bool& writeBodyRule,bool& writeAggrSetRule){
    if(!inequalitiesWithAggregate.empty()){
        std::unordered_set<std::string> bodyVars;
        for(const aspc::Literal& l : buildingBody){
            l.addVariablesToSet(bodyVars);
        }
        for(const aspc::ArithmeticRelation& l : inequalities){
            l.addVariablesToSet(bodyVars);
        }
        writeBodyRule = buildingBody.size()>1;
        if(!writeBodyRule){
            if(buildingBody.size()>0){
                for(std::string var: bodyVars){
                    bool foundInAggregate=false;
                    //ASSUMES ONLY ONE AGGREGATE
                    for(const aspc::Literal& l: inequalitiesWithAggregate[0].getAggregate().getAggregateLiterals()){
                        for(unsigned k=0; k<l.getAriety();k++){
                            if(l.isVariableTermAt(k) && l.getTermAt(k)==var){
                                foundInAggregate=true;
                                break;
                            }
                        }
                        if(foundInAggregate)
                            break;
                    }
                    if(!foundInAggregate){
                        for(const aspc::ArithmeticRelation& ineq : inequalitiesWithAggregate[0].getAggregate().getAggregateInequalities()){
                            for(std::string term: ineq.getLeft().getAllTerms()){
                                if(isVariable(term) && term == var){
                                    foundInAggregate=true;
                                    break;
                                }
                            }
                            if(!foundInAggregate){
                                for(std::string term: ineq.getRight().getAllTerms()){
                                    if(isVariable(term) && term == var){
                                        foundInAggregate=true;
                                        break;
                                    }
                                }
                            }
                            if(foundInAggregate){
                                break;
                            }
                        }
                    }
                    if(!foundInAggregate){
                        for(std::string term: inequalitiesWithAggregate[0].getGuard().getAllTerms()){
                            if(isVariable(term) && term == var){
                                foundInAggregate=true;
                                break;
                            }
                        }
                    }
                    if(!foundInAggregate){
                        writeBodyRule=true;
                        break;
                    }
                }
            }
        }
        writeAggrSetRule=inequalitiesWithAggregate[0].getAggregate().getAggregateLiterals().size()>1 || !inequalitiesWithAggregate[0].getAggregate().getAggregateInequalities().empty();
        if(!writeAggrSetRule){
            const aspc::Literal* literal = & inequalitiesWithAggregate[0].getAggregate().getAggregateLiterals()[0];
            for(unsigned k=0; k<literal->getAriety();k++){
                if(literal->isVariableTermAt(k)){
                    bool selectedVar=false;
                    for(std::string var: inequalitiesWithAggregate[0].getAggregate().getAggregateVariables()){
                        if(var == literal->getTermAt(k)){
                            selectedVar=true;
                        }
                    }
                    if(!selectedVar && bodyVars.count(literal->getTermAt(k))!=0){
                        selectedVar=true;
                    }
                    if(!selectedVar){
                        writeAggrSetRule=true;
                    }
                }
            }
            if(!writeAggrSetRule){
                for(unsigned k=0; k<literal->getAriety() && !writeAggrSetRule;k++){
                    if(literal->isVariableTermAt(k)){
                        for(unsigned j=k+1; j<literal->getAriety() && !writeAggrSetRule;j++){
                            if(literal->isVariableTermAt(j) && literal->getTermAt(k) == literal->getTermAt(j)){
                                writeAggrSetRule=true;
                            }
                        }
                    }
                }    
            }
        }
    }
    return;
}
void AspCore2ProgramBuilder::onConstraint() {

    bool writeBodyRule=false;
    bool writeAggrSetRule=false;
    preprocessConstraint(writeBodyRule,writeAggrSetRule);

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
        std::vector<aspc::Literal> originalBody(buildingBody);
        std::vector<aspc::ArithmeticRelation> originalBodyInequalities;
        for(const aspc::ArithmeticRelation& ineq:inequalities){
            originalBodyInequalities.push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
        }
        std::vector<aspc::ArithmeticRelationWithAggregate> originalAggrRelation;
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation:inequalitiesWithAggregate){
            originalAggrRelation.push_back(aspc::ArithmeticRelationWithAggregate(false,aggrRelation.getGuard(),aggrRelation.getAggregate(),aggrRelation.getComparisonType(),aggrRelation.isNegated()));
            originalAggrRelation.back().setPlusOne(aggrRelation.isPlusOne());
        }
        std::string bodyPredicate="";
        std::vector<std::string> bodyPredicateTerms;

        if(writeBodyRule){
            bodyPredicate = "body"+std::to_string(bodyPredicates.size());
            bodyPredicates.insert(bodyPredicate);

            std::unordered_set<std::string> bodyVars;
            for(const aspc::Literal& l : buildingBody){
                l.addVariablesToSet(bodyVars);
            }
            for(const aspc::ArithmeticRelation& ineq: inequalities){
                ineq.addVariablesToSet(bodyVars);
            }
            for(std::string var : bodyVars){
                bool foundVar=false;
                for(const aspc::Literal& l : inequalitiesWithAggregate[0].getAggregate().getAggregateLiterals()){
                    for(unsigned k=0; k<l.getAriety(); k++){
                        if(l.isVariableTermAt(k) && l.getTermAt(k) == var){
                            foundVar=true;
                            break;
                        }
                    }
                    if(foundVar){
                        break;
                    }
                }
                if(!foundVar){
                    for(const aspc::ArithmeticRelation& ineq: inequalitiesWithAggregate[0].getAggregate().getAggregateInequalities()){
                        for(std::string term : ineq.getLeft().getAllTerms()){
                            if(term == var){
                                foundVar=true;
                                break;
                            }
                        }
                        if(!foundVar){
                            for(std::string term : ineq.getRight().getAllTerms()){
                                if(term == var){
                                    foundVar=true;
                                    break;
                                }
                            }
                        }
                        if(foundVar)
                            break;
                    }
                }
                if(!foundVar){
                    for(std::string term : inequalitiesWithAggregate[0].getGuard().getAllTerms()){
                        if(term == var){
                            foundVar=true;
                            break;
                        }
                    }
                }
                if(foundVar){
                    bodyPredicateTerms.push_back(var);
                }
            }
            //aspc::Atom(bodyPredicate,bodyPredicateTerms);
            buildingHead.push_back(aspc::Atom(bodyPredicate,bodyPredicateTerms));
            inequalitiesWithAggregate.clear();
            onRule();
        }else{
            if(!buildingBody.empty()){
                bodyPredicate=buildingBody[0].getPredicateName();
                for(unsigned i=0; i<buildingBody[0].getAriety(); i++){
                    bodyPredicateTerms.push_back(buildingBody[0].getTermAt(i));
                }
            }
            buildingBody.clear();
            buildingHead.clear();
            inequalities.clear();
            inequalitiesWithAggregate.clear();
        }
        std::string aggrSetPredicate="";
        std::vector<std::string> aggrSetPredicateTerms;
        bool aggrset_found = false;
        if(writeAggrSetRule){
           
            aggrSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
            // aggrSetPredicates.insert(aggrSetPredicate);
            AggrSetPredicate aggrset;

            std::unordered_set<std::string> bodyVars;
            for(const aspc::Literal& l : originalBody){
                l.addVariablesToSet(bodyVars);
                aggrset.addLiteral(l);
            }
            for(const aspc::ArithmeticRelation& ineq: originalBodyInequalities){
                ineq.addVariablesToSet(bodyVars);
                aggrset.addInequality(ineq);
            }
            for(std::string var: originalAggrRelation[0].getAggregate().getAggregateVariables()){
                aggrSetPredicateTerms.push_back(var);
                aggrset.addTerm(var);
            }
            for(std::string var : bodyVars){
                bool foundVar=false;
                for(const aspc::Literal& l : originalAggrRelation[0].getAggregate().getAggregateLiterals()){
                    for(unsigned k=0; k<l.getAriety(); k++){
                        if(l.isVariableTermAt(k) && l.getTermAt(k) == var){
                            foundVar=true;
                            break;
                        }
                    }
                    if(foundVar){
                        break;
                    }
                }
                if(!foundVar){
                    for(const aspc::ArithmeticRelation& ineq: originalAggrRelation[0].getAggregate().getAggregateInequalities()){
                        for(std::string term : ineq.getLeft().getAllTerms()){
                            if(term == var){
                                foundVar=true;
                                break;
                            }
                        }
                        if(!foundVar){
                            for(std::string term : ineq.getRight().getAllTerms()){
                                if(term == var){
                                    foundVar=true;
                                    break;
                                }
                            }
                        }
                        if(foundVar)
                            break;
                    }
                }
                if(foundVar){
                    aggrSetPredicateTerms.push_back(var);
                    aggrset.addTerm(var);
                }
            }
            for(auto& previousAggrSet : aggrSetPredicates){
                std::cout<<previousAggrSet.first<<std::endl;
                
                if(previousAggrSet.second == aggrset){
                    aggrset_found=true;
                    aggrSetPredicate=previousAggrSet.first;
                    aggrSetPredicateTerms=previousAggrSet.second.getTerms();
                    break;
                }
            }
            if(!aggrset_found){
                aggrSetPredicates.insert({aggrSetPredicate,aggrset});
                //aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms);
                buildingHead.push_back(aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms));
                for(aspc::Literal l : originalAggrRelation[0].getAggregate().getAggregateLiterals()){
                    buildingBody.push_back(l);
                }
                for(aspc::ArithmeticRelation ineq: originalAggrRelation[0].getAggregate().getAggregateInequalities()){
                    inequalities.push_back(ineq);
                }
                onRule();
            }
                
            
        }else{
            if(!originalAggrRelation[0].getAggregate().getAggregateLiterals().empty()){
                aggrSetPredicate=originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getPredicateName();
                for(unsigned i=0; i<originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getAriety(); i++){
                    aggrSetPredicateTerms.push_back(originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getTermAt(i));
                }
                program.addAggregatePredicate(aggrSetPredicate,aggrSetPredicateTerms.size());
            }

            buildingBody.clear();
            buildingHead.clear();
            inequalities.clear();
            inequalitiesWithAggregate.clear();
        }

        
        if(originalAggrRelation[0].getComparisonType() != aspc::EQ){
            std::string aggrIdPredicate = "aggr_id"+std::to_string(aggrIdPredicates.size());
            aggrIdPredicates.insert(aggrIdPredicate);

            buildingHead.push_back(aspc::Atom(aggrIdPredicate,bodyPredicateTerms));
            if(bodyPredicate!=""){
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            }
            const aspc::ArithmeticRelationWithAggregate* aggregate = &originalAggrRelation[0];
            inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
                false,
                aggregate->getGuard(),
                aspc::Aggregate(
                    {aspc::Literal(false,aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms))},
                    {},
                    aggregate->getAggregate().getAggregateVariables(),
                    aggregate->getAggregate().getAggregateFunction()),
                aggregate->getComparisonType(),
                false)
            );
            inequalitiesWithAggregate[inequalitiesWithAggregate.size()-1].setPlusOne(aggregate->isPlusOne());
            onRuleRewrited();
            if(bodyPredicate!=""){
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            }
            buildingBody.push_back(aspc::Literal(aggregate->isNegated(),aspc::Atom(aggrIdPredicate,bodyPredicateTerms)));
            onConstraint();   
        }else{
            std::string aggrIdPredicate = "aggr_id"+std::to_string(aggrIdPredicates.size());
            aggrIdPredicates.insert(aggrIdPredicate);

            buildingHead.push_back(aspc::Atom(aggrIdPredicate,bodyPredicateTerms));
            if(bodyPredicate!=""){
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            }
            const aspc::ArithmeticRelationWithAggregate* aggregate = &originalAggrRelation[0];
            aspc::ComparisonType cmp = aggregate->isNegated() ? aspc::GT : aspc::GTE;
            // inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(false,aggregate->getGuard(),aggregate->getAggregate(),cmp,false));
            inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
                false,
                aggregate->getGuard(),
                aspc::Aggregate(
                    {aspc::Literal(false,aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms))},
                    {},
                    aggregate->getAggregate().getAggregateVariables(),
                    aggregate->getAggregate().getAggregateFunction()),
                cmp,
                false)
            );
            onRuleRewrited();

            std::string aggrIdPredicate2 = "aggr_id"+std::to_string(aggrIdPredicates.size());
            aggrIdPredicates.insert(aggrIdPredicate2);

            buildingHead.push_back(aspc::Atom(aggrIdPredicate2,bodyPredicateTerms));
            if(bodyPredicate!=""){
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            }
            aspc::ComparisonType cmp2 = aggregate->isNegated() ? aspc::LT : aspc::LTE;
            // inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(false,aggregate->getGuard(),aggregate->getAggregate(),cmp2,false));
            inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
                false,
                aggregate->getGuard(),
                aspc::Aggregate(
                    {aspc::Literal(false,aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms))},
                    {},
                    aggregate->getAggregate().getAggregateVariables(),
                    aggregate->getAggregate().getAggregateFunction()),
                cmp2,
                false)
            );
            onRuleRewrited();

            if(aggregate->isNegated()){
                if(bodyPredicate!=""){
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
                }
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIdPredicate,bodyPredicateTerms)));
                onConstraint();
                if(bodyPredicate!=""){
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
                }
                buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIdPredicate2,bodyPredicateTerms)));
                onConstraint();
            }else{
                if(bodyPredicate!=""){
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
                }
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIdPredicate,bodyPredicateTerms)));
                buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIdPredicate2,bodyPredicateTerms)));
                
                onConstraint();
            }
        }
        return;
    }
    aspc::Rule constraint(buildingHead, buildingBody, inequalities,std::vector<aspc::ArithmeticRelationWithAggregate>(inequalitiesWithAggregate), true);
    constraint.print();
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
//build aggr_set and aggr_id rule 
std::vector<aspc::Literal> AspCore2ProgramBuilder::rewriteAggregate(const aspc::Atom& bodyAtom,const std::unordered_set<string>& sharedVariables,const aspc::ArithmeticRelationWithAggregate& aggrRelation){
    AggrSetPredicate* aggrSet=NULL;
    std::string aggrSetPredicate; 
    bool sharedAggrSet=false;
    if(aggrRelation.getAggregate().getAggregateLiterals().size()>1 || !aggrRelation.getAggregate().getAggregateInequalities().empty()){
        aggrSetPredicate = "aggr_set"+std::to_string(aggrSetPredicates.size());
        std::unordered_set<std::string> distinctTerms;
        std::vector<std::string> aggrSetTerms;
        aggrSet = new AggrSetPredicate();

        for(const std::string& term : aggrRelation.getAggregate().getAggregateVariables()){
            if(distinctTerms.count(term)==0){
                distinctTerms.insert(term);
                aggrSetTerms.push_back(term);
                aggrSet->addTerm(term);
            }
        }
        for(const std::string& term : sharedVariables){
            if(distinctTerms.count(term)==0){
                distinctTerms.insert(term);
                aggrSetTerms.push_back(term);
                aggrSet->addTerm(term);
            }
        }

        for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
            buildingBody.push_back(l);
            aggrSet->addLiteral(l);
        }
        for(const aspc::ArithmeticRelation& ineq : aggrRelation.getAggregate().getAggregateInequalities()){
            inequalities.push_back(ineq);
            aggrSet->addInequality(ineq);
        }
        for(auto it=aggrSetPredicates.begin();it!=aggrSetPredicates.end() && !sharedAggrSet;it++){
            if(*aggrSet == it->second){
                sharedAggrSet=true;
                delete aggrSet;
                aggrSet = &it->second;
                aggrSetPredicate=it->first;
            }
        }
        if(!sharedAggrSet){
            aggrSetPredicates[aggrSetPredicate]=*aggrSet;
            buildingHead.clear();
            buildingHead.push_back(aspc::Atom(aggrSetPredicate,aggrSetTerms));
            onRule();
        }
        
    }
    if(aggrSet==NULL){
        const aspc::Literal* l = &aggrRelation.getAggregate().getAggregateLiterals()[0];
        program.addAggregatePredicate(l->getPredicateName(),l->getAriety());
    }else{
        program.addAggregatePredicate(aggrSetPredicate,aggrSet->getTerms().size());
    }

    //create aggrIdRule
    std::string aggrIdPredicate = "aggr_id"+std::to_string(aggrIdPredicates.size());
    std::vector<std::string> aggrIdTerms;
    for(const std::string& term : bodyAtom.getTerms()){
        if(sharedVariables.count(term)!=0){
            aggrIdTerms.push_back(term);
        }
    }

    buildingHead.clear();
    buildingHead.push_back(aspc::Atom(aggrIdPredicate,aggrIdTerms));
    if(bodyAtom.getPredicateName()!="")
        buildingBody.push_back(aspc::Literal(false,bodyAtom));
    aspc::ArithmeticRelationWithAggregate rewritedAggregate(aggrRelation);
    rewritedAggregate.setNegated(false);
    if(aggrSet!=NULL){
        rewritedAggregate.clearAggregateLiterals();
        rewritedAggregate.addAggregateLiteral(aspc::Literal(false,aspc::Atom(aggrSetPredicate, aggrSet->getTerms())));
    }
    inequalitiesWithAggregate.push_back(rewritedAggregate);
    onRuleRewrited();
    
    if(aggrSet!=NULL && !sharedAggrSet){
        delete aggrSet;
    }
    //WARNING: IT DOESN'T WORK WITH EQUAL OPERATOR
    return {aspc::Literal(aggrRelation.isNegated(),aspc::Atom(aggrIdPredicate,aggrIdTerms))};
}
void AspCore2ProgramBuilder::rewriteRuleWithAggregate(){

    aspc::Atom originalHead(buildingHead[0]);
    printingPredicate.insert(originalHead.getPredicateName());
    std::string bodyPredicate="body"+bodyPredicates.size();
    std::vector<std::string> bodyTerms;
    std::unordered_set<std::string> distinctTerms;
    std::unordered_set<std::string> bodyPositiveVars;
    aspc::ArithmeticRelationWithAggregate aggrRelation(inequalitiesWithAggregate[0]);

    for(aspc::Literal l : buildingBody){
        if(l.isPositiveLiteral())
            l.addVariablesToSet(bodyPositiveVars);
    }

    for(aspc::ArithmeticRelation ineq : inequalities){
        if(ineq.isBoundedValueAssignment(bodyPositiveVars)){
            bodyPositiveVars.insert(ineq.getAssignedVariable(bodyPositiveVars));
        }
    }
    const aspc::Atom* head = &buildingHead[0];
    for(unsigned i=0;i<head->getAriety();i++){
        if(head->isVariableTermAt(i) && distinctTerms.count(head->getTermAt(i))==0){
            distinctTerms.insert(head->getTermAt(i));
            bodyTerms.push_back(head->getTermAt(i));
        }
    }
    for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
        for(unsigned i=0;i<l.getAriety();i++){
            if(l.isVariableTermAt(i) && bodyPositiveVars.count(l.getTermAt(i))!=0 && distinctTerms.count(l.getTermAt(i))==0){
                distinctTerms.insert(l.getTermAt(i));
                bodyTerms.push_back(l.getTermAt(i));
            }
        }
    }
    for(const aspc::ArithmeticRelation& ineq : aggrRelation.getAggregate().getAggregateInequalities()){
        for(const std::string& term : ineq.getLeft().getAllTerms()){
            if(isVariable(term) && bodyPositiveVars.count(term)!=0 && distinctTerms.count(term)==0){
                distinctTerms.insert(term);
                bodyTerms.push_back(term);
            }
        }
        for(const std::string& term : ineq.getRight().getAllTerms()){
            if(isVariable(term) && bodyPositiveVars.count(term)!=0 && distinctTerms.count(term)==0){
                distinctTerms.insert(term);
                bodyTerms.push_back(term);
            }
        }
    }
    for(const std::string& term : aggrRelation.getGuard().getAllTerms()){
        if(isVariable(term) && bodyPositiveVars.count(term)!=0 && distinctTerms.count(term)==0){
            distinctTerms.insert(term);
            bodyTerms.push_back(term);
        }
    }
    bool writeBodyRule=buildingBody.size()>1 || !inequalities.empty(); 
    if(!writeBodyRule){
        if(!buildingBody.empty()){
            //one body literal no inequalities all head variables in buildingBody[0]
            for(std::string term : buildingBody[0].getTerms()){
                if(isVariable(term) && distinctTerms.count(term)==0){
                    writeBodyRule=true;
                    break;
                }
            }
        }
    }
    if(writeBodyRule){
        buildingHead.clear();
        buildingHead.push_back(aspc::Atom(bodyPredicate,bodyTerms));
        inequalitiesWithAggregate.clear();
        onRule();
    }else{
        if(!buildingBody.empty()){
            bodyPredicate = buildingBody[0].getPredicateName();
            bodyTerms = buildingBody[0].getTerms();
        }else{
            //WARNING a(X):-X=#count{Y:b(Y)}. doesn't work
            bodyTerms.clear();
            bodyPredicate="";
        }
        buildingHead.clear();
        buildingBody.clear();
        inequalitiesWithAggregate.clear();
        inequalities.clear();
        
    }
    std::vector<aspc::Literal> aggrIds = rewriteAggregate(aspc::Atom(bodyPredicate,bodyTerms),bodyPositiveVars,aggrRelation);
    buildingHead.push_back(originalHead);
    if(bodyPredicate!="")
        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyTerms)));
    for(aspc::Literal l : aggrIds){
        buildingBody.push_back(l);
    }
    onRule();
}
void AspCore2ProgramBuilder::rewriteRule(){
    std::cout<<"rewriteRule"<<std::endl;

    if(!inequalitiesWithAggregate.empty()){
        onRuleRewrited();
        return;
    }
    if(buildingBody.size()==1){
        bool conditionOnLiteral = false;
        for(unsigned i=0; i<buildingBody[0].getAriety() && ! conditionOnLiteral; i++){
            if(buildingBody[0].isVariableTermAt(i)){
                for(unsigned j=i+1; j<buildingBody[0].getAriety() && ! conditionOnLiteral; j++){
                    if(buildingBody[0].isVariableTermAt(j) && buildingBody[0].getTermAt(i) == buildingBody[0].getTermAt(j)){
                        conditionOnLiteral=true;
                    }
                }       
            }   
        }
        if(!conditionOnLiteral && inequalities.empty()){
            onRuleRewrited();
            return;
        }
    }
    // bool exitCase = buildingHead[0].getPredicateName()=="aggr_set0";
    std::vector<aspc::Atom> originalHead(buildingHead);
    std::vector<aspc::Literal> originalBody(buildingBody);
    std::vector<aspc::ArithmeticRelation> orginalInequalities;
    for(const aspc::ArithmeticRelation& ineq : inequalities){
        orginalInequalities.push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
    }

    std::string auxPredicate = "aux"+std::to_string(auxPredicateToBody.size());
    std::unordered_set<std::string> auxTerms;
    std::vector<std::string> auxDistinctTerms;

    for(const aspc::Atom& headAtom : originalHead){
        for(unsigned k=0;k<headAtom.getAriety();k++){
            if(auxTerms.count(headAtom.getTermAt(k))==0 || !headAtom.isVariableTermAt(k)){
                auxTerms.insert(headAtom.getTermAt(k));
                auxDistinctTerms.push_back(headAtom.getTermAt(k));
            }
        }
    } 
    for(const aspc::Literal& bodyLit : originalBody){
        auxPredicateToBody[auxPredicate].push_back(aspc::Literal(bodyLit));
        if(bodyLit.isPositiveLiteral()){
            for(unsigned k=0;k<bodyLit.getAriety();k++){
                if(auxTerms.count(bodyLit.getTermAt(k))==0 && bodyLit.isVariableTermAt(k)){
                    auxTerms.insert(bodyLit.getTermAt(k));
                    auxDistinctTerms.push_back(bodyLit.getTermAt(k));
                }
            }
        }
    }
    for(const aspc::ArithmeticRelation& ineq:orginalInequalities){
        auxPredicateToInequality[auxPredicate].push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
    }
    for(std::string term : auxDistinctTerms){
        auxLiteralTerms[auxPredicate].push_back(term);
    }
    bool iffCase = false;

    if(auxDistinctTerms.size() == buildingHead[0].getAriety()){
        iffCase=true;
        for(unsigned i=0; i<auxDistinctTerms.size(); i++){
            if(auxDistinctTerms[i]!=buildingHead[0].getTermAt(i)){
                iffCase=false;
                break;
            }
        }
        if(iffCase){
            for(unsigned i=0;i<auxPredicateToBody[auxPredicate].size();i++){
                auxPredicateToBody[buildingHead[0].getPredicateName()].push_back(auxPredicateToBody[auxPredicate][i]);
            }
            auxPredicateToBody.erase(auxPredicate);

            for(unsigned i=0;i<auxPredicateToInequality[auxPredicate].size();i++){
                auxPredicateToInequality[buildingHead[0].getPredicateName()].push_back(auxPredicateToInequality[auxPredicate][i]);
            }
            auxPredicateToInequality.erase(auxPredicate);

            for(unsigned i=0;i<auxLiteralTerms[auxPredicate].size();i++){
                auxLiteralTerms[buildingHead[0].getPredicateName()].push_back(auxLiteralTerms[auxPredicate][i]);
            }
            auxLiteralTerms.erase(auxPredicate);
            
            auxPredicate=buildingHead[0].getPredicateName();
            buildingHead.clear();
            buildingBody.clear();
            inequalities.clear();
        }
    }
    if(!iffCase){
        buildingBody.clear();
        buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicate,auxDistinctTerms)));
        inequalities.clear();
        //head:-aux
        onRuleRewrited();
        
    }
    
    for(const aspc::Literal& literal : originalBody){
        buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicate,auxDistinctTerms)));
        buildingBody.push_back(aspc::Literal(!literal.isNegated(),literal.getAtom()));
        //:-aux, not lit
        onConstraint();
    }
    for(const aspc::Literal& literal : originalBody){
        buildingBody.push_back(aspc::Literal(literal));
    }
    for(const aspc::ArithmeticRelation& ineq :orginalInequalities){
        inequalities.push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
    }
    buildingBody.push_back(aspc::Literal(true,aspc::Atom(auxPredicate,auxDistinctTerms)));
    //:-l1, ..., ln, not aux
    onConstraint();
    
}    
void AspCore2ProgramBuilder::onRuleRewrited() {
    if (buildingBody.empty() && inequalitiesWithAggregate.empty()) {
        program.addFact(buildingHead.back());
        
    } else {
        aspc::Rule rule = aspc::Rule(buildingHead, buildingBody, inequalities,inequalitiesWithAggregate, true);
        rule.print();
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
                // graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
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
        
    } else if(!inequalitiesWithAggregate.empty()) {
        rewriteRuleWithAggregate();
    } else{
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



