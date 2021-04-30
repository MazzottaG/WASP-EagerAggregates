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
        if(writeAggrSetRule){
           
            aggrSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
            aggrSetPredicates.insert(aggrSetPredicate);

            std::unordered_set<std::string> bodyVars;
            for(const aspc::Literal& l : originalBody){
                l.addVariablesToSet(bodyVars);
            }
            for(const aspc::ArithmeticRelation& ineq: originalBodyInequalities){
                ineq.addVariablesToSet(bodyVars);
            }
            for(std::string var: originalAggrRelation[0].getAggregate().getAggregateVariables()){
                aggrSetPredicateTerms.push_back(var);
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
                // if(!foundVar){
                //     for(std::string term : originalAggrRelation[0].getGuard().getAllTerms()){
                //         if(term == var){
                //             foundVar=true;
                //             break;
                //         }
                //     }
                // }
                if(foundVar){
                    aggrSetPredicateTerms.push_back(var);
                }
            }
            //aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms);
            buildingHead.push_back(aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms));
            for(aspc::Literal l : originalAggrRelation[0].getAggregate().getAggregateLiterals()){
                buildingBody.push_back(l);
            }
            for(aspc::ArithmeticRelation ineq: originalAggrRelation[0].getAggregate().getAggregateInequalities()){
                inequalities.push_back(ineq);
            }
            onRule();
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
            onRule();
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
            onRule();

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
            onRule();

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
        /*
        unsigned actualProgramSize = program.getRulesSize();
        std::string bodyPredicate = "body"+std::to_string(actualProgramSize);

        std::unordered_set<std::string> bodyVars;
        for(const aspc::Literal& l : originalBody){
            l.addVariablesToSet(bodyVars);
        }
        for(const aspc::ArithmeticRelation& ineq: originalBodyInequalities){
            if(ineq.isBoundedValueAssignment(bodyVars)){
                bodyVars.insert(ineq.getAssignedVariable(bodyVars));
            }
        }
        std::vector<std::string> bodyAtomTerms;
        std::unordered_set<std::string> distictBodyAtomTerms;
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: originalAggrRelation){
            for(const aspc::Literal& l: aggrRelation.getAggregate().getAggregateLiterals()){
                for(unsigned k = 0; k<l.getAriety();k++){
                    if(l.isVariableTermAt(k) && bodyVars.count(l.getTermAt(k))!=0 && distictBodyAtomTerms.count(l.getTermAt(k))==0){
                        distictBodyAtomTerms.insert(l.getTermAt(k));
                        bodyAtomTerms.push_back(l.getTermAt(k));
                    }
                }
            }
            for(const std::string& term : aggrRelation.getGuard().getAllTerms()){
                if(isVariable(term) && bodyVars.count(term)!=0 && distictBodyAtomTerms.count(term)==0){
                    distictBodyAtomTerms.insert(term);
                    bodyAtomTerms.push_back(term);
                }
            }
            for(const aspc::ArithmeticRelation& ineq: aggrRelation.getAggregate().getAggregateInequalities()){
                for(const std::string& term : ineq.getLeft().getAllTerms()){
                    if(isVariable(term) && bodyVars.count(term)!=0 && distictBodyAtomTerms.count(term)==0){
                        distictBodyAtomTerms.insert(term);
                        bodyAtomTerms.push_back(term);
                    }
                }
                for(const std::string& term : ineq.getRight().getAllTerms()){
                    if(isVariable(term) && bodyVars.count(term)!=0 && distictBodyAtomTerms.count(term)==0){
                        distictBodyAtomTerms.insert(term);
                        bodyAtomTerms.push_back(term);
                    }
                }
            }
        }
        inequalitiesWithAggregate.clear();
        if(!originalBody.empty()){

            buildingHead.push_back(aspc::Atom(bodyPredicate,bodyAtomTerms));
            //body :- l1, ..., ln
            onRule();
        }else{
            buildingBody.clear();
            inequalities.clear();

        }
        std::vector<aspc::Atom> aggr_set_atoms; 
        unsigned aggrCount=0;
        for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: originalAggrRelation){
            std::unordered_set<std::string> distictAggrSetTerms;
            std::vector<std::string> aggreSetTerms;
            std::string aggrSetPredicate = "aggr_set"+std::to_string(actualProgramSize)+"_"+std::to_string(aggrCount);
            for(const std::string& var: aggrRelation.getAggregate().getAggregateVariables()){
                if(distictAggrSetTerms.count(var)==0){
                    distictAggrSetTerms.insert(var);
                    aggreSetTerms.push_back(var);
                }
            }
            for(const aspc::Literal& l: aggrRelation.getAggregate().getAggregateLiterals()){
                buildingBody.push_back(aspc::Literal(l));
                for(unsigned k=0;k<l.getAriety();k++){
                    if(l.isVariableTermAt(k) && bodyVars.count(l.getTermAt(k))!=0 && distictAggrSetTerms.count(l.getTermAt(k))==0){
                        distictAggrSetTerms.insert(l.getTermAt(k));
                        aggreSetTerms.push_back(l.getTermAt(k));
                    }
                }
            }
            for(const aspc::ArithmeticRelation& ineq: aggrRelation.getAggregate().getAggregateInequalities()){
                inequalities.push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
                for(const std::string& term : ineq.getLeft().getAllTerms()){
                    if(isVariable(term) && bodyVars.count(term)!=0 && distictAggrSetTerms.count(term)==0){
                        distictAggrSetTerms.insert(term);
                        aggreSetTerms.push_back(term);
                    }
                }
                for(const std::string& term : ineq.getRight().getAllTerms()){
                    if(isVariable(term) && bodyVars.count(term)!=0 && distictAggrSetTerms.count(term)==0){
                        distictAggrSetTerms.insert(term);
                        aggreSetTerms.push_back(term);
                    }
                }
            }
            buildingHead.push_back(aspc::Atom(aggrSetPredicate,aggreSetTerms));
            aggr_set_atoms.push_back(aspc::Atom(aggrSetPredicate,aggreSetTerms));
            //agg_set :- aggr_body
            onRule();
            aggrCount++;
        }
        aggrCount=0;
        for(const aspc::Atom& aggr_set : aggr_set_atoms){
            std::string aggrIdPredicate = "aggr_id"+std::to_string(actualProgramSize)+"_"+std::to_string(aggrCount);
            const aspc::ArithmeticRelationWithAggregate* aggrRelation = &originalAggrRelation[aggrCount];
            std::unordered_set<std::string> distinctAggrIdTerms;
            std::vector<std::string> aggrIdTerms;
            for(const aspc::Literal& l: aggrRelation->getAggregate().getAggregateLiterals()){
                for(unsigned k=0;k<l.getAriety();k++){
                    if(l.isVariableTermAt(k) && bodyVars.count(l.getTermAt(k))!=0 && distinctAggrIdTerms.count(l.getTermAt(k))==0){
                        distinctAggrIdTerms.insert(l.getTermAt(k));
                        aggrIdTerms.push_back(l.getTermAt(k));
                    }
                }
            }
            for(const aspc::ArithmeticRelation& ineq : aggrRelation->getAggregate().getAggregateInequalities()){
                for(std::string term : ineq.getLeft().getAllTerms())
                    if(isVariable(term) && bodyVars.count(term)!=0 && distinctAggrIdTerms.count(term)==0){
                        distinctAggrIdTerms.insert(term);
                        aggrIdTerms.push_back(term);
                    }
                for(std::string term : ineq.getRight().getAllTerms())
                    if(isVariable(term) && bodyVars.count(term)!=0 && distinctAggrIdTerms.count(term)==0){
                        distinctAggrIdTerms.insert(term);
                        aggrIdTerms.push_back(term);
                    }
            }
            for(std::string term : aggrRelation->getGuard().getAllTerms()){
                if(isVariable(term) && bodyVars.count(term)!=0 && distinctAggrIdTerms.count(term)==0){
                    distinctAggrIdTerms.insert(term);
                    aggrIdTerms.push_back(term);
                }
            }
            if(aggrRelation->getComparisonType() == aspc::EQ){
                buildingHead.push_back(aspc::Atom(aggrIdPredicate,aggrIdTerms));
                if(!originalBody.empty())
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                aspc::ComparisonType compair=aggrRelation->isNegated() ? aspc::GT : aspc::GTE;
                inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
                                                        false,
                                                        aggrRelation->getGuard(),
                                                        aspc::Aggregate(
                                                            {aspc::Literal(false,aggr_set)},
                                                            {},
                                                            aggrRelation->getAggregate().getAggregateVariables(),
                                                            aggrRelation->getAggregate().getAggregateFunction()),
                                                        compair,
                                                        false));
                
                onRule();
                std::string otherAggrIdPredicate = "aggr_id"+std::to_string(actualProgramSize)+"_"+std::to_string(aggrCount)+"_2";
                compair = aggrRelation->isNegated() ? aspc::LT : aspc::LTE;
                buildingHead.push_back(aspc::Atom(otherAggrIdPredicate,aggrIdTerms));
                if(!originalBody.empty())
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
                                                        false,
                                                        aggrRelation->getGuard(),
                                                        aspc::Aggregate(
                                                            {aspc::Literal(false,aggr_set)},
                                                            {},
                                                            aggrRelation->getAggregate().getAggregateVariables(),
                                                            aggrRelation->getAggregate().getAggregateFunction()),
                                                        compair,
                                                        false));
                onRule();
                if(aggrRelation->isNegated()){
                    buildingBody.push_back(aspc::Literal(false, aspc::Atom(aggrIdPredicate,aggrIdTerms)));
                    if(!originalBody.empty())
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                    onConstraint();
                    buildingBody.push_back(aspc::Literal(true, aspc::Atom(otherAggrIdPredicate,aggrIdTerms)));
                    if(!originalBody.empty())
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                    onConstraint();
                }else{
                    buildingBody.push_back(aspc::Literal(false, aspc::Atom(aggrIdPredicate,aggrIdTerms)));
                    buildingBody.push_back(aspc::Literal(true, aspc::Atom(otherAggrIdPredicate,aggrIdTerms)));
                    if(!originalBody.empty())
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                    onConstraint();
                }
                

            }else{
                buildingHead.push_back(aspc::Atom(aggrIdPredicate,aggrIdTerms));
                if(!originalBody.empty())
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
                                                        false,
                                                        aggrRelation->getGuard(),
                                                        aspc::Aggregate(
                                                            {aspc::Literal(false,aggr_set)},
                                                            {},
                                                            aggrRelation->getAggregate().getAggregateVariables(),
                                                            aggrRelation->getAggregate().getAggregateFunction()),
                                                        aggrRelation->getComparisonType(),
                                                        false));
                inequalitiesWithAggregate.back().setPlusOne(aggrRelation->isPlusOne());
                onRule();
                buildingBody.push_back(aspc::Literal(aggrRelation->isNegated(), aspc::Atom(aggrIdPredicate,aggrIdTerms)));
                if(!originalBody.empty())
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyAtomTerms)));
                onConstraint();
                
            }
            aggrCount++;
        }
        return;
        */
        /*
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
        */
    }
    aspc::Rule constraint(buildingHead, buildingBody, inequalities,std::vector<aspc::ArithmeticRelationWithAggregate>(inequalitiesWithAggregate), true);
    // constraint.print();
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
    buildingBody.clear();
    buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicate,auxDistinctTerms)));
    inequalities.clear();
    //head:-aux
    onRuleRewrited();
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
        // rule.print();
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



