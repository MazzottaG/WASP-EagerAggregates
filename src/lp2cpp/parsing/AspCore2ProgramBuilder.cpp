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

void AspCore2ProgramBuilder::preprocess(bool& writeBodyRule,bool& writeAggrSetRule,bool isConstraint){
    std::unordered_set<std::string> bodyVars;
    std::unordered_set<std::string> headVars;
    if(!isConstraint){
        for(const aspc::Atom& a : buildingHead){
            aspc::Literal(false,a).addVariablesToSet(headVars);
        }
    }
    for(const aspc::Literal& l : buildingBody){
        l.addVariablesToSet(bodyVars);
    }
    for(const aspc::ArithmeticRelation& l : inequalities){
        l.addVariablesToSet(bodyVars);
    }
    writeBodyRule = buildingBody.size()>1 || inequalities.size()>0;
    if(!writeBodyRule){
        if(buildingBody.size()>0){
            for(std::string var: bodyVars){
                bool foundInAggregate=false;
                //WARNING: ASSUMES ONLY ONE AGGREGATE
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
                    if(!isConstraint){
                        if(headVars.count(var)!=0){
                            continue;
                        }
                    }
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
    return;
}
void AspCore2ProgramBuilder::onConstraint() {

    int size=program.getRules().size();
    if(!analyzeDependencyGraph)
        size=original_program.getRules().size();

    std::unordered_set<std::string> boundVariables;
    
    for (const aspc::Literal& l : buildingBody) {

        for(int term=0;term<l.getAriety();term++){
            if(l.isVariableTermAt(term)){
                boundVariables.insert(l.getTermAt(term));
            }
        }
        if(analyzeDependencyGraph){
            int currentBodyId = predicateIDs.size();
            unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
            if (i != predicateIDs.end())
                currentBodyId = i->second;
            else {
                predicateIDs[l.getPredicateName()] = currentBodyId;
                vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
            }
        }else{
            int currentBodyId = originalPredicateIDs.size();
            unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
            if (i != originalPredicateIDs.end())
                currentBodyId = i->second;
            else {
                originalPredicateIDs[l.getPredicateName()] = currentBodyId;
                originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
            }
        }
        
    }
    for(const aspc::ArithmeticRelationWithAggregate& aggrRelation : inequalitiesWithAggregate){
        for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {

            for(int term=0;term<l.getAriety();term++){
                if(l.isVariableTermAt(term)){
                    boundVariables.insert(l.getTermAt(term));
                }
            }
            if(analyzeDependencyGraph){
                int currentBodyId = predicateIDs.size();
                unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
                if (i != predicateIDs.end())
                    currentBodyId = i->second;
                else {
                    predicateIDs[l.getPredicateName()] = currentBodyId;
                    vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                }
            }else{
                int currentBodyId = originalPredicateIDs.size();
                unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
                if (i != originalPredicateIDs.end())
                    currentBodyId = i->second;
                else {
                    originalPredicateIDs[l.getPredicateName()] = currentBodyId;
                    originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                }
            }
            
        }
    }
    for (const aspc::Literal& l : buildingBody) {
        if(analyzeDependencyGraph){
            program.addPredicate(l.getPredicateName(), l.getAriety());
        }else{
            original_program.addPredicate(l.getPredicateName(), l.getAriety());
        }

    }
    for(const aspc::ArithmeticRelation& inequality : inequalities){
        if(inequality.isBoundedValueAssignment(boundVariables)){
            boundVariables.insert(inequality.getAssignedVariable(boundVariables));
        }
    }
    aspc::Rule constraint(buildingHead, buildingBody, inequalities,std::vector<aspc::ArithmeticRelationWithAggregate>(inequalitiesWithAggregate), true,!analyzeDependencyGraph);
    if(analyzeDependencyGraph)
        program.addRule(constraint);
    else
        original_program.addRule(constraint);

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
std::vector<aspc::Literal> AspCore2ProgramBuilder::rewriteAggregate(std::vector<aspc::Literal >& bodyLiterals,const std::unordered_set<string>& bodyVars,const aspc::ArithmeticRelationWithAggregate& aggrRelation,bool generateAuxVal){
    AggrSetPredicate* aggrSet=NULL;
    std::string aggrSetPredicate; 
    unsigned bodyLiteralsSize = bodyLiterals.size();
    bool sharedAggrSet=false;

    std::unordered_set<std::string>aggrBodySharedTerms;
    std::unordered_set<std::string>guardSharedTerms;
    
    
    for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
        for(unsigned i=0;i<l.getAriety();i++){
            if(l.isVariableTermAt(i) && bodyVars.count(l.getTermAt(i))!=0 && aggrBodySharedTerms.count(l.getTermAt(i))==0){
                aggrBodySharedTerms.insert(l.getTermAt(i));
            }
        }
    }
    for(const aspc::ArithmeticRelation& l : aggrRelation.getAggregate().getAggregateInequalities()){
        for(std::string term :l.getLeft().getAllTerms()){
            if(isVariable(term) && bodyVars.count(term)!=0 && aggrBodySharedTerms.count(term)==0){
                aggrBodySharedTerms.insert(term);
            }
        }
        for(std::string term :l.getRight().getAllTerms()){
            if(isVariable(term) && bodyVars.count(term)!=0 && guardSharedTerms.count(term)==0){
                aggrBodySharedTerms.insert(term);
            }
        }
    }
    for(std::string term :aggrRelation.getGuard().getAllTerms()){
        if(isVariable(term) && bodyVars.count(term)!=0 && guardSharedTerms.count(term)==0){
            guardSharedTerms.insert(term);
        }
    }

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
        for(const std::string& term : aggrBodySharedTerms){
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
        if(analyzeDependencyGraph)
            program.addAggregatePredicate(l->getPredicateName(),l->getAriety());
        else
            original_program.addAggregatePredicate(l->getPredicateName(),l->getAriety());
    }else{
        if(analyzeDependencyGraph)
            program.addAggregatePredicate(aggrSetPredicate,aggrSet->getTerms().size());
        else
            original_program.addAggregatePredicate(aggrSetPredicate,aggrSet->getTerms().size());
    }

    if(generateAuxVal){
        std::string auxValPred = "";
        if(!sharedAggrSet){
            auxValPred = "aux_val"+std::to_string(auxPossibleSumToAggrSet.size());
            auxPossibleSumToAggrSet[auxValPred]=aggrSetPredicate;
            aggrSetToAuxVal[aggrSetPredicate]=auxValPred;
        }else{
            auxValPred=aggrSetToAuxVal[aggrSetPredicate];
        }
        //WARNING: Works only if free variable is on first term of the guard
        guardSharedTerms.insert(aggrRelation.getGuard().getTerm1());
        bodyLiterals.push_back(aspc::Literal(false,aspc::Atom(auxValPred,{aggrRelation.getGuard().getTerm1()})));
        //------------------------------------------------------------------
        bodyLiteralsSize = bodyLiterals.size();
    }
    std::vector<std::string> aggrIdTerms;
    std::unordered_set<std::string>aggrIdDistincTems;

    for(std::string term: aggrBodySharedTerms){
        if(aggrIdDistincTems.count(term)==0){
            aggrIdTerms.push_back(term);
            aggrIdDistincTems.insert(term);
        }
    }
    for(std::string term: guardSharedTerms){
        if(aggrIdDistincTems.count(term)==0){
            aggrIdTerms.push_back(term);
            aggrIdDistincTems.insert(term);
        }
    }
    //create aggrIdRule
    if(aggrRelation.getComparisonType() != aspc::EQ){
        std::string aggrIdPredicate = "aggr_id"+std::to_string(aggrIdPredicates.size());
        aggrIdPredicates.insert(aggrIdPredicate);
        

        buildingHead.clear();
        buildingHead.push_back(aspc::Atom(aggrIdPredicate,aggrIdTerms));
        for(unsigned i = 0; i<bodyLiteralsSize; i++){
            buildingBody.push_back(aspc::Literal(bodyLiterals[i]));
        }
        aspc::ArithmeticRelationWithAggregate rewritedAggregate(aggrRelation);
        rewritedAggregate.setNegated(false);
        if(aggrSet!=NULL){
            rewritedAggregate.clearAggregateLiterals();
            rewritedAggregate.addAggregateLiteral(aspc::Literal(false,aspc::Atom(aggrSetPredicate, aggrSet->getTerms())));
        }
        inequalitiesWithAggregate.push_back(rewritedAggregate);
        onRule();     
        if(aggrSet!=NULL && !sharedAggrSet){
            delete aggrSet;
        }
        
        return {aspc::Literal(aggrRelation.isNegated(),aspc::Atom(aggrIdPredicate,aggrIdTerms))};
    }else{
        std::string aggrIdPredicateGTE = "aggr_id"+std::to_string(aggrIdPredicates.size());
        aggrIdPredicates.insert(aggrIdPredicateGTE);

        std::string aggrIdPredicateLTE = "aggr_id"+std::to_string(aggrIdPredicates.size());
        aggrIdPredicates.insert(aggrIdPredicateLTE);
        
        buildingHead.clear();
        buildingHead.push_back(aspc::Atom(aggrIdPredicateGTE,aggrIdTerms));
        for(unsigned i = 0; i<bodyLiteralsSize; i++){
            buildingBody.push_back(aspc::Literal(bodyLiterals[i]));
        }
        aspc::ArithmeticRelationWithAggregate rewritedAggregateGTE(aggrRelation);
        rewritedAggregateGTE.setNegated(false);
        rewritedAggregateGTE.setPlusOne(false);
        rewritedAggregateGTE.setCompareType(aspc::GTE);
        if(aggrSet!=NULL){
            rewritedAggregateGTE.clearAggregateLiterals();
            rewritedAggregateGTE.addAggregateLiteral(aspc::Literal(false,aspc::Atom(aggrSetPredicate, aggrSet->getTerms())));
        }
        inequalitiesWithAggregate.push_back(rewritedAggregateGTE);
        onRule();     

        buildingHead.clear();
        buildingHead.push_back(aspc::Atom(aggrIdPredicateLTE,aggrIdTerms));
        for(unsigned i = 0; i<bodyLiteralsSize; i++){
            buildingBody.push_back(aspc::Literal(bodyLiterals[i]));
        }
        aspc::ArithmeticRelationWithAggregate rewritedAggregateLTE(aggrRelation);
        rewritedAggregateLTE.setNegated(false);
        rewritedAggregateLTE.setPlusOne(true);
        rewritedAggregateLTE.setCompareType(aspc::GTE);
        if(aggrSet!=NULL){
            rewritedAggregateLTE.clearAggregateLiterals();
            rewritedAggregateLTE.addAggregateLiteral(aspc::Literal(false,aspc::Atom(aggrSetPredicate, aggrSet->getTerms())));
        }
        inequalitiesWithAggregate.push_back(rewritedAggregateLTE);
        onRule();     
        if(aggrSet!=NULL && !sharedAggrSet){
            delete aggrSet;
        }
        
        //WARNING: IT DOESN'T WORK WITH NOT EQUAL OPERATOR
        return {aspc::Literal(false,aspc::Atom(aggrIdPredicateGTE,aggrIdTerms)),aspc::Literal(true,aspc::Atom(aggrIdPredicateLTE,aggrIdTerms))};

    }
    
    
}
void AspCore2ProgramBuilder::rewriteRuleWithAggregateNotBound(){
}

void AspCore2ProgramBuilder::rewriteRuleWithAggregate(bool aggregateRelationNotBound){
    #ifdef TRACE_PARSING
        std::cout<<"Rewriting rule with aggregate"<<std::endl;
    #endif
    
    bool writeBodyRule=false;
    bool writeAggrSetRule=false;
    preprocess(writeBodyRule,writeAggrSetRule,false);
    #ifdef TRACE_PARSING
        if(writeBodyRule)
            std::cout<<"Body must be rewrited"<<std::endl;
        if(writeAggrSetRule)
            std::cout<<"AggrSet must be rewrited"<<std::endl;
    #endif
    std::vector<aspc::Atom> originalHead(buildingHead);
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

    buildingHead.clear();
    buildingBody.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
    
    std::string aggrSetPredicate="";
    std::vector<std::string> aggrSetPredicateTerms;
    bool aggrset_found = false;
    if(writeAggrSetRule){
        #ifdef TRACE_PARSING
            std::cout<<"Building Aggregate Set"<<std::endl;
        #endif
        aggrSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
        // aggrSetPredicates.insert(aggrSetPredicate);
        AggrSetPredicate aggrset;

        std::unordered_set<std::string> bodyVars;
        for(const aspc::Literal& l : originalBody){
            l.addVariablesToSet(bodyVars);
            
        }
        for(const aspc::ArithmeticRelation& ineq: originalBodyInequalities){
            ineq.addVariablesToSet(bodyVars);
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
        for(const aspc::Literal& l : originalAggrRelation[0].getAggregate().getAggregateLiterals())
            aggrset.addLiteral(l);
        for(const aspc::ArithmeticRelation& ineq : originalAggrRelation[0].getAggregate().getAggregateInequalities())
            aggrset.addInequality(ineq);

        #ifdef TRACE_PARSING
            std::cout<<"Aggregate Set Built"<<std::endl;
            aggrset.print();
        #endif
        for(auto& previousAggrSet : aggrSetPredicates){
            if(previousAggrSet.second == aggrset){
                aggrset_found=true;
                aggrSetPredicate=previousAggrSet.first;
                aggrSetPredicateTerms=previousAggrSet.second.getTerms();
                break;
            }
        }
        if(!aggrset_found){
            #ifdef TRACE_PARSING
                std::cout<<"Saving new aggr set"<<std::endl;
                aggrset.print();
            #endif
            for(const aspc::Literal& l : originalAggrRelation[0].getAggregate().getAggregateLiterals()){
                buildingBody.push_back(aspc::Literal(l));
            }

            for(const aspc::ArithmeticRelation& l : originalAggrRelation[0].getAggregate().getAggregateInequalities()){
                inequalities.push_back(aspc::ArithmeticRelation(l.getLeft(),l.getRight(),l.getComparisonType()));
            }
            aggrSetPredicates.insert({aggrSetPredicate,aggrset});
            //aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms);
            buildingHead.push_back(aspc::Atom(aggrSetPredicate,aggrSetPredicateTerms));
            inequalitiesWithAggregate.clear();
            rewriteRule();
            std::string auxValPred = "aux_val"+std::to_string(auxPossibleSumToAggrSet.size());
            aggrSetToAuxVal[aggrSetPredicate]=auxValPred;
            auxPossibleSumToAggrSet[auxValPred]=aggrSetPredicate;
            if(!originalAggrRelation[0].isBoundedRelation(bodyVars) && originalAggrRelation[0].getComparisonType()==aspc::EQ){
                originalBody.push_back(aspc::Literal(false,aspc::Atom(auxValPred,{originalAggrRelation[0].getGuard().getTerm1()})));
                if(!writeBodyRule && (originalBody.size()>1 || originalBodyInequalities.size()>0))
                    writeBodyRule=true;
                #ifdef TRACE_PARSING
                    std::cout<<"Adding aux_val predicate"<<std::endl;
                    aspc::Literal(false,aspc::Atom(auxValPred,{originalAggrRelation[0].getGuard().getTerm1()})).print();
                #endif
            }
            
        }else{
            #ifdef TRACE_PARSING
                std::cout<<"aggr set already declared"<<std::endl;
            #endif
            std::string auxValPred = aggrSetToAuxVal[aggrSetPredicate];
            if(!originalAggrRelation[0].isBoundedRelation(bodyVars) && inequalitiesWithAggregate[0].getComparisonType()==aspc::EQ){
                originalBody.push_back(aspc::Literal(false,aspc::Atom(auxValPred,{inequalitiesWithAggregate[0].getGuard().getTerm1()})));
                if(!writeBodyRule && (originalBody.size()>1 || originalBodyInequalities.size()>0))
                    writeBodyRule=true;
                #ifdef TRACE_PARSING
                    std::cout<<"Adding aux_val predicate"<<std::endl;
                    aspc::Literal(false,aspc::Atom(auxValPred,{inequalitiesWithAggregate[0].getGuard().getTerm1()})).print();
                #endif
            }
        }
            
        
    }else{
         
        #ifdef TRACE_PARSING
            std::cout<<"AggrSet rule not needed"<<std::endl;
            std::cout<<"Body: "<<std::endl;
            for(const aspc::Literal& l : originalBody){
                l.print();
            }
            for(const aspc::ArithmeticRelation& l : originalBodyInequalities){
                l.print();
            }
            std::cout<<"Aggregate Body: "<<std::endl;
            for(const aspc::Literal& l : originalAggrRelation[0].getAggregate().getAggregateLiterals()){
                l.print();
            }
            for(const aspc::ArithmeticRelation& l : originalAggrRelation[0].getAggregate().getAggregateInequalities()){
                l.print();
            }
        #endif
        std::unordered_set<std::string> bodyVars;
        for(const aspc::Literal& l : originalBody){
            l.addVariablesToSet(bodyVars);
        }
        for(const aspc::ArithmeticRelation& ineq: originalBodyInequalities){
            ineq.addVariablesToSet(bodyVars);
        }
        // no aggrset rule
        if(!originalAggrRelation[0].getAggregate().getAggregateLiterals().empty()){
            aggrSetPredicate=originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getPredicateName();
            if(!originalAggrRelation[0].isBoundedRelation(bodyVars) && originalAggrRelation[0].getComparisonType()==aspc::EQ){
                if(aggrSetToAuxVal.count(aggrSetPredicate)==0){
                    std::string auxValPred = "aux_val"+std::to_string(auxPossibleSumToAggrSet.size());
                    aggrSetToAuxVal[aggrSetPredicate]=auxValPred;
                    auxPossibleSumToAggrSet[auxValPred]=aggrSetPredicate;        
                }
                std::string auxValPred = aggrSetToAuxVal[aggrSetPredicate];
                originalBody.push_back(aspc::Literal(false,aspc::Atom(auxValPred,{originalAggrRelation[0].getGuard().getTerm1()})));
                if(!writeBodyRule && (originalBody.size()>1 || originalBodyInequalities.size()>0))
                    writeBodyRule=true;
                #ifdef TRACE_PARSING
                    std::cout<<"Adding aux_val predicate"<<std::endl;
                    aspc::Literal(false,aspc::Atom(auxValPred,{originalAggrRelation[0].getGuard().getTerm1()})).print();
                #endif
            }
            for(unsigned i=0; i<originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getAriety(); i++){
                aggrSetPredicateTerms.push_back(originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getTermAt(i));
            }
            original_program.addAggregatePredicate(aggrSetPredicate,aggrSetPredicateTerms.size());
        }
    }

    buildingBody.clear();
    buildingHead.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();


    std::string bodyPredicate="";
    std::vector<std::string> bodyPredicateTerms;

    if(writeBodyRule){
        #ifdef TRACE_PARSING
            std::cout<<"Body rule needed"<<std::endl;
        #endif
        bodyPredicate = "body"+std::to_string(bodyPredicates.size());
        bodyPredicates.insert(bodyPredicate);

        std::unordered_set<std::string> bodyVars;
        for(const aspc::Literal& l : originalBody){
            buildingBody.push_back(aspc::Literal(l));
            l.addVariablesToSet(bodyVars);
        }
        for(const aspc::ArithmeticRelation& ineq: originalBodyInequalities){
            inequalities.push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
            ineq.addVariablesToSet(bodyVars);
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
            if(!foundVar){
                for(std::string term : originalAggrRelation[0].getGuard().getAllTerms()){
                    if(term == var){
                        foundVar=true;
                        break;
                    }
                }
            }
            
            if(!foundVar){
                for(unsigned i=0; i<originalHead[0].getAriety(); i++){
                    if(isVariable(originalHead[0].getTermAt(i)) && originalHead[0].getTermAt(i)==var){
                        foundVar=true;
                        break;
                    }
                }
            }
            if(foundVar){
                bodyPredicateTerms.push_back(var);
            }
        }
        #ifdef TRACE_PARSING
            std::cout<<"Body Literal Computed"<<std::endl;
            aspc::Atom(bodyPredicate,bodyPredicateTerms).print();
        #endif

        //aspc::Atom(bodyPredicate,bodyPredicateTerms);
        buildingHead.push_back(aspc::Atom(bodyPredicate,bodyPredicateTerms));
        inequalitiesWithAggregate.clear();
        rewriteRule();
    }else{
        if(!originalBody.empty()){
            #ifdef TRACE_PARSING
                std::cout<<"Body Literal Already Exists"<<std::endl;
            #endif
            bodyPredicate=originalBody[0].getPredicateName();
            for(unsigned i=0; i<originalBody[0].getAriety(); i++){
                bodyPredicateTerms.push_back(originalBody[0].getTermAt(i));
            }
        }else{
            #ifdef TRACE_PARSING
                std::cout<<"Empty body"<<std::endl;
            #endif

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

        #ifdef TRACE_PARSING
            std::cout<<"Rule for aggregate with no equal op"<<std::endl;
            std::cout<<"Head: ";
            aspc::Atom(aggrIdPredicate,bodyPredicateTerms).print();
            std::cout<<"Body: ";
        #endif
        if(bodyPredicate!=""){
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            #ifdef TRACE_PARSING
                aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)).print();
            #endif
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
        #ifdef TRACE_PARSING
            inequalitiesWithAggregate[0].print();
        #endif
        inequalitiesWithAggregate[inequalitiesWithAggregate.size()-1].setPlusOne(aggregate->isPlusOne());
        onRule();
        if(bodyPredicate!=""){
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
        }
        buildingBody.push_back(aspc::Literal(aggregate->isNegated(),aspc::Atom(aggrIdPredicate,bodyPredicateTerms)));
        buildingHead.push_back(originalHead[0]);
        #ifdef TRACE_PARSING
            std::cout<<"Head:"<<std::endl;
            for(const aspc::Atom& l : buildingHead){
                l.print();
            }
            std::cout<<"Body:"<<std::endl;
            for(const aspc::Literal& l : buildingBody){
                l.print();
            }
        #endif
        onRule();
           
    }else{
        std::string aggrIdPredicate = "aggr_id"+std::to_string(aggrIdPredicates.size());
        aggrIdPredicates.insert(aggrIdPredicate);
        buildingHead.push_back(aspc::Atom(aggrIdPredicate,bodyPredicateTerms));
        #ifdef TRACE_PARSING
            std::cout<<"Rule for aggregate with no equal op"<<std::endl;
            std::cout<<"Head: ";
            aspc::Atom(aggrIdPredicate,bodyPredicateTerms).print();
            std::cout<<"Body: ";
        #endif
        if(bodyPredicate!=""){
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            #ifdef TRACE_PARSING
                aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)).print();
            #endif
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
        #ifdef TRACE_PARSING
            inequalitiesWithAggregate[0].print();
        #endif
        onRule();

        std::string aggrIdPredicate2 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        aggrIdPredicates.insert(aggrIdPredicate2);

        buildingHead.push_back(aspc::Atom(aggrIdPredicate2,bodyPredicateTerms));
        #ifdef TRACE_PARSING
            std::cout<<"Head: ";
            aspc::Atom(aggrIdPredicate2,bodyPredicateTerms).print();
            std::cout<<"Body: ";
        #endif
        if(bodyPredicate!=""){
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            #ifdef TRACE_PARSING
                aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)).print();
            #endif
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
        #ifdef TRACE_PARSING
            inequalitiesWithAggregate[0].print();
        #endif
        onRule();

        if(aggregate->isNegated()){
            // if(bodyPredicate!=""){
            //     buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            // }
            // buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIdPredicate,bodyPredicateTerms)));
            // onConstraint();
            // if(bodyPredicate!=""){
            //     buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            // }
            // buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIdPredicate2,bodyPredicateTerms)));
            // onConstraint();
            std::cout<<"Not supported"<<std::endl;
            exit(-1);
        }else{
            if(bodyPredicate!=""){
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(bodyPredicate,bodyPredicateTerms)));
            }
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIdPredicate,bodyPredicateTerms)));
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIdPredicate2,bodyPredicateTerms)));
            buildingHead.push_back(originalHead[0]);

            #ifdef TRACE_PARSING
                std::cout<<"Head:"<<std::endl;
                for(const aspc::Atom& l : buildingHead){
                    l.print();
                }
                std::cout<<"Body:"<<std::endl;
                for(const aspc::Literal& l : buildingBody){
                    l.print();
                }
            #endif
            rewriteRule();
        }
    }
}
void AspCore2ProgramBuilder::rewriteRule(bool aggregateRelationNotBound){

    if(!inequalitiesWithAggregate.empty()){
        rewriteRuleWithAggregate(aggregateRelationNotBound);
        return;
    }
    #ifdef TRACE_PARSING
    std::cout<<"Rewriting simple rule"<<std::endl;
    #endif
    {
        int currentHeadId = originalPredicateIDs.size();
        unordered_map<string, int>::iterator i = originalPredicateIDs.find(buildingHead[0].getPredicateName());
        if (i != originalPredicateIDs.end())
            currentHeadId = i->second;
        else {
            originalPredicateIDs[buildingHead[0].getPredicateName()] = currentHeadId;
            originalVertexByID[currentHeadId] = Vertex(currentHeadId, buildingHead[0].getPredicateName());
        }

        for (const aspc::Literal& l : buildingBody) {
            
            int currentBodyId = originalPredicateIDs.size();
            unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
            if (i != originalPredicateIDs.end())
                currentBodyId = i->second;
            else {
                originalPredicateIDs[l.getPredicateName()] = currentBodyId;
                originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());

            }
            originalVertexByID[currentBodyId].rules.push_back(program.getRulesSize());
            original_graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
        }
    }
    if(buildingBody.size()==1){
        // if the same variables occurs in two terms position rule must be rewrited
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
            // rules with one literal are simple projection
            #ifdef TRACE_PARSING
                std::cout<<"Rule not rewrited"<<std::endl;
            #endif
            onRule();
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
        onRule();
        
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
    // if (buildingBody.empty() && inequalitiesWithAggregate.empty()) {
    //     program.addFact(buildingHead.back());
        
    // } else {
    //     aspc::Rule rule = aspc::Rule(buildingHead, buildingBody, inequalities,inequalitiesWithAggregate, true,true);
    //     rule.print();
    //     program.addRule(rule);
        
    //     //adding edges to dependency graph
    //     for (const aspc::Atom& a : buildingHead) {
    //         int currentHeadId = predicateIDs.size();
    //         unordered_map<string, int>::iterator i = predicateIDs.find(a.getPredicateName());
    //         if (i != predicateIDs.end())
    //             currentHeadId = i->second;
    //         else {
    //             predicateIDs[a.getPredicateName()] = currentHeadId;
    //             vertexByID[currentHeadId] = Vertex(currentHeadId, a.getPredicateName());
    //         }
    //         vertexByID[currentHeadId].rules.push_back(rule.getRuleId());
    //         for (const aspc::Literal& l : buildingBody) {
    //             int currentBodyId = predicateIDs.size();
    //             unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
    //             if (i != predicateIDs.end())
    //                 currentBodyId = i->second;
    //             else {
    //                 predicateIDs[l.getPredicateName()] = currentBodyId;
    //                 vertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
    //             }
    //             vertexByID[currentBodyId].rules.push_back(rule.getRuleId());
    //             graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
    //         }
    //     }
    // }
    // //add predicates to program
    // for (const aspc::Atom& a : buildingHead) {
    //     program.addPredicate(a.getPredicateName(), a.getAriety());
    //     // internalPredicatesId.insert(predicateIDs[a.getPredicateName()]);
    // }
    // for (const aspc::Literal& l : buildingBody) {
    //     program.addPredicate(l.getPredicateName(), l.getAriety());
    // }

    // buildingBody.clear();
    // buildingHead.clear();
    // inequalities.clear();
    // inequalitiesWithAggregate.clear();
}

void AspCore2ProgramBuilder::onRule() {
    if (buildingBody.empty() && inequalitiesWithAggregate.empty()) {
        
        if(analyzeDependencyGraph){
            program.addFact(buildingHead.back());
        }else{
            original_program.addFact(buildingHead.back());
        }

    } else {
        aspc::Rule rule = aspc::Rule(buildingHead, buildingBody, inequalities,inequalitiesWithAggregate, true,!analyzeDependencyGraph);
        // rule.print();
        if(analyzeDependencyGraph){
            program.addRule(rule);
        }else{
            original_program.addRule(rule);
        }
        
        //adding edges to dependency graph
        for (const aspc::Atom& a : buildingHead) {
            if(analyzeDependencyGraph){
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
            }else{
                int currentHeadId = originalPredicateIDs.size();
                unordered_map<string, int>::iterator i = originalPredicateIDs.find(a.getPredicateName());
                if (i != originalPredicateIDs.end())
                    currentHeadId = i->second;
                else {
                    originalPredicateIDs[a.getPredicateName()] = currentHeadId;
                    originalVertexByID[currentHeadId] = Vertex(currentHeadId, a.getPredicateName());
                }
                originalVertexByID[currentHeadId].rules.push_back(rule.getRuleId());
                for (const aspc::Literal& l : buildingBody) {
                    int currentBodyId = originalPredicateIDs.size();
                    unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
                    if (i != originalPredicateIDs.end())
                        currentBodyId = i->second;
                    else {
                        originalPredicateIDs[l.getPredicateName()] = currentBodyId;
                        originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                    }
                    originalVertexByID[currentBodyId].rules.push_back(rule.getRuleId());
                    original_graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
                }
                for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: inequalitiesWithAggregate){
                    for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
                        int currentBodyId = originalPredicateIDs.size();
                        unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
                        if (i != originalPredicateIDs.end())
                            currentBodyId = i->second;
                        else {
                            originalPredicateIDs[l.getPredicateName()] = currentBodyId;
                            originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                        }
                        originalVertexByID[currentBodyId].rules.push_back(rule.getRuleId());
                        original_graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
                    }
                }
            }
        }
        
    }
    //add predicates to program
    for (const aspc::Atom& a : buildingHead) {
        if(analyzeDependencyGraph)
            program.addPredicate(a.getPredicateName(), a.getAriety());
        else
            original_program.addPredicate(a.getPredicateName(), a.getAriety());
            
    }
    for (const aspc::Literal& l : buildingBody) {
        if(analyzeDependencyGraph)
            program.addPredicate(l.getPredicateName(), l.getAriety());
        else
            original_program.addPredicate(l.getPredicateName(), l.getAriety());
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
    if(analyzeDependencyGraph){
        #ifdef TRACE_PARSING
        std::cout<<"---------Program---------"<<std::endl;
        for(const aspc::Rule& r:program.getRules()){
            std::cout<<"Rule "<<r.getRuleId()<<" ";
            r.print();
        }
        #endif
        std::unordered_set<std::string> constraintPredicates;
        for(const aspc::Rule& r: program.getRules()){
            if(r.isConstraint()){
                for(const aspc::Literal& l : r.getBodyLiterals()){
                    constraintPredicates.insert(l.getPredicateName());
                }
                for(const aspc::ArithmeticRelationWithAggregate& aggrReltion : r.getArithmeticRelationsWithAggregate()){
                    for(const aspc::Literal& l : aggrReltion.getAggregate().getAggregateLiterals()){
                        constraintPredicates.insert(l.getPredicateName());
                    }
                }
            }
        }
        #ifdef TRACE_PARSING
        for(const std::string& pred : constraintPredicates){
            std::cout<<"Constraint predicate: "<<pred<<std::endl;
        }
        #endif
        std::unordered_set<unsigned> labeledComponents;
        std::vector<unsigned> visitingComponents;
        std::unordered_map<unsigned,unsigned> predicateToComponent;
        const std::vector<std::vector<int>> scc = graphWithTarjanAlgorithm.SCC();
        for(unsigned componentId = 0; componentId<scc.size(); componentId++){
            for(unsigned predicateId : scc[componentId]){
                #ifdef TRACE_PARSING
                    std::cout<<"Component: "<<vertexByID[predicateId].name<<std::endl;
                #endif
                
                predicateToComponent[predicateId]=componentId;
                if(constraintPredicates.count(vertexByID[predicateId].name)!=0){
                    labeledComponents.insert(componentId);
                    visitingComponents.push_back(componentId);
                    #ifdef TRACE_PARSING
                    std::cout<<"Added to visit"<<std::endl;
                    #endif
                }
            }
        }
        while(!visitingComponents.empty()){
            unsigned componentId = visitingComponents.back();
            visitingComponents.pop_back();
            #ifdef TRACE_PARSING
            std::cout<<"Visiting component: "<<vertexByID[scc[componentId][0]].name<<std::endl;
            #endif
            for(unsigned ruleId : vertexByID[scc[componentId][0]].rules){
                const aspc::Rule* r = &program.getRule(ruleId);
                #ifdef TRACE_PARSING
                std::cout<<"Checking rule for component: ";r->print();
                #endif
                if(!r->isConstraint() && r->getHead()[0].getPredicateName() == vertexByID[scc[componentId][0]].name){
                    for(const aspc::Literal& l : r->getBodyLiterals()){
                        if(labeledComponents.count(predicateToComponent[predicateIDs[l.getPredicateName()]])==0){
                            visitingComponents.push_back(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                            labeledComponents.insert(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                        }
                    }
                    for(const aspc::ArithmeticRelationWithAggregate& aggrRelation : r->getArithmeticRelationsWithAggregate()){
                        for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                            if(labeledComponents.count(predicateToComponent[predicateIDs[l.getPredicateName()]])==0){
                                visitingComponents.push_back(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                                labeledComponents.insert(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                            }
                        }
                    }
                }
            }   
        }

        analyzeDependencyGraph=false;
        arietyMap.clear();
        std::unordered_set<unsigned> rewritedRules;
        std::unordered_set<unsigned> noRewritedRules;
        for(unsigned i=0; i<scc.size(); i++){
            if(labeledComponents.count(i)==0){
                for(unsigned ruleId: vertexByID[scc[i][0]].rules){
                    if(noRewritedRules.count(ruleId)==0){
                        #ifdef TRACE_PARSING
                        std::cout<<"rule without completion ";program.getRule(ruleId).print();
                        #endif
                        ruleWithoutCompletion.push_back(program.getRule(ruleId));
                        noRewritedRules.insert(ruleId);
                    }
                }
            }else{
                for(unsigned ruleId: vertexByID[scc[i][0]].rules){
                    if(rewritedRules.count(ruleId)==0){
                        #ifdef TRACE_PARSING
                        std::cout<<"rewriting ";program.getRule(ruleId).print();
                        #endif
                        buildingHead.clear();
                        buildingBody.clear();
                        inequalities.clear();
                        inequalitiesWithAggregate.clear();
                        const aspc::Rule* r = &program.getRule(ruleId);
                        if(r->isConstraint() || r->getHead()[0].getPredicateName() != vertexByID[scc[i][0]].name)
                            continue;
                        rewritedRules.insert(ruleId);
                        for(const aspc::Atom& a : r->getHead()){
                            buildingHead.push_back(a);
                        }
                        for(const aspc::Literal& l : r->getBodyLiterals()){
                            buildingBody.push_back(l);
                        }
                        for(const aspc::ArithmeticRelation& ineq: r->getArithmeticRelations()){
                            inequalities.push_back(ineq);
                        }
                        for(const aspc::ArithmeticRelationWithAggregate& ineq: r->getArithmeticRelationsWithAggregate()){
                            inequalitiesWithAggregate.push_back(ineq);
                        }
                        rewriteRuleWithCompletion();
                    }
                }
            }
        }
        for(const aspc::Rule& r: program.getRules()){
            if(r.isConstraint()){
                buildingHead.clear();
                buildingBody.clear();
                inequalities.clear();
                inequalitiesWithAggregate.clear();
                for(const aspc::Atom& a : r.getHead()){
                    buildingHead.push_back(a);
                }
                for(const aspc::Literal& l : r.getBodyLiterals()){
                    buildingBody.push_back(l);
                }
                for(const aspc::ArithmeticRelation& ineq: r.getArithmeticRelations()){
                    inequalities.push_back(ineq);
                }
                for(const aspc::ArithmeticRelationWithAggregate& aggr: r.getArithmeticRelationsWithAggregate()){
                    inequalitiesWithAggregate.push_back(aggr);
                }
                rewriteRuleWithCompletion();
            }
        }
        #ifdef TRACE_PARSING
        std::cout<<"Program with completion"<<std::endl;
        for(const aspc::Rule& r:original_program.getRules()){
            std::cout<<"Rule "<<r.getRuleId()<<" ";
            r.print();
        }
        std::cout<<"Program without completion"<<std::endl;
        #endif
        for(const aspc::Rule& r: ruleWithoutCompletion){
            for(const aspc::Atom& a : r.getHead()){
                original_program.addPredicate(a.getPredicateName(),a.getAriety());
            }
            for(const aspc::Literal& l : r.getBodyLiterals()){
                original_program.addPredicate(l.getPredicateName(),l.getAriety());
            }
            for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: r.getArithmeticRelationsWithAggregate()){
                    for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                    original_program.addPredicate(l.getPredicateName(),l.getAriety());
                }
            }
            #ifdef TRACE_PARSING
                std::cout<<"Rule "<<r.getRuleId()<<" ";
                r.print();
            #endif
        }
        buildGraphNoCompletion();
        
        // std::vector<std::vector<int>> sccc = original_graphWithTarjanAlgorithm.SCC();
        // for(int component=sccc.size()-1; component>=0 ; component--){
        //     for(unsigned predId : sccc[component]){
        //         auto it = originalVertexByID.find(sccc[component][0]);
        //         if(it!=originalVertexByID.end()){
        //             std::cout<<it->second.name<<std::endl;
        //         }
        //     }
        // }
    }
    for(auto& pair: aggrSetToAuxVal){
        // std::cout<<"Adding manual dependecy "<<pair.first<<" "<<pair.second<<std::endl;
        int currentHeadId = predicateIDs.size();
        unordered_map<string, int>::iterator itAuxVal = originalPredicateIDs.find(pair.second);
        if (itAuxVal != originalPredicateIDs.end())
            currentHeadId = itAuxVal->second;
        else {
            originalPredicateIDs[pair.second] = currentHeadId;
            originalVertexByID[currentHeadId] = Vertex(currentHeadId, pair.second);
        }

        int currentBodyId = originalPredicateIDs.size();
        unordered_map<string, int>::iterator itAggrSet = originalPredicateIDs.find(pair.first);
        if (itAggrSet != originalPredicateIDs.end())
            currentBodyId = itAggrSet->second;
        else {
            originalPredicateIDs[pair.first] = currentBodyId;
            originalVertexByID[currentBodyId] = Vertex(currentBodyId, pair.first);
        }
        original_graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
    }
    for(auto& auxToBody : auxPredicateToBody){
        int currentHeadId = predicateIDs.size();
        unordered_map<string, int>::iterator itAuxVal = originalPredicateIDs.find(auxToBody.first);
        if (itAuxVal != originalPredicateIDs.end())
            currentHeadId = itAuxVal->second;
        else {
            originalPredicateIDs[auxToBody.first] = currentHeadId;
            originalVertexByID[currentHeadId] = Vertex(currentHeadId, auxToBody.first);
        }
        for(const aspc::Literal& l: auxToBody.second){
            // std::cout<<"Adding manual dependecy "<<auxToBody.first<<" "<<l.getPredicateName()<<std::endl;
            int currentBodyId = originalPredicateIDs.size();
            unordered_map<string, int>::iterator itAggrSet = originalPredicateIDs.find(l.getPredicateName());
            if (itAggrSet != originalPredicateIDs.end())
                currentBodyId = itAggrSet->second;
            else {
                originalPredicateIDs[l.getPredicateName()] = currentBodyId;
                originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
            }
            original_graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
        }
        
    }
    #ifdef TRACE_PARSING
        std::cout<<"Original Program"<<std::endl;
        for(const aspc::Rule& r:original_program.getRules()){
            std::cout<<"Rule "<<r.getRuleId()<<" ";
            r.print();
        }
        exit(180);
    #endif
    return original_program;
}
bool AspCore2ProgramBuilder::isPredicateBodyNoCompletion(int predId)const{
    return predicateBodyNoCompletion.count(predId)!=0;
           
}
void AspCore2ProgramBuilder::buildGraphNoCompletion(){
    // std::cout<<"buildGraphNoCompletion"<<std::endl;
    for(const aspc::Rule& r: ruleWithoutCompletion){
        // r.print();
        for (const aspc::Atom& a : r.getHead()) {
            int currentHeadId = predicateIDsNoCompletion.size();
            unordered_map<string, int>::iterator i = predicateIDsNoCompletion.find(a.getPredicateName());
            if (i != predicateIDsNoCompletion.end())
                currentHeadId = i->second;
            else {
                predicateIDsNoCompletion[a.getPredicateName()] = currentHeadId;
                vertexByIDNoCompletion[currentHeadId] = Vertex(currentHeadId, a.getPredicateName());
            }
            vertexByIDNoCompletion[currentHeadId].rules.push_back(r.getRuleId());
            for (const aspc::Literal& l : r.getBodyLiterals()) {
                int currentBodyId = predicateIDsNoCompletion.size();
                unordered_map<string, int>::iterator i = predicateIDsNoCompletion.find(l.getPredicateName());
                if (i != predicateIDsNoCompletion.end())
                    currentBodyId = i->second;
                else {
                    predicateIDsNoCompletion[l.getPredicateName()] = currentBodyId;
                    vertexByIDNoCompletion[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                }
                predicateBodyNoCompletion.insert(currentBodyId);
                // vertexByIDNoCompletion[currentBodyId].rules.push_back(r.getRuleId());
                graphWithTarjanAlgorithmNoCompletion.addEdge(currentBodyId, currentHeadId);
                // std::cout<<"Adding dependency"<<std::endl;
            }
            for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: r.getArithmeticRelationsWithAggregate()){
                for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
                    int currentBodyId = predicateIDsNoCompletion.size();
                    unordered_map<string, int>::iterator i = predicateIDsNoCompletion.find(l.getPredicateName());
                    if (i != predicateIDsNoCompletion.end())
                        currentBodyId = i->second;
                    else {
                        predicateIDsNoCompletion[l.getPredicateName()] = currentBodyId;
                        vertexByIDNoCompletion[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
                    }
                    predicateBodyNoCompletion.insert(currentBodyId);
                    // vertexByIDNoCompletion[currentBodyId].rules.push_back(r.getRuleId());
                    graphWithTarjanAlgorithmNoCompletion.addEdge(currentBodyId, currentHeadId);
                    // std::cout<<"Adding dependency"<<std::endl;
                }
            }
        }
    }
}
void AspCore2ProgramBuilder::rewriteConstraint(){
    if(inequalitiesWithAggregate.empty()){
        onConstraint();
    }else{
        bool writeBodyRule=false;
        bool writeAggrSetRule=false;
        preprocess(writeBodyRule,writeAggrSetRule);

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
            rewriteRule();
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
                // std::cout<<previousAggrSet.first<<std::endl;
                
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
                rewriteRule();
            }
                
            
        }else{
            if(!originalAggrRelation[0].getAggregate().getAggregateLiterals().empty()){
                aggrSetPredicate=originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getPredicateName();
                for(unsigned i=0; i<originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getAriety(); i++){
                    aggrSetPredicateTerms.push_back(originalAggrRelation[0].getAggregate().getAggregateLiterals()[0].getTermAt(i));
                }
                original_program.addAggregatePredicate(aggrSetPredicate,aggrSetPredicateTerms.size());
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
    }
}
void AspCore2ProgramBuilder::rewriteRuleWithCompletion(bool aggregateRelationNotBound){
    if(!buildingHead.empty()){
        rewriteRule();
    }else{
        rewriteConstraint();
    }
}
void AspCore2ProgramBuilder::addRuleToOriginalProgram(){
    // aspc::Rule rule(buildingHead,buildingBody,inequalities,inequalitiesWithAggregate,true,false);
    // original_program.addRule(rule);
    // if(!buildingHead.empty()){
    //     for (const aspc::Atom& a : buildingHead) {
    //         int currentHeadId = originalPredicateIDs.size();
    //         unordered_map<string, int>::iterator i = originalPredicateIDs.find(a.getPredicateName());
    //         if (i != originalPredicateIDs.end())
    //             currentHeadId = i->second;
    //         else {
    //             originalPredicateIDs[a.getPredicateName()] = currentHeadId;
    //             originalVertexByID[currentHeadId] = Vertex(currentHeadId, a.getPredicateName());
    //         }
    //         originalVertexByID[currentHeadId].rules.push_back(rule.getRuleId());
    //         for (const aspc::Literal& l : buildingBody) {
    //             int currentBodyId = originalPredicateIDs.size();
    //             unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
    //             if (i != originalPredicateIDs.end())
    //                 currentBodyId = i->second;
    //             else {
    //                 originalPredicateIDs[l.getPredicateName()] = currentBodyId;
    //                 originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
    //             }
    //             originalVertexByID[currentBodyId].rules.push_back(rule.getRuleId());
    //             graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
    //         }
    //         if(!inequalitiesWithAggregate.empty()){
    //             for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: inequalitiesWithAggregate){
    //                 for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
    //                     int currentBodyId = originalPredicateIDs.size();
    //                     unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
    //                     if (i != originalPredicateIDs.end())
    //                         currentBodyId = i->second;
    //                     else {
    //                         originalPredicateIDs[l.getPredicateName()] = currentBodyId;
    //                         originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
    //                     }
    //                     originalVertexByID[currentBodyId].rules.push_back(rule.getRuleId());
    //                     graphWithTarjanAlgorithm.addEdge(currentBodyId, currentHeadId);
    //                 }
    //             }
    //         }
            
    //     }
    // }else{
    //     for (const aspc::Literal& l : buildingBody) {
    //         int currentBodyId = originalPredicateIDs.size();
    //         unordered_map<string, int>::iterator i = originalPredicateIDs.find(l.getPredicateName());
    //         if (i != originalPredicateIDs.end())
    //             currentBodyId = i->second;
    //         else {
    //             originalPredicateIDs[l.getPredicateName()] = currentBodyId;
    //             originalVertexByID[currentBodyId] = Vertex(currentBodyId, l.getPredicateName());
    //         }
    //     }
    // }
}
const map<string, unsigned> & AspCore2ProgramBuilder::getArietyMap() {
    return arietyMap;
}

GraphWithTarjanAlgorithm& AspCore2ProgramBuilder::getGraphWithTarjanAlgorithm() {
    if(analyzeDependencyGraph)
        return graphWithTarjanAlgorithm;
    return original_graphWithTarjanAlgorithm;
}

const unordered_map<int, Vertex>& AspCore2ProgramBuilder::getVertexByIDMap() const {
    if(analyzeDependencyGraph)
        return vertexByID;
    return originalVertexByID;
}

const unordered_map<string, int>& AspCore2ProgramBuilder::getPredicateIDsMap() const {
    if(analyzeDependencyGraph)
        return predicateIDs;
    return originalPredicateIDs;
}



