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
const aspc::Literal* AspCore2ProgramBuilder::getSupportingHead(std::string pred){
    for(const auto& support : supportPredicates){
        unsigned headId=0;
        for(std::string supPred : support.second){
            if(pred==supPred){
                return &predsToHeads[support.first][headId];
            }
            headId++;
        }
    }
    return NULL;
}
void AspCore2ProgramBuilder::rewriteRule(bool addDomBody){

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
    bool headInMoreRules=predsToRules.count(buildingHead[0].getPredicateName())!=0 && predsToRules[buildingHead[0].getPredicateName()].size()>1;
    if(buildingBody.size()==1 && inequalities.empty()){
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
        if(!conditionOnLiteral){
            // rules with one literal are simple projection
            #ifdef TRACE_PARSING
                std::cout<<"Rule not rewrited"<<std::endl;
            #endif
            if(headInMoreRules){
                std::string supPredicate = "sup_"+std::to_string(supportPredicates.size());
                supportPredicates[buildingHead[0].getPredicateName()].push_back(supPredicate);
                predsToHeads[buildingHead[0].getPredicateName()].push_back(aspc::Literal(false,buildingHead[0]));
                std::vector<std::string> terms(buildingHead[0].getTerms());
                buildingHead.clear();
                buildingHead.push_back(aspc::Atom(supPredicate,terms));
            }
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
            if(auxTerms.count(headAtom.getTermAt(k))==0 && headAtom.isVariableTermAt(k)){
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
        if(ineq.isBoundedValueAssignment(auxTerms)){
            std::string assignedVar = ineq.getAssignedVariable(auxTerms);
            if(auxTerms.count(assignedVar)==0){
                auxTerms.insert(assignedVar);
                auxDistinctTerms.push_back(assignedVar);
            }
        }
    }
    for(std::string term : auxDistinctTerms){
        auxLiteralTerms[auxPredicate].push_back(term);
    }
    bool iffCase = false;
    
    //iff optimization could be applied only if the head appears only in one rule
    if(!headInMoreRules){
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
    }
    
    
    if(!iffCase){
        buildingBody.clear();
        buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicate,auxDistinctTerms)));
        inequalities.clear();
        if(headInMoreRules){
            std::string supPredicate = "sup_"+std::to_string(supportPredicates.size());
            supportPredicates[buildingHead[0].getPredicateName()].push_back(supPredicate);
            predsToHeads[buildingHead[0].getPredicateName()].push_back(aspc::Literal(false,buildingHead[0]));
            std::vector<std::string> terms(buildingHead[0].getTerms());
            buildingHead.clear();
            buildingHead.push_back(aspc::Atom(supPredicate,terms));
        }
        //head:-aux
        onRule(); 
    }
    
    for(const aspc::Literal& literal : originalBody){
        if(domPredicate.count(literal.getPredicateName())==0){
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxPredicate,auxDistinctTerms)));
            buildingBody.push_back(aspc::Literal(!literal.isNegated(),literal.getAtom()));
            //:-aux, not lit
            onConstraint();
        }
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
    for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: inequalitiesWithAggregate){
        for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
            if(analyzeDependencyGraph)
                program.addAggregatePredicate(l.getPredicateName(), l.getAriety());
            else
                original_program.addAggregatePredicate(l.getPredicateName(), l.getAriety());
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
void AspCore2ProgramBuilder::labelComponents(std::unordered_set<unsigned>& labeledComponent,const std::vector<std::vector<int>>& scc){
    
    std::vector<unsigned> visitingComponents;
    std::unordered_map<unsigned,unsigned> componentToPredicate;
    std::unordered_map<unsigned,unsigned> predicateToComponent;
    //etichetto tutte le componenti che appaiono in un constraint
    for(unsigned componentId = 0; componentId<scc.size(); componentId++){
        for(unsigned predicateId : scc[componentId]){
            componentToPredicate[componentId]=predicateId;
            predicateToComponent[predicateId]=componentId;
            std::string currentPredicateName = vertexByID[predicateId].name;
            if(labeledComponent.count(componentId)==0){
                bool appearInConstraint=false;
                for(const aspc::Rule& r : program.getRules()){
                    if(r.isConstraint()){
                        for(const aspc::Literal& l : r.getBodyLiterals()){
                            if(l.getPredicateName() == currentPredicateName){
                                appearInConstraint=true;
                                break;
                            }
                        }
                        if(r.containsAggregate()){
                            for(const aspc::Literal& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()){
                                if(l.getPredicateName() == currentPredicateName){
                                    appearInConstraint=true;
                                    break;
                                }
                            }   
                        }
                        if(appearInConstraint)
                            break;
                    }
                }
                if(appearInConstraint){
                    labeledComponent.insert(componentId);
                    visitingComponents.push_back(componentId);
                }
            }

        }
    }
    
    while (!visitingComponents.empty()){
        unsigned currentComponent = visitingComponents.back();
        visitingComponents.pop_back();
        std::string currentPredicateName = vertexByID[componentToPredicate[currentComponent]].name;
        for(const aspc::Rule& r : program.getRules()){
            if(!r.isConstraint() && r.getHead()[0].getPredicateName() == vertexByID[componentToPredicate[currentComponent]].name){
                for(const aspc::Literal& l : r.getBodyLiterals()){
                    if(labeledComponent.count(predicateToComponent[predicateIDs[l.getPredicateName()]])==0){
                        visitingComponents.push_back(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                        labeledComponent.insert(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                    }
                }
                for(const aspc::ArithmeticRelationWithAggregate& aggrRelation : r.getArithmeticRelationsWithAggregate()){
                    for(const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()){
                        if(labeledComponent.count(predicateToComponent[predicateIDs[l.getPredicateName()]])==0){
                            visitingComponents.push_back(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                            labeledComponent.insert(predicateToComponent[predicateIDs[l.getPredicateName()]]);
                        }
                    }
                }
            }
        }
    }

}
void AspCore2ProgramBuilder::analyzeInputProgram(){
    std::unordered_set<unsigned> labeledComponents;
    const std::vector<std::vector<int>> scc = graphWithTarjanAlgorithm.SCC();

    labelComponents(labeledComponents,scc);
    analyzeDependencyGraph=false;
    arietyMap.clear();
    std::unordered_set<unsigned> rewritedRules;
    std::unordered_set<unsigned> noRewritedRules;
    
    unsigned ruleId=0;
    for(const aspc::Rule& r: program.getRules()){
        if(!r.isConstraint()){
            predsToRules[r.getHead()[0].getPredicateName()].push_back(ruleId);
        }
        ruleId++;
    }
    for(const aspc::Rule& r: program.getRules()){
        if(!r.isConstraint()){
            for(int i=scc.size()-1; i>=0; i--){
                if(vertexByID[scc[i][0]].name == r.getHead()[0].getPredicateName()){
                    if(labeledComponents.count(i) == 0){
                        if(noRewritedRules.count(r.getRuleId())==0){
                            ruleWithoutCompletion.push_back(r);
                            noRewritedRules.insert(r.getRuleId());
                        }
                    }else{
                        if(rewritedRules.count(r.getRuleId())==0){
                            rewritedRules.insert(r.getRuleId());
                            rewriteRuleWithCompletion(r);
                        }
                    }
                }
            } 
        }else{
            rewriteRuleWithCompletion(r);
        }
    }
    buildConstraintDuplicateHeads();
    return;
}
void AspCore2ProgramBuilder::buildConstraintDuplicateHeads(){
    for(const auto& predsHeads : predsToHeads){
        const aspc::Literal* reference_head = &predsHeads.second[0];
        std::vector<std::string> terms;
        for(unsigned i=0;i<reference_head->getAriety();i++){
            terms.push_back("X"+std::to_string(i));
        }
        unsigned headId=0;
        for(const aspc::Literal& head : predsHeads.second){
            clearData();
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(supportPredicates[predsHeads.first][headId],terms)));
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(head.getPredicateName(),terms)));
            onConstraint();
            headId++;
        }
        clearData();
        headId=0;
        
        buildingBody.push_back(aspc::Literal(false,aspc::Atom(reference_head->getPredicateName(),terms)));
        for(const aspc::Literal& head : predsHeads.second){
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(supportPredicates[predsHeads.first][headId],terms)));
            headId++;
        }
        
        onConstraint();
    }
}
void AspCore2ProgramBuilder::clearData(){
    buildingHead.clear();
    buildingBody.clear();
    inequalities.clear();
    inequalitiesWithAggregate.clear();
}

//aggregateBodyVariables must contains also variables appearing in the aggregate guard
std::pair<bool,std::pair<std::string,AggrSetPredicate>> AspCore2ProgramBuilder::buildBody(std::unordered_set<std::string> aggregateBodyVariables,const aspc::Rule& r,std::string auxValPred,std::vector<std::string> auxValTerm){
    unsigned bodySize = auxValPred!="" ? r.getBodyLiterals().size()+1 : r.getBodyLiterals().size();
    bool writeRule = bodySize > 1 || r.getArithmeticRelations().size() > 0;
    std::vector<aspc::Literal> ruleBody(r.getBodyLiterals());
    std::vector<aspc::ArithmeticRelation> ruleInequalities(r.getArithmeticRelations());
    std::unordered_set<std::string> headVars;
    if(!r.isConstraint()){
        const aspc::Literal* lHead = r.getHead().empty() ? NULL : new aspc::Literal(false,r.getHead()[0]);
        lHead->addVariablesToSet(headVars);
    }
    if(!writeRule){
        // body with at most one literal
        if(!ruleBody.empty()){
            const aspc::Literal* l = &ruleBody[0];
            
            for(unsigned i=0; i<l->getAriety(); i++){
                std::string v = l->getTermAt(i);
                if(l->isVariableTermAt(i) && aggregateBodyVariables.count(v)==0 && headVars.count(v)==0){
                    writeRule=true;
                    break;
                }
            }
        }
    }

    std::string bodyPredicate = "body"+std::to_string(bodyPredicates.size());
    AggrSetPredicate body; 
    if(writeRule){
        clearData();
        std::unordered_set<std::string> distictBodyTerms;
        if(auxValPred!=""){
            if(distictBodyTerms.count(auxValTerm[0])==0){
                distictBodyTerms.insert(auxValTerm[0]);
                body.addTerm(auxValTerm[0]);
            }
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxValPred,auxValTerm)));
        }
        if(!r.isConstraint()){
            const aspc::Literal* lHead = r.getHead().empty() ? NULL : new aspc::Literal(false,r.getHead()[0]);
            for(unsigned i=0; i<lHead->getAriety(); i++){
                if(lHead->isVariableTermAt(i) && distictBodyTerms.count(lHead->getTermAt(i))==0){
                    distictBodyTerms.insert(lHead->getTermAt(i));
                    body.addTerm(lHead->getTermAt(i));
                }
            }
        }
        for(const aspc::Literal& l : ruleBody){
            buildingBody.push_back(aspc::Literal(l));
            for(unsigned i=0; i<l.getAriety(); i++){
                if(l.isVariableTermAt(i) && aggregateBodyVariables.count(l.getTermAt(i))!=0 && distictBodyTerms.count(l.getTermAt(i))==0){
                    distictBodyTerms.insert(l.getTermAt(i));
                    body.addTerm(l.getTermAt(i));
                }
            }
        }
        for(const aspc::ArithmeticRelation& l : ruleInequalities){
            inequalities.push_back(aspc::ArithmeticRelation(l));
            for(std::string v : l.getLeft().getAllTerms()){
                if(isVariable(v) && aggregateBodyVariables.count(v)!=0 && distictBodyTerms.count(v)==0){
                    distictBodyTerms.insert(v);
                    body.addTerm(v);
                }
            }
            for(std::string v : l.getRight().getAllTerms()){
                if(isVariable(v) && aggregateBodyVariables.count(v)!=0 && distictBodyTerms.count(v)==0){
                    distictBodyTerms.insert(v);
                    body.addTerm(v);
                }
            }
        }
        bodyPredicates.insert(bodyPredicate);
        buildingHead.push_back(aspc::Atom(bodyPredicate,body.getTerms()));
        rewriteRule();
    }else{
        if(!ruleBody.empty()){
            const aspc::Literal* literal = &ruleBody[0];
            bodyPredicate=literal->getPredicateName();
            for(unsigned i=0; i<literal->getAriety(); i++){
                body.addTerm(literal->getTermAt(i));
            }
        }else{
            if(auxValPred!=""){
                bodyPredicate=auxValPred;
                body.addTerm(auxValTerm[0]);
            }else{
                bodyPredicate="";
            }
        }
    }
    return std::pair<bool,std::pair<std::string,AggrSetPredicate>>(writeRule,std::pair<std::string,AggrSetPredicate>(bodyPredicate,body));
}
std::pair<bool,std::pair<std::string,AggrSetPredicate>> AspCore2ProgramBuilder::buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation,std::string domPred,std::vector<std::string> domTerm){
    bool writeRule = aggregareRelation.getAggregate().getAggregateLiterals().size()>1 || aggregareRelation.getAggregate().getAggregateInequalities().size()>0;
    std::vector<aspc::Literal> aggregateLiterals(aggregareRelation.getAggregate().getAggregateLiterals());
    std::vector<aspc::ArithmeticRelation> aggregateInequalities(aggregareRelation.getAggregate().getAggregateInequalities());
    std::vector<std::string> aggregateVariables(aggregareRelation.getAggregate().getAggregateVariables());
    if(!writeRule){
        const aspc::Literal* l = &aggregateLiterals[0];
        for(unsigned i=0;i<l->getAriety();i++){
            if(l->isVariableTermAt(i)){
                bool found=false;
                for(std::string v : aggregateVariables){
                    if(v == l->getTermAt(i)){
                        found=true;
                        break;
                    } 
                }
                if(!found){
                    if(bodyVariables.count(l->getTermAt(i))!=0)
                        found=true;
                    else{
                        writeRule=true;
                        break;
                    }
                }
            }
        }
        if(!writeRule){
            for(unsigned i=0;i<l->getAriety() && !writeRule;i++){
                for(unsigned j=i+1;j<l->getAriety() && !writeRule;j++){
                    if(l->isVariableTermAt(i) && l->isVariableTermAt(j) && l->getTermAt(i)==l->getTermAt(j)){
                        writeRule=true;
                    }
                }
            }
        }
    }
    std::string aggregateSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
    AggrSetPredicate aggrSet;
    if(writeRule){
        clearData();
        std::unordered_set<string> aggrSetDistinctTerms;
        for(std::string v :aggregareRelation.getAggregate().getAggregateVariables()){
            if(aggrSetDistinctTerms.count(v)==0){
                aggrSetDistinctTerms.insert(v);
                aggrSet.addTerm(v);
            }
        }
        std::unordered_set<std::string> aggrBodyVars;
        for(const aspc::Literal& l:aggregateLiterals){
            if(l.isPositiveLiteral()){
                l.addVariablesToSet(aggrBodyVars);
            }
            for(unsigned i=0; i<l.getAriety(); i++){
                std::string v = l.getTermAt(i);
                if(l.isVariableTermAt(i) && bodyVariables.count(v)!=0 && aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            aggrSet.addLiteral(l);
            buildingBody.push_back(aspc::Literal(l));
        }
        
        
        for(const aspc::ArithmeticRelation& l:aggregateInequalities){
            
            for(std::string v : l.getLeft().getAllTerms()){
                if(isVariable(v) && bodyVariables.count(v)!=0 && aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            
            for(std::string v : l.getRight().getAllTerms()){
                if(isVariable(v) && bodyVariables.count(v)!=0 && aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            inequalities.push_back(aspc::ArithmeticRelation(l));
            aggrSet.addInequality(l);
        }

        bool sharedAggrSet=false;
        for(const auto& previous:aggrSetPredicates){
            if(aggrSet == previous.second){
                aggregateSetPredicate=previous.first;
                sharedAggrSet=true;
                break;
            }
        }
        if(!sharedAggrSet){
            aggrSetPredicates[aggregateSetPredicate]=aggrSet;
            if(domPred != ""){
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(domPred,domTerm)));
            }
            buildingHead.push_back(aspc::Atom(aggregateSetPredicate,aggrSet.getTerms()));
            rewriteRule();
            // aggrSet.setBodyDomain(domPredicate.back());
        }
        
    }else{

        //Aggregate contains only one bound literal considering body variables and aggregation variables
        
        const aspc::Literal* literal = &aggregateLiterals[0];
        aggregateSetPredicate=literal->getPredicateName();
        for(unsigned i=0; i<literal->getAriety(); i++){
            aggrSet.addTerm(literal->getTermAt(i));
        }
    }
    return std::pair<bool,std::pair<std::string,AggrSetPredicate>>(writeRule,std::pair<std::string,AggrSetPredicate>(aggregateSetPredicate,aggrSet));
}
void AspCore2ProgramBuilder::rewriteConstraint(const aspc::Rule& r){
    
    
}
std::vector<std::string> AspCore2ProgramBuilder::writeAggrIdRule(std::pair<bool,std::pair<std::string,AggrSetPredicate>> body,std::pair<bool,std::pair<std::string,AggrSetPredicate>> aggrSet,const aspc::Rule& r){
    const aspc::ArithmeticRelationWithAggregate* aggregate = &r.getArithmeticRelationsWithAggregate()[0];
    bool plusOne = aggregate->getComparisonType() != aspc::EQ && aggregate->isPlusOne();
    std::string aggrId0;
    std::string aggrId1;
    if(aggregate->getComparisonType() != aspc::EQ){
        clearData();
        if(body.second.first != "")
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
            false,
            aggregate->getGuard(),
            aspc::Aggregate(
                {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
                {},
                aggregate->getAggregate().getAggregateVariables(),
                aggregate->getAggregate().getAggregateFunction()),
            aggregate->getComparisonType(),
            false)
        );    
        inequalitiesWithAggregate[0].setPlusOne(aggregate->isPlusOne());
        aggrId0 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        buildingHead.push_back(aspc::Atom(aggrId0,body.second.second.getTerms()));
        aggrIdPredicates.insert(aggrId0);
        onRule();
    }else{
        aspc::ComparisonType cmp = aggregate->isNegated()  ? aspc::GT : aspc::GTE;
        clearData();
        if(body.second.first != "")
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
            false,
            aggregate->getGuard(),
            aspc::Aggregate(
                {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
                {},
                aggregate->getAggregate().getAggregateVariables(),
                aggregate->getAggregate().getAggregateFunction()),
            cmp,
            false)
        );    
        aggrId0 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        buildingHead.push_back(aspc::Atom(aggrId0,body.second.second.getTerms()));
        aggrIdPredicates.insert(aggrId0);
        onRule();
        aspc::ComparisonType cmp2 = aggregate->isNegated() ? aspc::LT : aspc::LTE;
        if(body.second.first != "")
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
            false,
            aggregate->getGuard(),
            aspc::Aggregate(
                {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
                {},
                aggregate->getAggregate().getAggregateVariables(),
                aggregate->getAggregate().getAggregateFunction()),
            cmp2,
            false)
        );    
        aggrId1 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        buildingHead.push_back(aspc::Atom(aggrId1,body.second.second.getTerms()));
        aggrIdPredicates.insert(aggrId1);
        onRule();
    }
    std::vector<std::string> aggrIds({aggrId0});
    if(aggrId1!=""){
        aggrIds.push_back(aggrId1);
    }
    return aggrIds;
}
void AspCore2ProgramBuilder::rewriteRuleWithCompletion(const aspc::Rule& r){
    // std::cout << "rewriting ";r.print();
    if(!r.isConstraint()){
        printingPredicate.insert(r.getHead()[0].getPredicateName());
    }
    if(!r.containsAggregate()){
        for(const aspc::Literal& l:r.getBodyLiterals()){
            buildingBody.push_back(aspc::Literal(l));
        }
        for(const aspc::ArithmeticRelation& l:r.getArithmeticRelations()){
            inequalities.push_back(aspc::ArithmeticRelation(l));
        }
        for(const aspc::Atom& a:r.getHead()){
            buildingHead.push_back(aspc::Atom(a));
        }
        
        if(r.isConstraint())
            onConstraint();
        else
            rewriteRule();
        return;
    }
    //constraint contains aggregate
    // std::cout<<"Rewriting rule with aggregate"<<std::endl;
    //building aggr_set
    std::unordered_set<std::string> bodyVariables;
    for(const aspc::Literal& l : r.getBodyLiterals()){
        l.addVariablesToSet(bodyVariables);
    }
    for(const aspc::ArithmeticRelation& l : r.getArithmeticRelations()){
        l.addVariablesToSet(bodyVariables);
    }

    std::unordered_set<std::string> aggregateBodyVariables;
    std::unordered_set<std::string> aggregatePositiveBodyVariables;
    for(const aspc::Literal& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()){
        l.addVariablesToSet(aggregateBodyVariables);
        if(l.isPositiveLiteral()){
            l.addVariablesToSet(aggregatePositiveBodyVariables);
        }
    }
    for(const aspc::ArithmeticRelation& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateInequalities()){
        l.addVariablesToSet(aggregateBodyVariables);
        if(l.isBoundedValueAssignment(aggregatePositiveBodyVariables)){
            aggregatePositiveBodyVariables.insert(l.getAssignedVariable(aggregatePositiveBodyVariables));
        }
    }
    std::unordered_set<std::string> guardVar;
    for(std::string v : r.getArithmeticRelationsWithAggregate()[0].getGuard().getAllTerms()){
        aggregateBodyVariables.insert(v);
        guardVar.insert(v);
    }
    std::unordered_set<std::string> domDistinctTerms;
    for(const aspc::Literal& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()){
        if(l.isNegated()){
            for(unsigned k=0;k<l.getAriety();k++){
                if(l.isVariableTermAt(k) && aggregatePositiveBodyVariables.count(l.getTermAt(k))==0){
                    domDistinctTerms.insert(l.getTermAt(k));
                }
            }
        }
    }
    for(const aspc::ArithmeticRelation& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateInequalities()){
        for(std::string term: l.getLeft().getAllTerms()){
            if(isVariable(term) && aggregatePositiveBodyVariables.count(term)==0){
                domDistinctTerms.insert(term);
            }
        }
        for(std::string term: l.getRight().getAllTerms()){
            if(isVariable(term) && aggregatePositiveBodyVariables.count(term)==0){
                domDistinctTerms.insert(term);
            }
        }
        
    }
    std::vector<std::string> domBodyTerms;
    std::string domPred="";
    if(!domDistinctTerms.empty()){
        domPred="dom"+std::to_string(domPredicate.size());
        domPredicate.insert(domPred);
        for(std::string v : domDistinctTerms){
            domBodyTerms.push_back(v);
        }
        domToTerms.insert({domPred,domBodyTerms});
    }
    


    auto aggrSet = buildAggregateSet(bodyVariables,r.getArithmeticRelationsWithAggregate()[0],domPred,domBodyTerms);
    std::string auxValPredicate="";
    std::vector<std::string> auxValTerm;
    if(!r.getArithmeticRelationsWithAggregate()[0].isBoundedRelation(bodyVariables) && r.getArithmeticRelationsWithAggregate()[0].getComparisonType() == aspc::EQ){
        if(aggrSetToAuxVal.count(aggrSet.second.first)!=0){
            auxValPredicate=aggrSetToAuxVal[aggrSet.second.first];
            auxValTerm.push_back(r.getArithmeticRelationsWithAggregate()[0].getGuard().getTerm1());
        }else{
            auxValPredicate="aux_val"+std::to_string(auxPossibleSumToAggrSet.size());
            auxPossibleSumToAggrSet[auxValPredicate]=aggrSet.second.first;
            aggrSetToAuxVal[aggrSet.second.first]=auxValPredicate;
            auxValTerm.push_back(r.getArithmeticRelationsWithAggregate()[0].getGuard().getTerm1());
        }
    }

    auto body = buildBody(aggregateBodyVariables,r,auxValPredicate,auxValTerm);
    if(domPred!="")
        domToBody.insert({domPred,aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms()))});
    std::vector<std::string> aggrIds = writeAggrIdRule(body,aggrSet,r);
    clearData();
    if(aggrIds.size() == 1){
        if(body.second.first != "")
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        buildingBody.push_back(aspc::Literal(r.getArithmeticRelationsWithAggregate()[0].isNegated(),aspc::Atom(aggrIds[0],body.second.second.getTerms())));
        if(r.isConstraint())
            onConstraint();
        else{
            buildingHead.push_back(r.getHead()[0]);
            rewriteRule();
        }
    }else{
        if(r.getArithmeticRelationsWithAggregate()[0].isNegated()){
            if(body.second.first != "")
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIds[0],body.second.second.getTerms())));
            if(r.isConstraint())
                onConstraint();
            else{
                buildingHead.push_back(r.getHead()[0]);
                rewriteRule();
            }
            if(body.second.first != "")
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIds[1],body.second.second.getTerms())));
            if(r.isConstraint())
                onConstraint();
            else{
                buildingHead.push_back(r.getHead()[0]);
                rewriteRule();
            }
        }else{
            if(body.second.first != "")
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIds[0],body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIds[1],body.second.second.getTerms())));
            if(r.isConstraint())
                onConstraint();
            else{
                buildingHead.push_back(r.getHead()[0]);
                rewriteRule();
            }
        }
    }
}
void AspCore2ProgramBuilder::addManualDependecy(){
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
    for(const auto& pair : domToBody){
        #ifndef TRACE_PROPAGATOR
            std::cout<<"Adding dependency from "<<pair.second.getPredicateName()<<" to "<<pair.first<<std::endl;
        #endif
        int currentHeadId = predicateIDs.size();
        unordered_map<string, int>::iterator itAuxVal = originalPredicateIDs.find(pair.first);
        if (itAuxVal != originalPredicateIDs.end())
            currentHeadId = itAuxVal->second;
        else {
            originalPredicateIDs[pair.first] = currentHeadId;
            originalVertexByID[currentHeadId] = Vertex(currentHeadId, pair.first);
        }
        int currentBodyId = originalPredicateIDs.size();
        unordered_map<string, int>::iterator itAggrSet = originalPredicateIDs.find(pair.second.getPredicateName());
        if (itAggrSet != originalPredicateIDs.end())
            currentBodyId = itAggrSet->second;
        else {
            originalPredicateIDs[pair.second.getPredicateName()] = currentBodyId;
            originalVertexByID[currentBodyId] = Vertex(currentBodyId, pair.second.getPredicateName());
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
            #ifdef TRACE_PROPAGATOR
                std::cout<<"Adding manual dependecy "<<auxToBody.first<<" "<<l.getPredicateName()<<std::endl;
            #endif
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
}
aspc::Program & AspCore2ProgramBuilder::getProgram() {
    if(analyzeDependencyGraph){
        analyzeInputProgram();
        buildGraphNoCompletion();
        addManualDependecy();
        #ifdef TRACE_PROPAGATOR
        for(const aspc::Rule& r: original_program.getRules()){
            r.print();
        }
        // exit(180);
        #endif
        
    }
    return original_program;
}
bool AspCore2ProgramBuilder::isPredicateBodyNoCompletion(int predId)const{
    return predicateBodyNoCompletion.count(predId)!=0;
           
}
void AspCore2ProgramBuilder::buildGraphNoCompletion(){
    // std::cout<<"buildGraphNoCompletion"<<std::endl;
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



