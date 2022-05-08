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
 * File:   AspCore2ProgramBuilder.h
 * Author: bernardo
 *
 * Created on June 16, 2016, 2:53 PM
 */

#ifndef ASPCORE2PROGRAMBUILDER_H
#define	ASPCORE2PROGRAMBUILDER_H

#include "../DLV2libs/input/InputBuilder.h"
#include "../language/Program.h"
#include "../language/ArithmeticExpression.h"
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../language/ArithmeticRelation.h"
#include "../language/ArithmeticRelationWithAggregate.h"
#include <vector>
#include <unordered_map>
#include "../language/Aggregate.h"
#include "../../stl/UnorderedSet.h"
#include "../utils/AggrSetPredicate.h"
#include "../language/EagerProgram.h"
#include "../utils/AssignedBody.h"

class AspCore2ProgramBuilder : public DLV2::InputBuilder {
private:
    
    //Input subprogram
    aspc::Program program;
    
    aspc::Program compilableProgram;
    GraphWithTarjanAlgorithm graphWithTarjanAlgorithm;
    std::unordered_map<std::string, int> predicateIDs;
    std::unordered_map<int, Vertex> vertexByID;
    
    bool rewritten=false;
    bool analyzeDependencyGraph=false;
    

    //Program after rewriting
    aspc::EagerProgram rewrittenProgram;

    //Predicate to domain predicate
    std::unordered_set<std::string> domainPredicates; 
    std::unordered_map<std::string,std::string> predicateToDomainPredicate;

    //Value predicate for bound value assignement with aggregate
    std::unordered_set<std::string> valuesPredicates; 
    std::unordered_map<std::string,int> valuesPredicateToRule;

    // Body predicate with assigned literals and ineqs
    std::unordered_set<std::string> bodyPredicates; 
    std::unordered_map<std::string,AssignedBody> bodyPredicateToAssignedBody;

    // AggreSet predicate with assigned literals and ineqs
    std::unordered_set<std::string> aggregateSetPredicates; 
    std::unordered_map<std::string,AssignedBody> aggregateSetPredicateToAssignedBody;

    //AggregateId to body predicate
    std::unordered_set<std::string> aggIdPredicates; 
    std::unordered_map<std::string,std::string> aggIdPredicateToBodyPredicate;

    //Rewritten program after completion
    aspc::EagerProgram programWithCompletion;
    
    //Rewritten rule to completion subprogram
    std::vector<std::vector<int>> rewrittenRuleToCompletionSubProgram;
    
    //support predicates
    std::unordered_set<std::string> supPredicates;
    std::unordered_map<std::string,std::vector <std::string>> predicateToSupportPredicates;

    //aux predicate
    std::unordered_set<std::string> auxPredicates;

    std::unordered_set<std::string> internalPredicates;

    //Fake lazy program
    aspc::EagerProgram endProgram;
    
    //Output literals
    std::unordered_set<std::string> printingPredicate;


    
    bool buildingAggregate = false;
    std::string aggregateFunction="None";
    std::vector<std::string> aggregateVariables;
    std::vector<aspc::Literal> aggreagateLiterals;
    std::vector<aspc::ArithmeticRelation> aggreagateInequalities;
    aspc::ArithmeticExpression guard;
    aspc::ComparisonType inequalitySignAggregate;
    bool isLower;
    bool isNegated;

    
    std::vector<aspc::Aggregate> aggregates;
    
    std::vector<std::string> buildingTerms;
    std::vector<aspc::Literal> buildingBody;
    std::vector<aspc::Atom> buildingHead;
    std::map<std::string, unsigned> arietyMap;
    bool naf;
    aspc::ComparisonType inequalitySign;
    char arithOp;
    aspc::ArithmeticExpression expression;
    std::vector<aspc::ArithmeticRelation> inequalities;
    std::vector<aspc::ArithmeticRelationWithAggregate> inequalitiesWithAggregate;
    std::string predicateName;

    void buildExpression();
    bool negatedTerm=false;
    void buildCompilablePrograms();
    void computeCompletion();
    bool splitProgram(std::unordered_set<int>&,const std::vector<std::vector<int>>&);
    void buildProgram();
public:
    AspCore2ProgramBuilder();

    virtual void onAggregate(bool naf);

    virtual void onAggregateElement();

    virtual void onAggregateFunction(char* functionSymbol);

    virtual void onAggregateGroundTerm(char* value, bool dash);

    virtual void onAggregateLowerGuard();

    virtual void onAggregateNafLiteral();

    virtual void onAggregateUnknownVariable();

    virtual void onAggregateUpperGuard();

    virtual void onAggregateVariableTerm(char* value);

    virtual void onArithmeticOperation(char arithOperator);

    virtual void onAtom(bool isStrongNeg);

    virtual void onBody();

    virtual void onBodyLiteral();

    virtual void onBuiltinAtom();

    virtual void onChoiceAtom();

    virtual void onChoiceElement();

    virtual void onChoiceElementAtom();

    virtual void onChoiceElementLiteral();

    virtual void onChoiceLowerGuard();

    virtual void onChoiceUpperGuard();

    virtual void onConstraint();

    virtual void onDirective(char* directiveName, char* directiveValue);

    virtual void onEqualOperator();

    virtual void onExistentialAtom();

    virtual void onExistentialVariable(char* var);

    virtual void onFunction(char* functionSymbol, int nTerms);

    virtual void onGreaterOperator();

    virtual void onGreaterOrEqualOperator();

    virtual void onHead();

    virtual void onHeadAtom();

    virtual void onLessOperator();

    virtual void onLessOrEqualOperator();

    virtual void onNafLiteral(bool naf);

    virtual void onPredicateName(char* name);

    virtual void onQuery();

    virtual void onRule();

    virtual void onTerm(int value);

    virtual void onTerm(char* value);

    virtual void onTermDash();

    virtual void onTermParams();

    virtual void onTermRange(char* lowerBound, char* upperBound);

    virtual void onUnequalOperator();

    virtual void onUnknownVariable();

    virtual void onWeakConstraint();

    virtual void onWeightAtLevels(int nWeight, int nLevel, int nTerm);
    
    aspc::Program & getProgram();
    aspc::EagerProgram & getRewrittenProgram();
    aspc::EagerProgram & getCompilingProgram();
    
    std::unordered_set<std::string> getInternalPredicates()const;
    std::unordered_set<std::string> getDomainPredicates(){return domainPredicates;}
    std::unordered_set<std::string> getValuesPredicates(){return valuesPredicates;}
    std::vector<aspc::Atom> getFacts()const{return program.getFacts();}
    const  std::map<std::string, unsigned> & getArietyMap();
    bool isDomainPredicate(std::string predicate){
        return domainPredicates.count(predicate)!=0;
    }
    bool isDomainPredicateForPredicate(std::string dom,std::string pred){
        return predicateToDomainPredicate[pred]==dom;
    }
    std::string getPredicateForDomainPredicate(std::string dom){
        for(auto pair: predicateToDomainPredicate)
            if(pair.second==dom)
                return pair.first;
        return "";
    }
    std::string getBodyPredicateForAggrId(std::string aggrId){
        return aggIdPredicateToBodyPredicate[aggrId];
    }
    bool isAggregateIdPredicate(std::string predName){
        return aggIdPredicates.count(predName)!=0;
    }
    const unordered_set<std::string> getPrintingPredicates(){return printingPredicate;}
    aspc::EagerProgram& getEndProgram(){return endProgram;}
    bool isAuxPredicate(std::string predicate){
        return auxPredicates.count(predicate)!=0;
    }
    bool isValuePredicate(std::string predicate){
        return valuesPredicates.count(predicate)!=0;
    }
    int getRuleForAuxVal(std::string predicate){
        return valuesPredicateToRule[predicate];
    }
    bool isBodyPredicate(std::string predicate){
        return bodyPredicates.count(predicate)!=0;
    }
    std::vector<aspc::Rule> getRuleWithoutCompletion()const{return endProgram.getRules();}
    bool isAggrSetPredicate(std::string predicate){
        return aggregateSetPredicates.count(predicate)!=0;
    }

    void clearData();
    const std::vector<std::vector<int>>&  getSubPrograms();
    std::vector<aspc::Rule>  getSubProgramsForRule(int id);
    void clearAggregateFields();
    GraphWithTarjanAlgorithm& getGraphWithTarjanAlgorithm();

    unordered_set<std::string> getSumPredicates(){
        std::unordered_set<std::string> preds;
        for(const aspc::Rule& r: rewrittenProgram.getRules()){
            if(!r.isConstraint() && r.containsAggregate()){
                preds.insert(r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0].getPredicateName());
            }
        }
        return preds;
    }

    std::vector<std::string> getSupportPredicateForHead(std::string pred){
        return predicateToSupportPredicates[pred];
    }
    std::set<std::string> getBodyPredicates()const {return program.getBodyPredicates();}
    std::set<std::string> getHeadPredicates()const {return program.getHeadPredicates();}

    bool isSupPredicate(const std::string& pred)const {return supPredicates.find(pred)!=supPredicates.end();}
};

#endif	/* ASPCORE2PROGRAMBUILDER_H */

