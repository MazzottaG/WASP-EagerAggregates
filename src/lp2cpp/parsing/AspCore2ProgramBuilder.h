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

class AspCore2ProgramBuilder : public DLV2::InputBuilder {
private:
    aspc::Program program;
    aspc::Program preProgram;
    
    aspc::Program original_program;
    bool analyzeDependencyGraph=true;
    std::vector<aspc::Rule> ruleWithoutCompletion;
    
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
    GraphWithTarjanAlgorithm graphWithTarjanAlgorithm;
    GraphWithTarjanAlgorithm original_graphWithTarjanAlgorithm;
    GraphWithTarjanAlgorithm graphWithTarjanAlgorithmNoCompletion;
    std::set<int> internalPredicatesId;

    std::unordered_map<std::string, int> predicateIDs;
    std::unordered_map<int, Vertex> vertexByID;
    
    std::unordered_map<std::string, int> originalPredicateIDs;
    std::unordered_map<int, Vertex> originalVertexByID;

    std::unordered_map<std::string, int> predicateIDsNoCompletion;
    std::unordered_set<int> predicateBodyNoCompletion;
    std::unordered_map<int, Vertex> vertexByIDNoCompletion;
    
    std::unordered_map<std::string,std::vector<std::string>> auxLiteralTerms;
    std::unordered_map<std::string,std::vector<aspc::Literal>> auxPredicateToBody;
    std::unordered_map<std::string,std::vector<aspc::ArithmeticRelation>> auxPredicateToInequality;

    std::unordered_set<std::string> bodyPredicates;
    std::unordered_map<std::string,AggrSetPredicate> aggrSetPredicates;
    // std::unordered_set<AggrSetPredicate> aggrSetPredicatesData;
    std::unordered_set<std::string> aggrIdPredicates;

    std::unordered_map<std::string, std::unordered_set<unsigned>> aggrSetToRule;
    std::unordered_set<std::string> printingPredicate;
    
    std::unordered_map<std::string, std::string> auxPossibleSumToAggrSet;
    std::unordered_map<std::string, int> auxValToRule;
    std::unordered_map<std::string, std::string> aggrSetToAuxVal;
    std::unordered_set<std::string> domPredicate;
    std::unordered_map<std::string,aspc::Literal> domToBody;
    std::unordered_map<std::string,std::vector<std::string>> domToTerms;

    std::unordered_map<std::string,std::vector<int>> predsToRules;
    std::unordered_map<std::string,std::vector<std::string>> supportPredicates;
    std::unordered_map<std::string,std::vector<aspc::Literal>> predsToHeads;
    std::vector<std::string> sups;

    std::unordered_set<std::string> recursivePredicates;
    std::unordered_map<int,std::vector<aspc::Rule>> ruleToSubProgram;
    std::unordered_map<int,std::vector<std::pair<int,std::string>>> aggregateToAggrId;
    void buildExpression();
    bool negatedTerm=false;
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
    aspc::Program & getSourceProgram();
    void analyzeInputProgram();
    void labelComponents(std::unordered_set<unsigned>& labeledComponent,const std::vector<std::vector<int>>& scc);
    void buildGraphNoCompletion();
    void buildConstraintDuplicateHeads();
    bool isPredicateBodyNoCompletion(int)const;
    const aspc::Literal* getSupportingHead(std::string pred);
    bool isSupPredicateForHead(std::string sup,std::string head);
    std::vector<std::string> getSupPredicatesForHead(std::string head);
    const  std::map<std::string, unsigned> & getArietyMap();
    bool isInternalPredicateName(std::string predName) {
        unsigned predId = predicateIDs[predName];
        return internalPredicatesId.find(predId)!=internalPredicatesId.end();
    }
    bool isInternalPredicate(int predId)const {
        return internalPredicatesId.find(predId)!=internalPredicatesId.end();
    }
    bool isDomPredicate(std::string predicate){
        return domPredicate.count(predicate)!=0;
    }
    const unordered_set<std::string> getPrintingPredicates(){return printingPredicate;}
    
    const std::unordered_map<std::string,std::vector<aspc::Literal>>& getAuxPredicateBody()const{
        return auxPredicateToBody;
    }
    const std::vector<aspc::ArithmeticRelation>& getInequalitiesForAuxPredicate(std::string pred){
        return auxPredicateToInequality[pred];
    }
    const std::unordered_map<std::string,std::vector<aspc::ArithmeticRelation>>& getAuxPredicateInequalities() const{
        return auxPredicateToInequality;
    }
    const std::unordered_map<std::string,std::string>& getAggrSetToAuxVal() const{
        return aggrSetToAuxVal;
    }
    const std::vector<aspc::Literal>& getBodyForAuxiliary(std::string aux){
        std::vector<aspc::Literal> ordered_body;
        if(auxPredicateToBody.find(aux)==auxPredicateToBody.end())
            return ordered_body;
        return auxPredicateToBody[aux];
    }
    const std::vector<string>& getAuxPredicateTerms(std::string auxPredicate){
        return auxLiteralTerms[auxPredicate];
    }
    bool isAuxPredicate(std::string predicate){
        return auxPredicateToBody.count(predicate)!=0;
    }
    std::string getAssignedAggrSet(std::string auxVal){
        return auxPossibleSumToAggrSet[auxVal];
    }
    bool isAuxValPred(std::string predicate){
        return auxPossibleSumToAggrSet.count(predicate)!=0;
    }
    int getRuleForAuxVal(std::string predicate){
        return auxValToRule[predicate];
    }
    bool isBodyPredicate(std::string predicate){
        return bodyPredicates.count(predicate)!=0;
    }
    const std::vector<aspc::Rule>& getRuleWithoutCompletion()const{return ruleWithoutCompletion;}
    // const std::unordered_map<std::string,AggrSetPredicate>& getAggrSetPredicate(){
    //     return aggrSetPredicates;
    // }
    bool isAggrSetPredicate(std::string predicate){
        return aggrSetPredicates.count(predicate)!=0;
    }
    bool isAggrIdPredicate(std::string predicate){
        return aggrIdPredicates.count(predicate)!=0;
    }
    void rewriteRule(int,bool=false);

    void rewriteConstraint(const aspc::Rule& r);
    void rewriteRuleWithAggregate(const aspc::Rule& r);
    void rewriteRuleWithCompletion(const aspc::Rule& r,int);
    std::pair<bool,std::pair<std::string,AggrSetPredicate>> buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation,std::string domPred,std::vector<std::string>domTerms,int ruleId);
    std::pair<bool,std::pair<std::string,AggrSetPredicate>> buildBody(std::unordered_set<std::string> aggregateBodyVariables,const aspc::Rule& r,std::string auxValPred,std::vector<std::string> auxValTerm,int ruleId);
    std::vector<std::string> writeAggrIdRule(std::pair<bool,std::pair<std::string,AggrSetPredicate>> body,std::pair<bool,std::pair<std::string,AggrSetPredicate>> aggrSet,const aspc::Rule& r);
    void clearData();
    std::vector<aspc::Literal> rewriteAggregate(std::vector<aspc::Literal>& ,const std::unordered_set<string>& ,const aspc::ArithmeticRelationWithAggregate&,bool=false);
    void addManualDependecy();
    aspc::Literal* getAssociatedBodyPred(const std::string& domPred){if(domToBody.count(domPred)==0) return NULL;return &domToBody[domPred];}
    std::vector<std::string> getDomTerms(const std::string& domPred){if(domToTerms.count(domPred)==0) return std::vector<std::string>();return domToTerms[domPred];}
    const std::unordered_map<int,std::vector<aspc::Rule>>&  getSubPrograms();
//    const void printSCC(){
//        std::vector<std::vector<int> > SCC = graphWithTarjanAlgorithm.SCC();
//        for(int i = 0;i< SCC.size();i++)
//        {
//            cout<< "componente "<< i <<endl;
//            for(int j = 0;j< SCC[i].size();j++)
//            {
//                std::unordered_map<int, Vertex>::iterator it = vertexByID.find(SCC[i][j]);
//                Vertex current = it->second;
//                cout<< current.id << "  " << current.name<<endl;
//                for(int c = 0; c< current.rules.size();c++)
//                    getProgram().getRule(current.rules[c]).print();
//            }
//        }
//    }
    void clearAggregateFields();
    bool isLazyPredicate(std::string pred){
        return predicateIDsNoCompletion.count(pred)!=0;
    }
    GraphWithTarjanAlgorithm& getSourceGraphWithTarjanAlgorithm();
    GraphWithTarjanAlgorithm& getGraphWithTarjanAlgorithm();
    GraphWithTarjanAlgorithm& getGraphWithTarjanAlgorithmNoCompletion(){return graphWithTarjanAlgorithmNoCompletion;}
    void normalizeArithmeticRelationsWithAggregate();
    const std::unordered_map<int, Vertex>& getSourceVertexByIDMap() const;
    const std::unordered_map<int, Vertex>& getVertexByIDMap() const;
    const std::unordered_map<int, Vertex>& getVertexByIDMapNoCompletion() {return vertexByIDNoCompletion;}
    const std::unordered_map<std::string, int>& getPredicateIDsMap() const;

    void rewritSourceProgram();
    aspc::ArithmeticRelationWithAggregate buildAggrSetRule(const aspc::Rule&,std::string&);
    aspc::Literal buildBodyRule(const aspc::Rule&,const aspc::ArithmeticRelationWithAggregate&,std::string&);
    
    void onRuleFirstRewriting();
    void onConstraintFirstRewriting();

    std::vector<std::pair<int,std::string>> getAggrIdForAggregate(int ruleId){return aggregateToAggrId[ruleId];}
    std::unordered_map<int,std::vector<std::pair<int,std::string>>> getAggregateToAggrID(){return aggregateToAggrId;}
};

#endif	/* ASPCORE2PROGRAMBUILDER_H */

