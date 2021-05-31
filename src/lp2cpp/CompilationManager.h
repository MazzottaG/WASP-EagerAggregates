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

#ifndef COMPILATIONMANAGER_H
#define	COMPILATIONMANAGER_H

#include "language/Program.h"
#include "parsing/AspCore2ProgramBuilder.h"
#include "utils/Indentation.h"
#include <string>
#include <set>
#include "datastructures/BoundAnnotatedLiteral.h"
#include "language/ArithmeticRelationWithAggregate.h"

const int LAZY_MODE = 0; 
const int EAGER_MODE = 1;

class CompilationManager {
public:
    CompilationManager(int mode);
    void lp2cpp();
    void generateStratifiedCompilableProgram(aspc::Program & program, AspCore2ProgramBuilder* builder);
    void setOutStream(std::ostream* outputTarget);
    const std::set<std::string> & getBodyPredicates();
    void insertModelGeneratorPredicate(const std::string & p) {
        modelGeneratorPredicates.insert(p);
    }
    void loadProgram(const std::string & filename);
    void setIdbs(std::unordered_set<std::string> && idbs) {
        this->idbs = std::move(idbs);
    }
    const std::unordered_set<std::string> & getIdbs() const {
        return idbs;
    }



    
private:
    unsigned exploreLiteral(const aspc::Literal*,std::unordered_set<std::string>&,unsigned);
    unsigned compileRuleBody(const std::vector<unsigned>,unsigned ,const aspc::Rule& ,std::unordered_set<std::string>,bool);
    void compileEagerRule(const aspc::Rule&,bool);
    void compileEagerRuleWithAggregate(const aspc::Rule&,bool);
    bool checkTupleFormat(const aspc::Literal& li,std::string buildIndex,bool tuplePointer);
    void declareAuxMap(std::string mapVariableName,std::vector<unsigned> keyIndexes,std::string predicateName,bool createFalseAuxMap,bool aggrStruct);
    void printVars(const aspc::Literal& li,std::string tupleName,std::unordered_set<std::string> & boundVars)const;
    void compileRule(const aspc::Rule& r,unsigned start, const aspc::Program& p) ;
    void declareDataStructures(const aspc::Rule& r, unsigned start,const std::set< std::pair<std::string, unsigned> >& aggregatePredicates);
    void declareRuleEagerStructures(const aspc::Rule& r);
    bool matchConstants(const aspc::Rule & rule, const aspc::Atom & atom, Indentation & ind);
    void generateHeadTupleAndMatchConstants(const aspc::Rule & rule, Indentation & ind, const std::set<std::string> & bodyPredicates);
    void setHeadVariables(Indentation & ind, const aspc::Rule & rule);
    bool checkInequalities(const aspc::Rule & rule, Indentation & ind);
    void declareArithmeticVariables(const aspc::Rule & rule, Indentation & ind);
    bool handleEqualCardsAndConstants(const aspc::Rule & r,unsigned i,const std::vector<unsigned>& joinOrder);
    bool handleExpression(const aspc::Rule& r, const aspc::ArithmeticRelation &, unsigned, const std::unordered_set<std::string> &);
    void writeNegativeTuple(const aspc::Rule & rule, std::vector<unsigned> & joinOrder, unsigned start, unsigned i);
    void declareDataStructuresForReasonsOfNegative(const aspc::Program & program);
    void declareDataStructuresForReasonsOfNegative(const aspc::Program & program, const aspc::Literal & lit, std::unordered_set<std::string> & litBoundVariables, std::unordered_set<std::string> & openSet);
    void writeNegativeReasonsFunctions(aspc::Program & program);
    void writeNegativeReasonsFunctionsPrototypes(aspc::Program & program);
    void writeNegativeReasonsFunctions(const aspc::Program & program, const BoundAnnotatedLiteral & lit,
        std::list<BoundAnnotatedLiteral> & toProcessLiterals, std::list<BoundAnnotatedLiteral> & processedLiterals, std::unordered_map <std::string, std::string> & functionsMap);
    void writeNegativeReasonsFunctionsPrototypes(const aspc::Program & program, const BoundAnnotatedLiteral & lit,
        std::list<BoundAnnotatedLiteral> & toProcessLiterals, std::list<BoundAnnotatedLiteral> & processedLiterals, std::unordered_map <std::string, std::string> & functionsMap);
    void initRuleBoundVariables(std::unordered_set<std::string> & ruleBoundVariables, const BoundAnnotatedLiteral & lit, const aspc::Atom & head, bool printVariablesDeclaration);
    void printLiteralTuple(const aspc::Literal* l, const std::vector<bool> & coveredMask) ;
    void printLiteralTuple(const aspc::Literal* l, const std::unordered_set<std::string> & boundVariables);
    void printLiteralTuple(const aspc::Literal* l);
    
    std::ostream* out;
    
    std::set<std::string> bodyPredicates;
    
    std::set<std::string> headPredicates;
    
    std::map<std::string,const aspc::Rule*> headPreds;
    Indentation ind;
    
    std::set<std::string> declaredMaps;
    
    AspCore2ProgramBuilder* builder;
    
    std::unordered_map<std::string, std::vector<std::string> > sharedVariablesMapForAggregateBody;
    std::unordered_map<std::string, std::vector< std::pair<int,int> > > aggrIdentifierForAggregateBody;
    
    std::unordered_map<std::string, std::vector<unsigned> > sharedVarAggrIDToBodyIndices;

    //contains aggr_set variable indices that appear in aggr_id
    std::unordered_map<std::string, std::vector<unsigned> > sharedVarAggrIDToAggrSetIndices;
    std::unordered_map<std::string, std::vector<unsigned> > aggrVarToAggrSetIndices;
    std::unordered_map<std::string, unsigned > aggrIdToRule;
    std::unordered_map<std::string, unsigned > aggrSetToSharedVar;

    //foreach aggrSet list of aggregateRules
    std::unordered_map<std::string, std::vector<unsigned>> aggrSetToRule;

    //contains aggr_set predicate inside sum aggregate
    std::unordered_set<std::string> sumAggrSetPredicate;
    std::unordered_map<std::string,std::set<std::pair<std::string,std::string>>> sumAggrSetPredicateToAggrId;
    
    std::unordered_map<std::string,std::vector<unsigned>> sharedVarAggrIdAggrSet;
    
    
    std::unordered_map<std::string, std::set<std::string> > predicateToAuxiliaryMaps;
    std::unordered_map<std::string, std::set<std::string> > predicateToNegativeAuxiliaryMaps;
    
    std::unordered_map<std::string, std::set<std::string> > predicateToUndefAuxiliaryMaps;
    std::unordered_map<std::string, std::set<std::string> > predicateToNegativeUndefAuxiliaryMaps;

    std::unordered_map<std::string, std::set<std::string> > predicateToFalseAuxiliaryMaps;
    
    std::unordered_set<std::string> modelGeneratorPredicates;
    
    std::unordered_set<std::string> modelGeneratorPredicatesInNegativeReasons;
    
    std::unordered_map<std::string, unsigned> predicateArieties;
    
    std::unordered_set<std::string> idbs;
    
    int mode;

    
};

#endif	/* COMPILATIONMANAGER_H */

