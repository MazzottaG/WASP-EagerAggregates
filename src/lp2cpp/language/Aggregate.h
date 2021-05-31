/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Aggregate.h
 * Author: giuseppe
 *
 * Created on 17 marzo 2020, 17.20
 */

#ifndef AGGREGATE_H
#define AGGREGATE_H
#include "Formula.h"
#include "Literal.h"
#include "ArithmeticRelation.h"
#include <map>
#include <vector>
#include <set>


namespace aspc {
    
    enum AggregateFunction {
        COUNT = 0, SUM, MAX, MIN, UNKNOWN
    };
    
    class Aggregate : public Formula{
    
    public:
        Aggregate();
        Aggregate(const std::vector<aspc::Literal> & literals,const std::vector<aspc::ArithmeticRelation>& inequalities, const std::vector<std::string> & variables, std::string function);
        aspc::Aggregate& operator=(const aspc::Aggregate&);
        virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const override;
        virtual void addVariablesToSet(std::unordered_set<std::string> &) const override;
        virtual bool isPositiveLiteral() const override;
        virtual void print() const override;
        virtual bool isLiteral() const override;
        virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string &) const override;
        const std::vector<aspc::Literal> & getAggregateLiterals()const{return aggregateLiterals;}
        const std::vector<std::string>& getAggregateVariables()const {return aggregateVariables;}
        int containsVar(std::string v)const{
            for(int i=0;i<aggregateVariables.size();i++)
                if(v == aggregateVariables[i])
                    return i;
            return -1;
        }
        const std::vector<aspc::ArithmeticRelation> & getAggregateInequalities()const{return inequalities;}
        const std::vector<aspc::ArithmeticRelation> & getAggregateNormalizedInequalities()const{return normalized_inequalities;}
        void normalizeArithmeticRelation(const std::unordered_set<std::string> sharedVariables);
        std::string getJoinTupleName()const;
        void computeJoinTupleName();
        std::string aggrVarsToString()const;
        void setJoinTupleName(std::string joinTupleName){
            tupleName=joinTupleName;
        }
        bool isSum()const;
        std::string getAggrLitProj(int litIndex)const {return aggregateLiteralsProjection[litIndex];}
        std::string getAggregateFunction()const;
        std::string getTermAt(unsigned int termIndex)const;
        std::string getStringRep()const;
        void clearAggregateLiterals(){aggregateLiterals.clear();}
        void addLiteral(aspc::Literal l){aggregateLiterals.push_back(l);}
        void getOrderedAggregateBody(std::vector<aspc::Formula*>& orderedBody,std::unordered_set<std::string>)const;
        virtual ~Aggregate();
        
    private:
        std::vector<aspc::Literal> aggregateLiterals;
        std::vector<aspc::ArithmeticRelation> inequalities;
        std::vector<aspc::ArithmeticRelation> normalized_inequalities;
        std::vector<std::string> aggregateVariables;
        aspc::AggregateFunction aggregateFunction;
        std::string tupleName;
        std::vector<std::string> aggregateLiteralsProjection;
        
    };
}
#endif /* AGGREGATE_H */

