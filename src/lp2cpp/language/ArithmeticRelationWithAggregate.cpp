/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ArithmeticRelationWithAggregate.cpp
 * Author: giuseppe
 * 
 * Created on 20 marzo 2020, 9.57
 */

#include "ArithmeticRelationWithAggregate.h"
#include "../utils/SharedFunctions.h"

aspc::ArithmeticRelationWithAggregate::ArithmeticRelationWithAggregate(bool isLower, const aspc::ArithmeticExpression & expression, const aspc::Aggregate & aggregate_, aspc::ComparisonType compare,bool isNegated):aggregate(aggregate_),guard(expression),negated(isNegated){
    //guard = aspc::ArithmeticExpression(expression);

    plusOne=false;
    if(isLower){
        if(compare == aspc::GT)
            comparisonType = aspc::LT;
        else if(compare == aspc::GTE)
            comparisonType = aspc::LTE;
        else if(compare == aspc::LT)
            comparisonType = aspc::GT;
        else if(compare == aspc::LTE)
            comparisonType = aspc::GTE;
        else comparisonType = compare;
    }else{
        comparisonType = compare;
    }
    if(comparisonType == aspc::GT){
        comparisonType = aspc::GTE;
        plusOne=true;
    }else if(comparisonType == aspc::LT){
        negated=!negated;
        comparisonType = aspc::GTE;
    }else if(comparisonType==aspc::LTE){
        negated=!negated;
        comparisonType = aspc::GTE;
        plusOne=true;
    }

    /*for(const aspc::ArithmeticRelation& r : aggregate_.getAggregateNormalizedInequalities()){
        if(guard.getTerm1() == r.getLeft().getStringRep() && guard.getTerm1()[0]>='A'&& guard.getTerm1()[0]<='Z'){
           guard.setTerm1(r.getRight().getStringRep()); 
        }else if(!guard.isSingleTerm() && guard.getTerm2() == r.getLeft().getStringRep() && guard.getTerm2()[0]>='A'&& guard.getTerm2()[0]<='Z'){
            guard.setTerm2(r.getRight().getStringRep());
        }
    }*/

}           

bool aspc::ArithmeticRelationWithAggregate::isBoundedRelation(const std::unordered_set<std::string> & boundVariables) const {
    
    for (const std::string & v : guard.getAllTerms()) {
        if (isVariable(v) && !boundVariables.count(v)) {
            return false;
        }
    }
    
    return true;
}

bool aspc::ArithmeticRelationWithAggregate::isBoundedLiteral(const std::unordered_set<std::string> &) const {
    
    return false;
}
bool aspc::ArithmeticRelationWithAggregate::isBoundedValueAssignment(const std::unordered_set<std::string> & boundVariables) const {
    
    //#count{..}=X #count{..}=X+5 se X non è bound è un boundedValueAssignment 
    //#count{..}=X+Y se entrambe non sono bound allora non è un boundedValueAssignment
    
    if(this->comparisonType != aspc::EQ )
        return false;
    
    unsigned unassignedVariables=0;
    for (const std::string & v : guard.getAllTerms()) {
        if (!boundVariables.count(v) && isVariable(v)) {
            unassignedVariables++;
        }
    }
    return unassignedVariables == 1;
    
}
void aspc::ArithmeticRelationWithAggregate::addVariablesToSet(std::unordered_set<std::string> & set) const {
    for (const std::string & v : guard.getAllTerms()) {
        if (!set.count(v) && isVariable(v)) {
            //set.insert(v);
        }
    }
    
}
bool aspc::ArithmeticRelationWithAggregate::isPositiveLiteral() const {
    return false;
}
void aspc::ArithmeticRelationWithAggregate::print() const {
    std::string negation = negated ? "not":"";
    std::cout<<negation<<" ";
    aggregate.print();
    std::cout << " " << aspc::ArithmeticRelation::comparisonType2String[comparisonType] << " " << guard;
    std::string plus = plusOne ? "+1":"";
    std::cout<<plus;
    
}
bool aspc::ArithmeticRelationWithAggregate::isLiteral() const {
    return false;
}
bool aspc::ArithmeticRelationWithAggregate::containsAggregate() const{
    return true;
}
unsigned aspc::ArithmeticRelationWithAggregate::firstOccurrenceOfVariableInLiteral(const std::string &) const{
    return -1;
}
std::string aspc::ArithmeticRelationWithAggregate::getStringRep() const{
    std::string rep;
    for(std::string v: aggregate.getAggregateVariables()){
        rep+=v+"_";
    }
    rep+=getJoinTupleName();
    for(const aspc::ArithmeticRelation& ineq : aggregate.getAggregateInequalities()){
        rep+=ineq.getStringRep();
    }
    rep+=getCompareTypeAsString()+guard.getStringRep();
    return rep;
}

aspc::ArithmeticRelationWithAggregate::~ArithmeticRelationWithAggregate() {
}

