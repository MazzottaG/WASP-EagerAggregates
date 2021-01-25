/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Aggregate.cpp
 * Author: giuseppe
 * 
 * Created on 17 marzo 2020, 17.20
 */

#include "Aggregate.h"
#include <iostream>
#include "../utils/SharedFunctions.h"


std::map<std::string,aspc::AggregateFunction> string2AggregateFunction = {
    {"#count", aspc::COUNT},
    {"#sum", aspc::SUM},
    {"#max", aspc::MAX},
    {"#min", aspc::MIN}

};

std::map<aspc::AggregateFunction,std::string> aggregateFunction2String = {
    {aspc::COUNT,"#count"},
    {aspc::SUM,"#sum"},
    {aspc::MAX,"#max"},
    {aspc::MIN,"#min"}

};
aspc::Aggregate::Aggregate(){
    
}


aspc::Aggregate::Aggregate(const std::vector<aspc::Literal> & literals, const std::vector<aspc::ArithmeticRelation>& inequalities_, const std::vector<std::string> & variables, std::string function): inequalities(inequalities_), aggregateFunction(string2AggregateFunction[function]){ 
    std::string tupleName= "";
    int totalArity = 0;
    int literalIndex=0;
    for(const aspc::Literal& l : literals){
        if(!l.isNegated()){
            aggregateLiteralsProjection.push_back("");
            for(int i=0;i<l.getAriety();i++)
                aggregateLiteralsProjection[literalIndex]+=std::to_string(i+totalArity)+"_";
            aggregateLiterals.push_back(aspc::Literal(l));
            literalIndex++;
            totalArity+=l.getAriety();
        }
    }
    // std::cout<<"Aggregate"<<std::endl;

    for(const aspc::Literal& l : literals){
        if(l.isNegated()){
            aggregateLiteralsProjection.push_back("");
            for(int i=0;i<l.getAriety();i++)
                aggregateLiteralsProjection[literalIndex]+=std::to_string(i+totalArity)+"_";
            
            aggregateLiterals.push_back(aspc::Literal(l));
            
            literalIndex++;
            totalArity+=l.getAriety();
        }
    }
    for(const std::string& v : variables){
        if(containsVar(v)<0){
            aggregateVariables.push_back(v);
        }
    }
    computeJoinTupleName();
}

std::string aspc::Aggregate::aggrVarsToString()const{
    std::string aggrVars;
    for(std::string v : aggregateVariables){
        aggrVars+=v+"_";
    }
    return aggrVars;
}   
std::unordered_map<aspc::ComparisonType,std::string> convertToWord={
    {aspc::GT,"GT"},
    {aspc::GTE,"GTE"},
    {aspc::LTE,"LTE"},
    {aspc::LT,"LT"},
    {aspc::EQ,"EQ"},
    {aspc::NE,"NE"}
};
std::unordered_map<char,std::string> convertToWordArithmeticOp={
    {'+',"PLUS"},
    {'-',"MINUS"},
    {'*',"TIMES"},
    {'/',"DIV"}
};
void aspc::Aggregate::computeJoinTupleName(){
    tupleName="";
    // for(std::string v : aggregateVariables){
    //     tupleName+=v+"_";
    // }
    for(const aspc::Literal& l : aggregateLiterals){
        if(l.isNegated())
            tupleName+="not_";
        tupleName+=l.getPredicateName()+"_";
        for(int i=0;i<l.getAriety();i++){
            if(!l.isVariableTermAt(i) && l.getTermAt(i)[0]=='-')
                tupleName+="n"+l.getTermAt(i).substr(1);
            else
                tupleName+=l.getTermAt(i)+"_";
        }
    }
    for(const aspc::ArithmeticRelation& inequality: inequalities){
        tupleName+=inequality.getLeft().getTerm1();
        if(!inequality.getLeft().isSingleTerm()){
            tupleName+=convertToWordArithmeticOp[inequality.getLeft().getOperation()]+inequality.getLeft().getTerm2();
        }

        tupleName+=convertToWord[inequality.getComparisonType()];
        tupleName+=inequality.getRight().getTerm1();
        if(!inequality.getRight().isSingleTerm()){
            tupleName+=convertToWordArithmeticOp[inequality.getRight().getOperation()]+inequality.getRight().getTerm2();
        }
        tupleName+="_";
    }
}
std::string aspc::Aggregate::getJoinTupleName()const{ 
    return tupleName;
}
void aspc::Aggregate::normalizeArithmeticRelation(const std::unordered_set<std::string> sharedVariables){
    int inequality_index=0;
    std::set<unsigned int> normalized_relation_indices;
    // std::cout<<sharedVariables.size()<<std::endl;
    for(aspc::ArithmeticRelation& r : inequalities){
        if(r.getComparisonType() == aspc::EQ){
            if(r.getLeft().isSingleTerm() && r.getRight().isSingleTerm()){
                if(sharedVariables.count(r.getLeft().getTerm1())>0 && sharedVariables.count(r.getRight().getTerm1())>0)
                    break;
                // Z = Y
                for(aspc::Literal& l : aggregateLiterals){
                    for(int i=0;i<l.getAriety();i++){
                        // l.print();
                        
                        if(l.isVariableTermAt(i) && l.getTermAt(i) == r.getLeft().getTerm1() && sharedVariables.count(r.getLeft().getTerm1())<=0){
                            // std::cout<<"Mapping "<<l.getTermAt(i) << " to "<<r.getRight()<<std::endl;
                            l.setTermAt(i,r.getRight().getTerm1());
                        }else if(!isVariable(r.getLeft().getTerm1()) || sharedVariables.count(r.getLeft().getTerm1())>0){
                            
                            if(l.isVariableTermAt(i) && l.getTermAt(i) == r.getRight().getTerm1()){
                                // std::cout<<"Maps "<<l.getTermAt(i) << " to "<<r.getLeft()<<std::endl;
                                l.setTermAt(i,r.getLeft().getTerm1());
                            }
                        }
                        
                    }
                }
                for(int i=0;i<aggregateVariables.size();i++){
                    if(aggregateVariables[i] == r.getLeft().getTerm1() && isVariable(r.getRight().getTerm1())){
                        if(sharedVariables.count(aggregateVariables[i])<=0)
                            aggregateVariables[i]=r.getRight().getTerm1();
                    }else if(aggregateVariables[i] == r.getRight().getTerm1() && isVariable(r.getLeft().getTerm1()) && sharedVariables.count(r.getLeft().getTerm1())>0){
                        aggregateVariables[i]=r.getLeft().getTerm1();
                    }
                }
                // X = Y,X in body, Z > X
                for(int i=0;i<inequalities.size();i++){
                    if(i!=inequality_index){
                        int term=0;
                        for(std::string& t : inequalities[i].getLeft().getAllTerms()){
                            if(t == r.getLeft().getTerm1()){

                                if(sharedVariables.count(t)<=0)
                                    inequalities[i].setTermAtExpression(0,term,r.getRight().getTerm1());
                                
                            }else if(t == r.getRight().getTerm1()){ 

                                if(!isVariable(r.getLeft().getTerm1()) || sharedVariables.count(r.getLeft().getTerm1())>0)
                                    inequalities[i].setTermAtExpression(0,term,r.getLeft().getTerm1());

                            }
                            term++;
                        }
        
                        term=0;
                        for(std::string& t : inequalities[i].getRight().getAllTerms()){
                            if(t == r.getLeft().getTerm1()){
                                if(sharedVariables.count(t)<=0)
                                    inequalities[i].setTermAtExpression(1,term,r.getRight().getTerm1());
                            }else if(t == r.getRight().getTerm1()){ 
                                if(!isVariable(r.getLeft().getTerm1()) || sharedVariables.count(r.getLeft().getTerm1())>0)
                                    inequalities[i].setTermAtExpression(1,term,r.getLeft().getTerm1());
                            }
                            term++;
                        }
                    }
                }
                normalized_inequalities.push_back(aspc::ArithmeticRelation(r));
                normalized_relation_indices.insert(inequality_index);
            }
        }

        inequality_index++;
    }
    unsigned int removed_inequalities=0;
    for(unsigned int index : normalized_relation_indices){
        inequalities.erase(inequalities.begin()+(index-removed_inequalities));
        removed_inequalities++;
    }
    computeJoinTupleName();
}

bool aspc::Aggregate::isBoundedRelation(const std::unordered_set<std::string>& set) const {
    
    return true;
}

bool aspc::Aggregate::isBoundedLiteral(const std::unordered_set<std::string>&) const {
    return false;
}

bool aspc::Aggregate::isBoundedValueAssignment(const std::unordered_set<std::string>& boundVariables) const {

    return false;
}

void aspc::Aggregate::addVariablesToSet(std::unordered_set<std::string>& set) const {

}

bool aspc::Aggregate::isPositiveLiteral() const {
    return false;
}
std::string aspc::Aggregate::getTermAt(unsigned int termIndex)const{
    std::unordered_set<std::string> boundVars;
    int term=0;
    for(const aspc::Literal& l : aggregateLiterals){
        for(int i=0;i<l.getAriety();i++){
            if(l.isVariableTermAt(i))
                boundVars.insert(l.getTermAt(i));
            if(term == termIndex)
                return l.getTermAt(i);
            term++;
        }
    }
    for(const aspc::ArithmeticRelation& inequality : inequalities){
        if(inequality.isBoundedValueAssignment(boundVars)){
            if(term == termIndex)
                return inequality.getAssignedVariable(boundVars);
            boundVars.insert(inequality.getAssignedVariable(boundVars));
            term++;
        }
    }
    return "";
}
std::string aspc::Aggregate::getStringRep()const{
    std::string result;
    for(const std::string& v: aggregateVariables){
        result+=v+",";
    }
    for(const aspc::Literal& l : aggregateLiterals){
        result+=l.getPredicateName()+",";
        for(int i=0;i<l.getAriety();i++){
            result+=l.getTermAt(i)+",";
        }
    }
    for(const aspc::ArithmeticRelation& r : inequalities){
        result+=r.getLeft().getStringRep()+",";
        result+=r.getRight().getStringRep()+",";
    }
    
    return result.substr(0,result.length()-1);
}
std::string aspc::Aggregate::getAggregateFunction()const{
    return aggregateFunction2String[aggregateFunction];
}


bool aspc::Aggregate::isSum()const{
    return aggregateFunction==aspc::SUM;
}



void aspc::Aggregate::print() const {
    
    
    std::cout<<aggregateFunction2String[this->aggregateFunction]<<"{";
    
    unsigned size=this->aggregateVariables.size();
    int j=0;
    for(std::string s:aggregateVariables){
        std::cout<<s;
        if(j<size-1)
            std::cout<<", ";
    }
    std::cout<<" : ";
    size=this->aggregateLiterals.size();

    for(unsigned i=0;i<size;++i){
        
        if(aggregateLiterals[i].isNegated())
        std::cout << "not ";
        std::cout<<aggregateLiterals[i].getPredicateName()<<"(";
        
        std::vector<std::string> terms = aggregateLiterals[i].getAtom().getTerms();
        unsigned num_terms = terms.size();
        
        for(unsigned j=0;j<num_terms;++j){
            std::cout<<terms[j];
            if(j<num_terms-1)
                std::cout<<", ";
        }
        std::cout<<")";
        if(i<size-1)
            std::cout<<", ";
    }

    for(const aspc::ArithmeticRelation& r : inequalities){
        std::cout<<", " << r.getStringRep();
    }
    std::cout<<"}";
    
}

bool aspc::Aggregate::isLiteral() const {
    return false;
}

unsigned aspc::Aggregate::firstOccurrenceOfVariableInLiteral(const std::string &) const {
    return 1;
}

aspc::Aggregate::~Aggregate(){
    
}


