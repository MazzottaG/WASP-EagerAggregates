/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ArithmeticRelation.h
 * Author: bernardo
 *
 * Created on March 16, 2018, 5:07 PM
 */

#ifndef ARITHMETICRELATION_H
#define ARITHMETICRELATION_H
#include "Formula.h"
#include "ArithmeticExpression.h"
#include <string>
#include <map>

namespace aspc {
    

    enum ComparisonType {
        GTE = 0, LTE, GT, LT, NE, EQ, UNASSIGNED
    };

    class ArithmeticRelation : public Formula {
    public:
        static std::map<aspc::ComparisonType, std::string> comparisonType2String;



    public:
        ArithmeticRelation(const aspc::ArithmeticExpression & left, const aspc::ArithmeticExpression & right, aspc::ComparisonType comparisonType);

        virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const override;
        virtual void addVariablesToSet(std::unordered_set<std::string> &) const override;
        virtual bool isPositiveLiteral() const override;
        virtual void print() const override;
        virtual bool isLiteral() const override;
        virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string &) const override;

        virtual ~ArithmeticRelation() {

        }
        
        aspc::ComparisonType getComparisonType() const {
            return comparisonType;
        }

        aspc::ArithmeticExpression getLeft() const {
            return left;
        }
        void setTermAtExpression(int expression, int term_index, std::string new_term){
            if(expression == 0){
                if(term_index == 0){
                    left.setTerm1(new_term);
                }else{
                    left.setTerm2(new_term);
                }
            }else{
                if(term_index == 0){
                    right.setTerm1(new_term);
                }else{
                    right.setTerm2(new_term);
                }
            }
        }
        aspc::ArithmeticExpression getRight() const {
            return right;
        }

        std::string getStringRep() const;
        
        std::string getAssignmentStringRep(const std::unordered_set<std::string>& boundVariables) const;
        
        std::string getAssignedVariable(const std::unordered_set<std::string>& boundVariables) const;



    private:
        aspc::ArithmeticExpression left;
        aspc::ArithmeticExpression right;
        aspc::ComparisonType comparisonType;


    };
}

#endif /* ARITHMETICRELATION_H */

