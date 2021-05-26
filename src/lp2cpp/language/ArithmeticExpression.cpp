/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ArithmeticExpression.cpp
 * Author: bernardo
 * 
 * Created on March 7, 2017, 2:22 PM
 */

#include "ArithmeticExpression.h"
#include "../utils/SharedFunctions.h"
#include <string>
#include<iostream>

aspc::ArithmeticExpression::ArithmeticExpression() {

}
aspc::ArithmeticExpression::ArithmeticExpression(const aspc::ArithmeticExpression& expr){
    term1=expr.getTerm1();
    if(!expr.isSingleTerm()){
        operation=expr.getOperation();
        term2=expr.getTerm2();
    }
    singleTerm = expr.isSingleTerm();
}
aspc::ArithmeticExpression::ArithmeticExpression(const std::string& term1, const std::string& term2, char operation) : term1(term1), term2(term2), operation(operation), singleTerm(false) {
}

aspc::ArithmeticExpression::ArithmeticExpression(const std::string& term1) : term1(term1), singleTerm(true) {
}
bool aspc::ArithmeticExpression::operator==(const aspc::ArithmeticExpression& expr){
    if(term1!=expr.term1 || singleTerm!=expr.singleTerm)
        return false;
    if(!singleTerm){
        if(term2 != expr.term2 || operation!=expr.operation)
            return false;
    }
    return true;
}

aspc::ArithmeticExpression& aspc::ArithmeticExpression::operator=(const aspc::ArithmeticExpression& o){
    
        this->term1=o.term1;
        this->term2=o.term2;
        this->operation=o.operation;
        this->singleTerm=o.singleTerm;
        return *this;
        
}
bool aspc::ArithmeticExpression::isSingleTerm() const {
    return singleTerm;
}

std::vector<std::string> aspc::ArithmeticExpression::getAllTerms() const {
    std::vector<std::string> res;
    res.push_back(term1);
    if (!isSingleTerm()) {
        res.push_back(term2);
    }
    return res;
}


std::string aspc::ArithmeticExpression::getStringRep() const {
    std::string res = "";
    if (isInteger(term1) || isVariable(term1)) {
        res += term1;
    } else {
        
        res += "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(term1) + "\")";
    }
    if (!singleTerm) {
        res += " ";
        res += operation;
        res += " ";
        if (isInteger(term2) || isVariable(term2)) {
            res += term2;
        } else {
            res += "ConstantsManager::getInstance().mapConstant(\"" + escapeDoubleQuotes(term2) + "\")";
        }
    }
    return res;
}
