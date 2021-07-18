/*
 * TupleWithReasonso change this license header, choose License Headers in Project Properties.
 * TupleWithReasonso change this template file, choose TupleWithReasonsools | TupleWithReasonsemplates
 * and open the template in the editor.
 */

/* 
 * File:   PredicateSet.h
 * Author: bernardo
 *
 * Created on September 7, 2018, 11:20 AM
 */

#ifndef SMARTPREDICATESET_H
#define SMARTPREDICATESET_H
#include <unordered_set>
#include <iostream>
#include <vector>
#include <list>
#include <cmath>
#include <unordered_map>
#include "TupleLight.h"

class SmartPredicateSet : protected std::unordered_set<int> {
public:

    SmartPredicateSet(unsigned ariety) : ariety(ariety) {
    }

    virtual ~SmartPredicateSet() {
    }

    void clear() {

        std::unordered_set<int>::clear();
    }
    //WARNING: moving tuples between two predicate set implies first removing and then adding to new SmartPredicateSet
    std::pair<const TupleLight *, bool> insert(TupleLight* value) {
        const auto & insertResult = std::unordered_set<int>::insert(value->getId());
        return std::make_pair(value, insertResult.second);
    }

    const TupleLight * find(const TupleLight & value) {
        
        const auto & findResult = std::unordered_set<int>::find(value.getId());
        if (findResult == std::unordered_set<int>::end()) {
            return NULL;
        }
        return &value;
    }
    std::vector<int> getTuplesId(){
        std::vector<int> tuples;
        auto it = unordered_set<int>::begin();
        while (it!=unordered_set<int>::end()){
            tuples.push_back(*it);
            it++;
        }
        return tuples;
    }
    

    //assuming its a copy   
    // void erase(TupleWithReasonsuple*  value)
    // factory from int to tuple*

    void erase(const TupleLight & value) {

        const TupleLight* realValue;
        const auto & findResult = std::unordered_set<int>::find(value.getId());
        if (findResult == std::unordered_set<int>::end()) {
            return;
        }
        realValue = &value;
        // realValue->removeFromCollisionsLists();
        std::unordered_set<int>::erase(findResult);
    }

    
private:
    unsigned ariety;

};

#endif 

