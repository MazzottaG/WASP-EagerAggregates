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
#include "TupleWithReasons.h"

const unsigned SMART_PREDICATE_SETS_TOTAL_MEMORY = (sizeof NULL) * 1 * 1024 * 1024; //8MB in size

class SmartPredicateSet : protected std::unordered_set<int> {
public:

    //Size of NULL is typically 8 byte, i.e. 32 bit

    SmartPredicateSet(unsigned ariety) : ariety(ariety), lookup_bases(ariety, 0) {
        unsigned total_size = SMART_PREDICATE_SETS_TOTAL_MEMORY / (sizeof NULL);
        if (ariety == 0) {
            lookup_size = total_size = 1;
        } else if (ariety == 1) {
            lookup_size = total_size = (unsigned) sqrt(total_size);
        } else {
            lookup_size = (unsigned) std::pow(total_size, 1.0 / ariety);
        }
        lookup = std::vector<TupleWithReasons*>(total_size, NULL);
    }

    virtual ~SmartPredicateSet() {
    }

    void clear() {

        std::fill(lookup.begin(), lookup.end(), (TupleWithReasons*) NULL);
        std::fill(lookup_bases.begin(), lookup_bases.end(), 0);
        std::unordered_set<int>::clear();
    }
    //WARNING: moving tuples between two predicate set implies first removing and then adding to new SmartPredicateSet
    std::pair<const TupleWithReasons *, bool> insert(TupleWithReasons* value) {

        if (canLookup(*value)) {
            unsigned pos = valueToPos(*value);

            if (lookup[pos] == NULL) {
                lookup[pos] = value;
                return std::make_pair(value, true);
            }
            return std::make_pair(lookup[pos], false);

        }

        const auto & insertResult = std::unordered_set<int>::insert(value->getId());
        return std::make_pair(value, insertResult.second);
    }

    const TupleWithReasons * find(const TupleWithReasons & value) {
        
         if (canLookup(value)) {
            return lookup[valueToPos(value)];
        }
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

    void erase(const TupleWithReasons & value) {

        const TupleWithReasons* realValue;
        if (canLookup(value)) {
            unsigned pos = valueToPos(value);
            realValue = lookup[pos];
            if (lookup[pos] == NULL) {
                return;
            }
            lookup[pos] = NULL;
            realValue->removeFromCollisionsLists();
        } else {
            const auto & findResult = std::unordered_set<int>::find(value.getId());
            if (findResult == std::unordered_set<int>::end()) {
                return;
            }
            realValue = &value;
            realValue->removeFromCollisionsLists();
            std::unordered_set<int>::erase(findResult);
        }

    }

    // const std::vector<const TupleWithReasons*> & getTupleWithReasonsuples() const {
    //     return tuples;
    // }
    
private:

    inline bool canLookup(const TupleWithReasons & value) {
        // for (unsigned i = 0; i < ariety; i++) {
        //     if ((value[i] - lookup_bases[i] >= lookup_size) || (value[i] - lookup_bases[i] < 0)) {
        //         if (unordered_set<int>::empty() && lookup_size > 0){
        //         // if (tuples.empty() && lookupReferences.empty() && lookup_size > 0) {
        //             lookup_bases[i] = value[i];
        //         } else {
        //             return false;
        //         }
        //     }
        // }
        // return true;
        return false;
    }

    inline unsigned valueToPos(const TupleWithReasons & value) const {
        //Assuming canLookup is checked before
        unsigned pos = 0;
        for (unsigned i = 0; i < ariety; i++) {
//            std::count <<" Value "<<value[i]<<" lookup_base "<<lookup_bases[i]<<std::endl;
            pos += (value[i] - lookup_bases[i]) * std::pow(lookup_size, i);
        }
        return pos;
    }

    std::vector<TupleWithReasons*> lookup;

    unsigned ariety;
    int lookup_size;
    std::vector<int> lookup_bases;
};

#endif 

