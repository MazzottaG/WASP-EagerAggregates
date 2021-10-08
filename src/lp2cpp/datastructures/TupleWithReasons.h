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
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Tuple.h
 * Author: bernardo
 *
 * Created on April 9, 2018, 1:19 PM
 */

#ifndef TUPLE_WITH_REASONS_H
#define TUPLE_WITH_REASONS_H
#include <vector>
#include <string>
#include <unordered_set>
#include "TupleWithoutReasons.h"
#include <iostream>

class TupleWithReasons : public TupleWithoutReasons {
public:

    TupleWithReasons():TupleWithoutReasons(){

    }

    TupleWithReasons(const std::string* predicateName, bool negated = false, int waspID=0) : TupleWithoutReasons(predicateName, negated,waspID) {
    }
    TupleWithReasons(const std::string* predicateName,std::vector<int> v, bool negated = false, int waspID=0) : TupleWithoutReasons(predicateName,v, negated,waspID) {
        
    }
    TupleWithReasons(const TupleWithReasons& orig) : TupleWithoutReasons(orig), positiveReasons(orig.positiveReasons),
    negativeReasons(orig.negativeReasons) {
    }

    virtual ~TupleWithReasons() {

    }

    TupleWithReasons(const std::initializer_list<int> & l, bool negated = false, int waspID=0) : TupleWithoutReasons(l, negated,waspID) {
    }

    TupleWithReasons(const std::initializer_list<int> & l, const std::string * predicateName, bool negated = false, int waspID=0) :
    TupleWithoutReasons(l, predicateName, negated,waspID) {
    }

    TupleWithReasons(const std::vector<int> & l, const std::string * predicateName, bool negated = false, int waspID=0) :
    TupleWithoutReasons(l, predicateName, negated,waspID) {
    }
    TupleWithReasons(const std::vector<int> & l, bool negated = false, int waspID=0) :
    TupleWithoutReasons(l, negated,waspID) {
    }

    void addPositiveReason(const TupleWithReasons* r) const {
        positiveReasons.push_back(r);
    }

    void addNegativeReason(const TupleWithReasons & r) const {
        negativeReasons.push_back(r);
    }

    const vector<const TupleWithReasons*> & getPositiveReasons() const {
        return positiveReasons;
    }

    const vector<TupleWithReasons> & getNegativeReasons() const {
        return negativeReasons;
    }

    void setCollisionListIndex(std::vector<const TupleWithReasons *>* collisionList, unsigned index) const {
        // std::cout<<"Set Collision List Index";
        // print();
        // std::cout<<" "<<index<<" List size: "<<collisionList->size()<<std::endl;
        collisionsLists[collisionList] = index;
    }
    void removeFromCollisionsLists() const {
        // std::cout<<"Removing from collisions list";
        // print();   
        // std::cout<<std::endl;     
        
        for (auto & collisionListAndIndex : collisionsLists) {
            std::vector<const TupleWithReasons *> & collisionList = *(collisionListAndIndex.first);
            // if(!collisionList.empty()){
                unsigned index = collisionListAndIndex.second;
                // std::cout<<"Collisions List at index: "<<index<<std::endl;
                collisionList[index] = collisionList[collisionList.size() - 1];
                collisionList[index]->setCollisionListIndex(&collisionList, index);
                collisionList.pop_back();
                // std::cout<<"Updated Collisions List Size: "<<collisionList.size()<<std::endl;
                
            // }
        }
        collisionsLists.clear();
    }
    // ORIGINAL VERSIO removeFromCollisionsLists METHOD
    // void removeFromCollisionsLists() const {
    //     for (auto & collisionListAndIndex : collisionsLists) {
    //         std::vector<const TupleWithReasons *> & collisionList = *(collisionListAndIndex.first);
    //         unsigned index = collisionListAndIndex.second;
    //         collisionList[index] = collisionList[collisionList.size() - 1];
    //         collisionList[index]->setCollisionListIndex(&collisionList, index);
    //         collisionList.pop_back();
    //     }
    // }

    bool operator==(const TupleWithReasons& right) const {
        return TupleWithoutReasons::operator==(right);
    }
    
    TupleWithReasons& operator=(const TupleWithReasons& right) {
        if (this == &right) 
            return *this; 
        TupleWithoutReasons::operator =(right);
        positiveReasons = right.positiveReasons;
        negativeReasons = right.negativeReasons;
        collisionsLists = right.collisionsLists;
        
        return *this;
    }



private:
    mutable std::unordered_map<std::vector<const TupleWithReasons *>*, unsigned> collisionsLists;
    mutable vector<const TupleWithReasons*> positiveReasons;
    mutable vector<TupleWithReasons> negativeReasons;

};



#endif /* TUPLE_H */

