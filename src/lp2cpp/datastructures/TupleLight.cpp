/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Tuple.cpp
 * Author: bernardo
 * 
 * Created on April 9, 2018, 1:19 PM
 */

#include "TupleLight.h"
// #include "TupleFactory.h"

// void TupleLight::removeFromCollisionsLists(const TupleFactory& factory) const {
//     for (auto & collisionListAndIndex : collisionsLists) {
//         std::vector<unsigned> & collisionList = *(collisionListAndIndex.first);
//         unsigned index = collisionListAndIndex.second;
//         collisionList[index] = collisionList[collisionList.size() - 1];
//         factory.getTupleFromInternalID(collisionList[index])->setCollisionListIndex(&collisionList, index);
//         collisionList.pop_back();
//     }
//     collisionsLists.clear();
// }