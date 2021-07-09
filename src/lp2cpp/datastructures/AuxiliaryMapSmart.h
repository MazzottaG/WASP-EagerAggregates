/*
 *
 *  Copyright 2016 Bernardo Cuteri, Francesco Ricca.
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
 * File:   AuxiliaryMap.h
 * Author: bernardo
 *
 * Created on March 7, 2016, 2:17 PM
 */

#ifndef AUXILIARY_MAP_SMART_H
#define AUXILIARY_MAP_SMART_H
#include <list>
#include <vector>
#include <unordered_map>
#include <cmath>
#include "TupleWithoutReasons.h"
#include <bitset>

template<class T, size_t S>
class AuxiliaryMapSmart {
public:

    AuxiliaryMapSmart(const std::vector<unsigned> & keyIndices) :
        keySize(keyIndices.size()), keyIndices(keyIndices){
    }

    virtual ~AuxiliaryMapSmart() {
    }
    
    // inline int keySetSize(){
    //     int size = lookupReferences.size();
    //     for(auto it = lookupReferences.begin(); it!=lookupReferences.end();it++){
    //         if(it->empty())
    //             size--;
    //     }
    //     return size;
    // }
    inline const std::vector< const T* >& getValues(const std::vector<int>& key) const {
        std::bitset<S> keyCode;
        valueToPos(key,keyCode);
        const auto it = tuples.find(keyCode);
        if (it == tuples.end()) {
            return EMPTY_RESULT;
        }
        return it->second;
    }

    inline void insert2(const T & value) {
        
        std::bitset<S> keyCode;
        std::vector<int> key = getKey(value);
        valueToPos(key,keyCode);
        auto & collisionList = tuples[keyCode];
        value.setCollisionListIndex(&collisionList, collisionList.size());
        collisionList.push_back(&value);
    }
   
    void clear() {
        tuples.clear();
    }
    inline unsigned size()const{
        
        unsigned size = tuples.size();
        for (const auto element : tuples){
            if(element.second.empty())
                size--;
        }
        return size;
    }
protected:

    inline void valueToPos(const std::vector<int> & key, std::bitset<S>& keyCode) const {
        for (unsigned i = 0; i < keySize; i++) {
            keyCode = keyCode << 32;
            keyCode |= std::bitset<S>(key[i]);
        }
    }
    
    std::vector<int> getKey(const T& value){
        std::vector<int> key(keySize);
        for (unsigned i = 0; i < keySize; i++) {
            key[i] = value[keyIndices[i]];
        }
        return key;
    }
    
    std::unordered_map<std::bitset<S>, std::vector< const T* > > tuples;
    unsigned keySize;
    std::vector<unsigned> keyIndices;
    static const std::vector< const T* > EMPTY_RESULT;


};

template<class T,size_t S>
const std::vector< const T* > AuxiliaryMapSmart<T,S>::EMPTY_RESULT;


#endif /* AUXILIARYMAPSMART_H */

