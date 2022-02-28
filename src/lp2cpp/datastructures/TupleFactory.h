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
#ifndef TUPLEFACTORY_H
#define TUPLEFACTORY_H
#include <unordered_map>
#include <list>
#include <cassert>
#include "TupleLight.h"
#include "IndexedSet.h"
#include <variant>

struct TuplePointerHash {

   inline std::size_t operator()(const TupleLight* v) const {
        std::size_t seed = 0;
        for (int i=0; i < v->size(); i++) {
            seed ^= v->at(i) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

struct TuplePointerEq {
   bool operator()(const TupleLight *val1, const TupleLight* val2) const{
      return *val1 == *val2;
   }
};
class TupleFactory{
    private:
        std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq> tupleToInternalVar;
        std::vector<TupleLight*> internalIDToTuple;
        std::unordered_map<int,TupleLight*> waspIDToTuple;
        std::list<TupleLight> storage;
        std::unordered_map<const std::string*,unsigned> aggregateSetToIndex;

    public:
        static TupleLight bufferTuple;
        void setBufferedTupleStorage(int* vectorData,int size,const std::string* predName){
            bufferTuple.setContent(vectorData,size,predName);
        }
        TupleFactory(/* args */){
            storage.push_back(TupleLight());
            internalIDToTuple.push_back(&storage.back());
            AggregateSetCmp::factory=this;
        }
        
        ~TupleFactory(){

        }
        void removeFromCollisionsList(int id){
            if(id < internalIDToTuple.size()){
                TupleLight* tupleToRemove = internalIDToTuple[id];
                std::vector<std::pair<std::variant< std::vector<int>, IndexedSet >*,unsigned>>* collisionsLists = &tupleToRemove->getCollisionsLists();
                for (unsigned i=0; i<collisionsLists->size(); i++) {
                    std::variant< std::vector<int>, IndexedSet >* collisionList = collisionsLists->at(i).first;
                    unsigned index = collisionsLists->at(i).second;

                    if(std::holds_alternative<std::vector<int>>(*collisionList)){
                        std::vector<int>& collisionVector = std::get<std::vector<int>>(*collisionList);
                        collisionVector[index] = collisionVector[collisionVector.size() - 1];
                        internalIDToTuple[collisionVector[index]]->setCollisionListIndex(collisionList, index,i);
                        collisionVector.pop_back();
                    }else{
                        IndexedSet& collisionSet = std::get<IndexedSet>(*collisionList);
                        collisionSet.erase(id); 
                    }
                }
                tupleToRemove->clearCollisionsList();
            }
        }
        void setId(TupleLight* t,unsigned id){
            if(t->getId()!=id){ 
                if(id < internalIDToTuple.size()){
                    t->setId(id);
                    internalIDToTuple[id]=t;
                }
            }
        }
        //store new wasp tuple and return a smart reference to it
        TupleLight* addNewTuple(std::vector<int> terms,const std::string* predName, unsigned id){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                storage.push_back(bufferTuple);
                TupleLight* reference = &storage.back();
                tupleToInternalVar.insert(reference);
                internalIDToTuple.push_back(reference);
                waspIDToTuple.insert({id,reference});
                reference->setWaspID(id);
                reference->setId(storage.size()-1);
                bufferTuple.clearContent();
                // std::cout<<reference->getWaspID()<<" "<<reference->getId()<<" ";reference->print();std::cout<<" "<<id<<std::endl;
                return &storage.back();
            }
            bufferTuple.clearContent();
            // std::cout<<"Already added"<<std::endl;
            // assert(it->getWaspID() == id);
            return *it;
        }
        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalTuple(std::vector<int> terms,const std::string* predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                
                storage.push_back(bufferTuple);
                TupleLight* trueReference = &storage.back();
                tupleToInternalVar.insert(trueReference);
                internalIDToTuple.push_back(trueReference);
                trueReference->setId(storage.size()-1);
                bufferTuple.clearContent();
                return trueReference;
            }
            bufferTuple.clearContent();

            // assert(it->second == -1);
            return *it;
        }
        TupleLight* find(std::vector<int> terms,const std::string* predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                bufferTuple.clearContent();
                return NULL;
            }
            bufferTuple.clearContent();
            // assert(it->second == -1);
            return *it;
        }
        TupleLight* find(const TupleLight& t){
            TupleLight* tuple = const_cast<TupleLight *>(&t);
            auto it = tupleToInternalVar.find(tuple);
            if(it==tupleToInternalVar.end()){
                // std::cout<<"Not found"<<std::endl;
                return NULL;
            }
            // assert(it->second == -1);
            return *it;
        }
        TupleLight* getTupleFromWASPID(int id){
            if(waspIDToTuple.count(id)!=0)
                return waspIDToTuple[id];
            return NULL;

        }

        TupleLight* getTupleFromInternalID(int id)const{
            if(id<internalIDToTuple.size())
                return internalIDToTuple[id];
            return NULL;
        }

        void printModelAsConstraint()const {
            std::cout<<"Tuple factory"<<std::endl;
            for(auto tuple : storage){
                if(tuple.getWaspID()!=0){
                    tuple.printAsConstraint();
                }
                
            }
        }
        void print()const {
            std::cout<<"Tuple factory"<<std::endl;
            bool first=true;
            for(auto tuple : storage){
                if(!first)
                    tuple.print();
                else
                    first=false;
            }
        }
        unsigned size(){
            return storage.size();
        }
        void printSize(){
            std::cout<<storage.size()<<std::endl;
        }
        unsigned getIndexForAggrSet(const std::string* pred)const{
            auto it = aggregateSetToIndex.find(pred);
            if(it != aggregateSetToIndex.end()){
                return it->second;
            }
            return 0;
        }
        void setIndexForAggregateSet(unsigned index,const std::string* pred){
            aggregateSetToIndex.emplace(pred,index);
        }
};


#endif