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
#ifndef TUPLEFACTORYTRIE_H
#define TUPLEFACTORYTRIE_H
#include <unordered_map>
#include <list>
#include <cassert>
#include "TupleLight.h"
#include "IndexedSet.h"
#include "TupleTrieSet.h"
#include <variant>
#include <bitset>
#include <cmath>
class TupleFactoryTrie{
    private:
        std::vector<TupleTrieSet> tupleToInternalVarSets;
        std::vector<TupleLight*> internalIDToTuple;
        std::unordered_map<int,TupleLight*> waspIDToTuple;
        std::list<TupleLight> storage;
        std::unordered_map<int,unsigned> aggregateSetToIndex;
        bool generated;
        


    public:
        static TupleLight bufferTuple;
        void setBufferedTupleStorage(int* vectorData,int size,int predName){
            bufferTuple.setContent(vectorData,size,predName);
        }
        TupleFactoryTrie(/* args */){
            storage.push_back(TupleLight());
            internalIDToTuple.push_back(&storage.back());
            generated=false;
        }
        
        ~TupleFactoryTrie(){

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
        void addPredicate(){
            tupleToInternalVarSets.push_back(TupleTrieSet());
        }
        //store new wasp tuple and return a smart reference to it
        TupleLight* addNewTuple(std::vector<int> terms,int predName, unsigned id){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto node = tupleToInternalVar.addNodeForTuple(&bufferTuple);
            if(!node->existsTuple()){
                storage.push_back(bufferTuple);
                TupleLight* reference = &storage.back();
                node->setTuple(reference);
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
            return node->getTuple();
        }
        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalTuple(std::vector<int> terms,int predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto node = tupleToInternalVar.addNodeForTuple(&bufferTuple);
            if(!node->existsTuple()){
                storage.push_back(bufferTuple);
                TupleLight* trueReference = &storage.back();
                node->setTuple(trueReference);
                internalIDToTuple.push_back(trueReference);
                trueReference->setId(storage.size()-1);
                bufferTuple.clearContent();
                return trueReference;
            }
            bufferTuple.clearContent();

            // assert(it->second == -1);
            return node->getTuple();
        }
        TupleLight* find(std::vector<int> terms,int predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==NULL){
                bufferTuple.clearContent();
                return NULL;
            }
            bufferTuple.clearContent();
            // assert(it->second == -1);
            return it;
        }
        TupleLight* find(const TupleLight& t){
            TupleLight* tuple = const_cast<TupleLight *>(&t);
            auto& tupleToInternalVar=tupleToInternalVarSets[t.getPredicateName()];
            return tupleToInternalVar.find(tuple);
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
        unsigned getIndexForAggrSet(int pred)const{
            auto it = aggregateSetToIndex.find(pred);
            if(it != aggregateSetToIndex.end()){
                return it->second;
            }
            return 0;
        }
        void setIndexForAggregateSet(unsigned index,int pred){
            aggregateSetToIndex.emplace(pred,index);
        }
        bool isGenerated()const {return generated;}
        void setGenerated(bool gen){this->generated=gen;}
        void printStats()const{
            for(int i=0;i<tupleToInternalVarSets.size();i++)
                tupleToInternalVarSets[i].printStats();
        }
};


#endif