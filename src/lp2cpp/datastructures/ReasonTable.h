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
#ifndef REASONTABLE_H
#define REASONTABLE_H

#include <iostream>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "../../stl/UnorderedSet.h"
class ReasonTable{

    public:
        ReasonTable(){
            currentLevel=0;
            removingLevels=0;
            resizeFactor=1;
        }
        void insert(int v){
            int pos=v;
            if(pos < 0)
                pos=v*-1;
            // if(pos >= literalToLevel.size()){
            //     literalToLevel.resize(pos+1);
            // }
            if(literalToLevel.find(pos)== literalToLevel.end()){
                literalToLevel[pos]=currentLevel;
                reason.push_back(v);
            }

            // if(literalToLevel[pos] > 0 && literalToLevel[pos]<=currentLevel)
            //     return;
            // literalToLevel[pos]=currentLevel;
            // reason.push_back(v);
        }
        void eraseCurrentLevel(){
            if(currentLevel>0){
                currentLevel--;
                if(currentLevel==0)
                    deleteErasedLevel();
                else
                    removingLevels++;
            }
        }
        unsigned size()const{
            return reason.size();
        }
        void print(){
            for(int v : reason){
                int a=v;
                if(a<0)
                    a*=-1;
                std::cout<<v<<";"<<literalToLevel[a]<<" ";
            }
            std::cout<<std::endl;
        }
        int getCurrentLevel()const{
            return currentLevel;
        }
        void addLevel(){
            if(removingLevels>0){
                deleteErasedLevel();
            }
            currentLevel++;
        }
        int level(int v) {
            int a=v;
            if(a<0) 
                a*=-1;
            if(literalToLevel.size()>a) 
                return literalToLevel[a]; 
            return 0;
        }
        void getLiteralUntil(int level,UnorderedSet<int>& reas){
            if(level<=0)
                return;
            for(int i=0;i<reason.size();i++){
                int lit=reason[i];
                int pos= lit > 0 ? lit : -lit;
                if(literalToLevel[pos] > level){
                    return;
                }
                reas.insert(lit);
            }
        }
        std::vector<int>::iterator begin(){return reason.begin();}
        std::vector<int>::iterator end(){return reason.end();}
        
        private:
            std::vector<int> reason;
            std::unordered_map<int,int> literalToLevel;

            int currentLevel;
            int removingLevels;
            int resizeFactor;
            void deleteErasedLevel(){
                int j=0;
                for(int i=0;i<reason.size();i++){
                    reason[j]=reason[i];
                    int pos = reason[i]>0 ? reason[i]:-reason[i];
                    if(literalToLevel[pos]>currentLevel){
                        literalToLevel.erase(pos);
                    } else{
                        j++;
                    }

                }
                reason.resize(j);
                removingLevels=0;
            }

};
#endif