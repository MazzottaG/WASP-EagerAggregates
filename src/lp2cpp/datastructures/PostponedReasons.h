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
#ifndef POSTPONEDREASONS_H
#define POSTPONEDREASONS_H
#include <iostream>
#include <vector>
#include "PostponedReasonData.h"


class PostponedReasons{

    public:
        ~PostponedReasons(){
            for(auto & propLit:mapping){
                delete propLit.second;
            }
        }

        PostponedReasonData* operator[](int i){
            // std::cout << "getting "<<std::endl;
            return mapping[i];
        }
        PostponedReasonData* getAt(int i){
            return mapping[i];
        }
        void erase(int lit){
            if(mapping.find(lit) != mapping.end())
                delete mapping[lit];
            mapping.erase(lit);
        }
        bool addPropagation(int lit){
            if(mapping.find(lit)==mapping.end()){
                mapping[lit]=new PostponedReasonData();
                return true;
            }
            return false;
        }
        void addAggrToLit(int lit,int aggr_id,bool sign){
            if(mapping.find(lit)!=mapping.end()){
                mapping[lit]->addAggregate(aggr_id,sign);
            }
        }
        void setPropLevelToLit(int lit,int propLevel){
            if(mapping.find(lit)!=mapping.end()){
                mapping[lit]->setPropagationLevel(propLevel);
            }
        }
        void addBodyLitToLit(int lit,int bodyLit){
            if(mapping.find(lit)!=mapping.end()){
                mapping[lit]->addBodyLiteral(bodyLit);
            }
        }
        void addSharedVarToLit(int lit,int v){
            if(mapping.find(lit)!=mapping.end()){
                mapping[lit]->addSharedVariable(v);
            }
        }

        void addPropagation(int lit,const std::vector<int>& aggr_id, const std::vector<bool>& aggr_sign,int propLevel,std::vector<int>body,std::vector<int>sharedVars){
            // std::cout <<"Adding prop lit "<<lit <<std::endl;
            // if(mapping.find(lit)==mapping.end()){
            //     // std::cout<<"New"<<std::endl;
            //     mapping.insert({lit,PostponedReasonData(aggr_id,aggr_sign,propLevel,body,sharedVars)});
            //     return;
            // }

            //     PostponedReasonData* data = &mapping[lit];
            // // if(data->getPropagationLevel() == -1){
            //     // std::cout<<"Existing"<<std::endl;
            //     data->setAggregates(aggr_id,aggr_sign);
            //     data->setPropagationLevel(propLevel);
            //     data->setBodyReason(body);
            //     data->setSharedVariables(sharedVars);
            // // }else{

            // // }
            // // std::cout << "Added" <<std::endl;
            // // reas.print();
        }
        int size()const {return mapping.size();}
        void clear(){mapping.clear();}
        void print()const{
            for(const auto & lit : mapping){
                std::cout<< lit.first << " " ;
            }
            std::cout<<std::endl;
        }
    private:
        std::unordered_map<int,PostponedReasonData*> mapping;

        // int checkSize(int i){
        //     int pos = i>0 ? i : -1*i;
        //     if(pos>=mapping.size()){
        //         mapping.resize(pos+1);
        //     }

        //     return pos;
        // }
};

#endif
