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
#ifndef POSTPONEDREASONDATA_H
#define POSTPONEDREASONDATA_H
#include <vector>
#include <unordered_set>
#include "../../stl/UnorderedSet.h"

class PostponedReasonData{
    
    public:
        PostponedReasonData(const std::vector<int>& aggr,const std::vector<bool>& aggr_sign,int propLevel,const UnorderedSet<int>& bodyReason,const std::vector<int>& sharedVars){
            this->propagationLevel=propLevel;
            setBodyReason(bodyReason);
            setSharedVariables(sharedVars);
            setAggregates(aggr,aggr_sign);
        }
        PostponedReasonData(){
            propagationLevel=-1;
        }
        void clear(){
            propagationLevel=-1;
            bodyLit.clear();
            sharedVariables.clear();
            aggregates_id.clear();
            aggregates_sign.clear();
        }
        void addAggregate(int aggr_id, bool sign){
            aggregates_id.push_back(aggr_id);
            aggregates_sign.push_back(sign);
        }
        void addBodyLiteral(int lit){
            bodyLit.insert(lit);
        }
        void addSharedVariable(int v){
            sharedVariables.push_back(v);
        }
        void setAggregates(const std::vector<int>& aggr,const std::vector<bool>& aggr_sign){
            aggregates_id.clear();
            aggregates_sign.clear();
            for(int i=0;i<aggr.size();i++){
                aggregates_id.push_back(aggr[i]);
                aggregates_sign.push_back(aggr_sign[i]);
            }
        }
        const std::vector<int>& getAggregateId()const{return aggregates_id;}
        const std::vector<bool>& getAggregateSign()const{return aggregates_sign;}
        
        int getPropagationLevel()const{return propagationLevel;}
        void setPropagationLevel(int propLevel){this->propagationLevel=propLevel;}

        const UnorderedSet<int> & getBodyReason()const{return bodyLit;}
        void setBodyReason(const UnorderedSet<int> & bodyReason){ 
            bodyLit.clear();
            for(unsigned i=0;i<bodyReason.size();i++)
                this->bodyLit.insert(bodyReason[i]);
        }

        const std::vector<int> & getSharedVariables()const{return sharedVariables;}
        void setSharedVariables(const std::vector<int> & sharedVars){ 
            sharedVariables.clear();
            for(int v : sharedVars) 
                this->sharedVariables.push_back(v);
        }

        bool isPositive(int aggrId)const{return aggregates_sign[aggrId];}
        void setPositive(int aggrId, bool pos){aggregates_sign[aggrId]=pos;}

        PostponedReasonData(const PostponedReasonData& other){
            setAggregates(other.getAggregateId(),other.getAggregateSign());
            setPropagationLevel(other.getPropagationLevel());
            setBodyReason(other.getBodyReason());
            setSharedVariables(other.getSharedVariables());
        }

        PostponedReasonData operator=(const PostponedReasonData& other){
            
            setAggregates(other.getAggregateId(),other.getAggregateSign());
            setPropagationLevel(other.getPropagationLevel());
            setBodyReason(other.getBodyReason());
            setSharedVariables(other.getSharedVariables());
            return *this;
        }
        void print()const{
            std::cout << "Propagation Data"<<std::endl;
            std::cout << "Propagation Level: "<<propagationLevel<<std::endl;
            for(int i=0;i<aggregates_id.size();i++){
                std::string boolValue = aggregates_sign[i] ? "true":"false";
                std::cout << "Aggr "<<aggregates_id[i]<<" "<<boolValue<<std::endl;
            }
            std::cout << "shared variables: " ;
            for(int v : sharedVariables){
                std::cout << v << " ";
            }
            std::cout << std::endl << "bodyReason: ";
            for(int i=0;i<bodyLit.size();i++){
                std::cout << bodyLit[i] << " ";
            }
            std::cout << std::endl;
        }
    private:
        std::vector<int> aggregates_id;
        std::vector<bool> aggregates_sign;

        int propagationLevel;
        UnorderedSet<int> bodyLit;
        std::vector<int> sharedVariables;
};
#endif