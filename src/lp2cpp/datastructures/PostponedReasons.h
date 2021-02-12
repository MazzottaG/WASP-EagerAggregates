#ifndef POSTPONEDREASONS_H
#define POSTPONEDREASONS_H
#include <iostream>
#include <vector>
#include "PostponedReasonData.h"


class PostponedReasons{

    public:
        PostponedReasonData& operator[](int i){
            // std::cout << "getting "<<std::endl;
            if(mapping.find(i)==mapping.end())
                mapping.insert({i,PostponedReasonData()});

            return mapping[i];
        }
        void erase(int lit){
            // std::cout << "Erasing "<<lit<<std::endl;
            if(mapping.find(lit) != mapping.end())
                mapping[lit].clear();
        }
        void addPropagation(int lit,const std::vector<int>& aggr_id, const std::vector<bool>& aggr_sign,int propLevel,std::vector<int>body,std::vector<int>sharedVars){
            // std::cout <<"Adding prop lit "<<lit <<std::endl;
            if(mapping.find(lit)==mapping.end()){
                // std::cout<<"New"<<std::endl;
                mapping.insert({lit,PostponedReasonData(aggr_id,aggr_sign,propLevel,body,sharedVars)});
                return;
            }

                PostponedReasonData* data = &mapping[lit];
            // if(data->getPropagationLevel() == -1){
                // std::cout<<"Existing"<<std::endl;
                data->setAggregates(aggr_id,aggr_sign);
                data->setPropagationLevel(propLevel);
                data->setBodyReason(body);
                data->setSharedVariables(sharedVars);
            // }else{

            // }
            // std::cout << "Added" <<std::endl;
            // reas.print();
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
        std::unordered_map<int,PostponedReasonData> mapping;

        // int checkSize(int i){
        //     int pos = i>0 ? i : -1*i;
        //     if(pos>=mapping.size()){
        //         mapping.resize(pos+1);
        //     }

        //     return pos;
        // }
};

#endif
