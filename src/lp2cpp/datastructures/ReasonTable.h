#ifndef REASONTABLE_H
#define REASONTABLE_H

#include <iostream>
#include <vector>
#include <unordered_map>
class ReasonTable{
    private:
        std::vector<int> reason;
        std::unordered_map<int,int> literalToPos;
    public:
        void insert(int v){
            if(literalToPos.count(v)<=0){
                literalToPos[v]=reason.size();
                reason.push_back(v);
            }
        }
        void erase(int v){
            if(literalToPos.count(v)>0){
                for(int i=literalToPos[v]+1;i<reason.size();i++){
                    literalToPos[reason[i]]--;
                }
                reason.erase(reason.begin()+literalToPos[v]);
                literalToPos.erase(v);
            }
        }
        unsigned size()const{
            return reason.size();
        }
        int pos(int v) {if(literalToPos.count(v)>0) return literalToPos[v]; return -1;}
        std::vector<int>::iterator begin(){return reason.begin();}
        std::vector<int>::iterator end(){return reason.end();}

};
#endif