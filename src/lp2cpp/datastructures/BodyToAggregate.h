#ifndef BODYTOAGGREGATE_H
#define BODYTOAGGREGATE_H
#include <vector>
#include <map>
#include <unordered_set>
#include <cmath>
#include "TupleWithoutReasons.h"

class BodyToAggregate {
    
    public:
        void addAggrKeyToBody(const std::vector<int>& k,int id){
            keys[k].insert(id);
        }
        void eraseAggrKeyFromBody(const std::vector<int>& k,int id){
            if(keys.find(k)!=keys.end()){
                keys[k].erase(id);
            }
        }
        bool bodyContainsAggrKey(const std::vector<int>& k,int id){
            if(keys.find(k)==keys.end())
                return false;
            
            return keys[k].find(id) != keys[k].end();   
        }
        
    private:
        std::map<std::vector<int>,std::unordered_set<int>> keys;
};
#endif 

