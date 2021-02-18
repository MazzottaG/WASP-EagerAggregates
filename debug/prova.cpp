#include <iostream>
#include <vector>
#include <unordered_map>
#include <set>
#include <map>
#include <string>
// #include "../src/lp2cpp/datastructures/ReasonTable.h"
// #include "../src/lp2cpp/datastructures/TupleWithReasons.h"
// #include "../src/lp2cpp/datastructures/PredicateSet.h"
using namespace std;
void backTrack(std::set<int> trueLit,std::set<int> falseLit,const std::unordered_map<int,std::string>&varToLit,std::vector<int> toVisit,int current){
    if(current==toVisit.size()){
        for(const auto & lit : varToLit){
            if(trueLit.count(lit.first)>0){
                std::cout<<lit.second<<" ";
            }else{
                std::cout<<"not "<<lit.second<<" ";
            }
        }
        std::cout<<std::endl;
        return;
    }
    trueLit.insert(toVisit[current]);
    backTrack(trueLit,falseLit,varToLit,toVisit,current+1);
    trueLit.erase(toVisit[current]);
    falseLit.insert(toVisit[current]);
    backTrack(trueLit,falseLit,varToLit,toVisit,current+1);
    falseLit.erase(toVisit[current]);

}
int main(){
    std::map<std::vector<int>,int> aggrVars;
    std::unordered_map<int*,const std::vector<int>*> reverse_mapping;
    int count = 0;
    // {1,1},{1,2},{1,3},{2,1},{2,2},{2,3},{3,1},{3,2},{3,3}
    std::unordered_map<int,std::set<int> > s; 
    for(int j=1;j<4;j++){
        auto it=aggrVars.insert({{2,j},0});
        if(it.second){
            int size = aggrVars.size();
            auto nextIt=it.first;
            nextIt++;
            int count=0;
            for(;nextIt!=aggrVars.end();nextIt++){
                count++;
                nextIt->second++;
            }
            it.first->second=size-count;
            reverse_mapping[&it.first->second] = &it.first->first;
        }
    }
    int index = aggrVars[{2,1}];
    s[0].insert(index);
    index = aggrVars[{2,2}];
    s[0].insert(index);
    index = aggrVars[{2,3}];
    s[0].insert(index);

    for(auto it=s[0].rbegin();it!=s[0].rend();it++){
        std::cout << *it <<" ";
    }
    std::cout << std::endl;

    for(int j=1;j<4;j++){
        auto it=aggrVars.insert({{1,j},0});
        if(it.second){
            int size = aggrVars.size();
            auto nextIt=it.first;
            nextIt++;
            int count=0;
            for(;nextIt!=aggrVars.end();nextIt++){
                count++;
                nextIt->second++;
            }
            it.first->second=size-count;
            reverse_mapping[&it.first->second] = &it.first->first;
        }
    }
    
    index = aggrVars[{1,1}];
    s[0].insert(index);
    index = aggrVars[{1,2}];
    s[0].insert(index);
    index = aggrVars[{1,3}];
    s[0].insert(index);

    for(auto it=s[0].rbegin();it!=s[0].rend();it++){
        std::cout << (*it)<<" ";
    }
    std::cout << std::endl;

}

