#include <iostream>
#include <vector>
#include <unordered_map>
#include <set>
#include <map>
#include <string>
// #include "../src/lp2cpp/datastructures/ReasonTable.h"
#include "../src/lp2cpp/datastructures/VarsIndex.h"
#include "../src/lp2cpp/datastructures/DynamicTrie.h"
#include "../src/lp2cpp/datastructures/VariablesMapping.h"
#include "../src/lp2cpp/datastructures/TupleWithReasons.h"
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
    std::unordered_map<DynamicCompilationVector*,std::set<VarsIndex>> m;
    DynamicTrie sharedv;
    DynamicTrie vVars;
    std::vector<int> v = {1,1};
    std::vector<int> vc = {1,1};
    std::vector<int> v1 = {2,2};
    std::vector<int> v1c = {2,2};
    std::vector<int> vars = {1,1};
    std::vector<int> vars1 = {1,2};
    std::vector<int> vars2 = {2,1};
    std::vector<int> vars3 = {2,2};
    m[sharedv.addElements(v)].insert(VarsIndex(1,vVars.addElements(vars)));
    m[sharedv.addElements(vc)].insert(VarsIndex(1,vVars.addElements(vars1)));
    m[sharedv.addElements(v1)].insert(VarsIndex(2,vVars.addElements(vars2)));
    m[sharedv.addElements(v1c)].insert(VarsIndex(2,vVars.addElements(vars3)));

    for(auto it = m.begin();it!=m.end();it++){
        std::cout<<it->first->operator[](0)<<" "<<it->first->operator[](1)<<std::endl;
    }

}

