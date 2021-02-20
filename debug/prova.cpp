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
    std::unordered_map<DynamicCompilationVector*,std::set<VarsIndex>> m[1];
    DynamicTrie sharedv;
    DynamicTrie aggrVars;
    std::vector<int> empty;
    DynamicCompilationVector* body=sharedv.addElements(empty);
    // std::cout<<m[0][body].key_comp<<std::endl;
    // set<VarsIndex>::key_compare mycomp = m[0][body].key_comp();  

    std::vector<int> v1={2,1};
    std::vector<int> v2={1,2};
    std::vector<int> v3={2,2};
    std::vector<int> v4={1,3};
    std::vector<int> v5={2,3};
    std::vector<int> v6={1,1};
    std::vector<int> v7={2,3};
    
    DynamicCompilationVector* aggrKeyIndex1 = aggrVars.addElements(v1);
    DynamicCompilationVector* aggrKeyIndex2 = aggrVars.addElements(v2);
    DynamicCompilationVector* aggrKeyIndex3 = aggrVars.addElements(v3);
    DynamicCompilationVector* aggrKeyIndex4 = aggrVars.addElements(v4);
    DynamicCompilationVector* aggrKeyIndex5 = aggrVars.addElements(v5);
    if(aggrKeyIndex5!=nullptr){
        for(int i=0;i<aggrKeyIndex5->size();i++){
            std::cout<<aggrKeyIndex5->operator[](i)<<" ";
        }
        std::cout<<std::endl;
    }
    DynamicCompilationVector* aggrKeyIndex6 = aggrVars.addElements(v6);
    DynamicCompilationVector* aggrKeyIndex7 = aggrVars.addElements(v7);
    m[0][body].insert(VarsIndex(2,aggrKeyIndex1));
    m[0][body].insert(VarsIndex(1,aggrKeyIndex2));
    m[0][body].insert(VarsIndex(2,aggrKeyIndex3));
    bool ins = m[0][body].insert(VarsIndex(1,aggrKeyIndex4)).second;
    if(ins){
        std::cout<<"Inserted"<<std::endl;
        if(m[0][body].find(VarsIndex(1,aggrKeyIndex4))==m[0][body].end()){
            std::cout<<"UnableToFind"<<std::endl;
        }else{
            std::cout<<"Found"<<std::endl;
        }
    }else{
        std::cout<<"Not inserted"<<std::endl;
    }
    m[0][body].insert(VarsIndex(2,aggrKeyIndex5));
    m[0][body].insert(VarsIndex(1,aggrKeyIndex6));
    VarsIndex comp(1,aggrKeyIndex4);

    if(m[0][body].find(VarsIndex(1,aggrKeyIndex4)) == m[0][body].end()){
        std::cout<<"not in"<<std::endl;
    }else{
        std::cout<<"in"<<std::endl;
    }
    
}

