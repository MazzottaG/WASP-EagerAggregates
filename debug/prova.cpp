#include <iostream>
#include <vector>
#include <unordered_map>
#include<set>
#include <string>
#include "../src/lp2cpp/datastructures/ReasonTable.h"
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
    ReasonTable r;
    r.addLevel();

    r.addLevel();
    r.insert(2);
    r.insert(1);

    r.addLevel();
    r.addLevel();
    r.addLevel();
    r.insert(4);
    r.insert(1);
    std::vector<int>rr;
    rr.insert(rr.end(),r.begin(), r.end());
    rr.push_back(3);
    rr.push_back(5);

    r.print();
    for(int v : rr){
        std::cout << v << " ";
    }                 
}

