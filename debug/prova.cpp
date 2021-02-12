#include <iostream>
#include <vector>
#include <unordered_map>
#include<set>
#include <string>
#include "../src/lp2cpp/datastructures/ReasonTable.h"
#include "../src/lp2cpp/datastructures/TupleWithReasons.h"
#include "../src/lp2cpp/datastructures/PredicateSet.h"
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
   r.addLevel();//not a(5)
   r.insert(-5);
   r.addLevel();//not a(4)
   r.insert(-4);
   r.addLevel();//not a(3)
   r.insert(-3);
   r.addLevel();//a(2)
   r.addLevel();//not a(1)
   r.insert(-1);
   r.print();
   
   
   

}

