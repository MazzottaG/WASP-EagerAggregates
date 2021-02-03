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
    //0 vuoto
    r.addLevel();
    r.insert(1);
    r.insert(2);
    //1 pieno
    r.addLevel();
    //2 vuoto
    r.addLevel();
    //3 vuoto
    r.addLevel();
    //4 vuoto
    r.addLevel();
    r.insert(3);
    r.insert(4);
    //5 pieno

    r.eraseCurrentLevel();

    r.eraseCurrentLevel();
    
    r.eraseCurrentLevel();

    r.eraseCurrentLevel();

    r.eraseCurrentLevel();
    r.eraseCurrentLevel();
    r.eraseCurrentLevel();

    r.addLevel(); // -> -1+1
    r.insert(3);
    r.insert(4);
    //0 pieno
    r.addLevel(); //->0+1
    //1 vuoto
    r.addLevel(); // ->1
    r.insert(2);
    r.insert(1);
    //2 pieno
    r.addLevel(); //1+1
    //
    r.addLevel(); //2
    r.addLevel(); //2
    
    r.eraseCurrentLevel();
    r.eraseCurrentLevel();
    r.eraseCurrentLevel();

    r.addLevel();
    r.insert(0);
    r.eraseCurrentLevel();
    r.eraseCurrentLevel();
    r.eraseCurrentLevel();
    r.eraseCurrentLevel();
    

}

