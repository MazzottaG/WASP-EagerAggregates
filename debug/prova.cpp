#include <iostream>
#include <vector>
#include "../src/lp2cpp/datastructures/ReasonTable.h"
int main(){
    ReasonTable r;
    r.addLevel();
    r.insert(12);
    r.insert(21);
    r.addLevel();

    r.erase(12,r.level(12));
    r.insert(-31);
    r.insert(-13);
    r.erase(-13,r.level(-13));
    r.erase(-31,r.level(-13));
    for(auto it = r.begin();it!=r.end();it++){
        std::cout<<*it<<" ";
    }
    std::cout<<std::endl;
    r.addLevel();
    r.insert(32);
    r.insert(21);

    r.erase(21,r.level(32));
    for(auto it = r.begin();it!=r.end();it++){
        std::cout<<*it<<" ";
    }
    std::cout<<std::endl;
}