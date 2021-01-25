#ifndef REASONTABLE_H
#define REASONTABLE_H

#include <iostream>
#include <vector>
#include <unordered_map>
class ReasonTable{

    private:
        std::vector<int> reason;
        std::unordered_map<int,int> literalToLevel;
        int currentLevel=-1;
        std::unordered_map<int,int> levelSize;
    public:
        void insert(int v){
            //remember to call add level before
            if(literalToLevel.count(v)<=0){
                literalToLevel[v]=currentLevel;
                levelSize[currentLevel]++;
                reason.push_back(v);
            }
        }
        void erase(int v,int level){
            if(literalToLevel.count(v)>0 && literalToLevel[v]==level){
                int starter=0;
                for(int i=0;i<level;i++){
                    starter+=levelSize[i];
                }
                for(int i=starter;i<starter+levelSize[level];i++){
                    if(reason[i]==v){
                        levelSize[level]--;
                        reason.erase(reason.begin()+i);
                        literalToLevel.erase(v);
                        if(levelSize[level]==0){
                            for(int v=level+1;v<=currentLevel;v++){
                                for(int j=0;j<levelSize[v];j++,i++)
                                    literalToLevel[reason[i]]--;
                                levelSize[v-1]=levelSize[v];
                            }
                            levelSize.erase(currentLevel);
                            currentLevel--;

                        }
                        return;
                    }
                }
            }
        }
        unsigned size()const{
            return reason.size();
        }
        int getCurrentLevel()const{ return currentLevel;}
        void addLevel(){currentLevel++;}

        int level(int v) {if(literalToLevel.count(v)>0) return literalToLevel[v]; return -1;}
        std::vector<int>::iterator begin(){return reason.begin();}
        std::vector<int>::iterator end(){return reason.end();}

};
#endif