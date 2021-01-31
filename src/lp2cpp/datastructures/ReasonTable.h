#ifndef REASONTABLE_H
#define REASONTABLE_H

#include <iostream>
#include <vector>
#include <unordered_map>
class ReasonTable{

    private:
        std::vector<int> reason;
        std::unordered_map<int,int> literalToLevel;
        int currentLevel;
        std::unordered_map<int,int> levelSize;
    public:
        ReasonTable(){
            currentLevel=-1;
        }
        void insert(int v){
            //remember to call add level before

            if(literalToLevel.count(v)<=0){
                literalToLevel[v]=currentLevel;
                levelSize[currentLevel]++;
                reason.push_back(v);
            }
        }
        void eraseCurrentLevel(){
            if(currentLevel>=0){
                while(levelSize[currentLevel]>0){

                    levelSize[currentLevel]--;
                    int v = reason.back();
                    literalToLevel.erase(v);
                    reason.pop_back();
                }
                levelSize.erase(currentLevel);
                currentLevel--;
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
        void print(){
            int index=0;
            for(int i=0;i<=currentLevel;i++){
                std::cout<<"Level "<<i<<std::endl;
                for(int j=0;j<levelSize[i];j++,index++){
                    std::cout<<reason[index]<<" ";
                }
                std::cout<<std::endl;
            }
        }
        int getCurrentLevel()const{ return currentLevel;}
        void addLevel(){currentLevel++;}
        int level(int v) {if(literalToLevel.count(v)>0) return literalToLevel[v]; return -1;}
        std::vector<int>::iterator begin(){return reason.begin();}
        std::vector<int>::iterator end(){return reason.end();}

};
#endif