#ifndef REASONTABLE_H
#define REASONTABLE_H

#include <iostream>
#include <vector>
#include <unordered_map>
class ReasonTable{

    private:
        std::vector<int> reason;
        std::vector<int> literalToLevel;

        int currentLevel;
        int removingLevels;
        int resizeFactor;

    public:
        ReasonTable(){
            currentLevel=0;
            removingLevels=0;
            resizeFactor=1;
        }
        void insert(int v){
            int pos=v;
            if(pos < 0)
                pos=v*-1;
            if(pos >= literalToLevel.size()){
                literalToLevel.resize(pos+1);
                
            }
            if(literalToLevel[pos] > 0 && literalToLevel[pos]<=currentLevel)
                return;
            literalToLevel[pos]=currentLevel;
            reason.push_back(v);
        }
        void eraseCurrentLevel(){
            if(currentLevel>0){
                currentLevel--;
                if(currentLevel==0)
                    deleteErasedLevel();
                else
                    removingLevels++;
            }
        }
        unsigned size()const{
            return reason.size();
        }
        void print(){
            for(int v : reason){
                int a=v;
                if(a<0)
                    a*=-1;
                std::cout<<v<<";"<<literalToLevel[a]<<" ";
            }
            std::cout<<std::endl;
        }
        int getCurrentLevel()const{
            return currentLevel;
        }
        void addLevel(){
            if(removingLevels>0){
                deleteErasedLevel();
            }
            currentLevel++;
        }
        int level(int v) {
            int a=v;
            if(a<0) 
                a*=-1;
            if(literalToLevel.size()>a) 
                return literalToLevel[a]; 
            return 0;
        }
        std::vector<int> getLiteralUntil(int level){
            if(level==0)
                return {};
            std::vector<int> reas;
            for(int i=0;i<reason.size();i++){
                int lit=reason[i];
                int pos= lit > 0 ? lit : -1*lit;
                if(literalToLevel[pos]>level){
                    break;
                }
                reas.push_back(lit);
            }
            return reas;
        }
        std::vector<int>::iterator begin(){return reason.begin();}
        std::vector<int>::iterator end(){return reason.end();}
        private:
        void deleteErasedLevel(){
            for(int i=0;i<literalToLevel.size();i++){
                if(literalToLevel[i]>currentLevel){
                    literalToLevel[i]=0;
                    reason.pop_back();
                }
            }
            removingLevels=0;
        }

};
#endif