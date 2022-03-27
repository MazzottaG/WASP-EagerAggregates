#ifndef TUPLE_TRIE_SET
#define TUPLE_TRIE_SET
#include "TupleLight.h"
#include <unordered_map>
class TupleNode{
    private:
        int term;
        TupleLight* tuple;
        std::unordered_map<int,TupleNode*> children;
    public:
        TupleNode(int t){term=t;tuple=NULL;}
        ~TupleNode(){
            for(auto pair : children) delete pair.second;
        }

        TupleNode* add(int t){
            if(children.count(t)==0){
                children[t]=new TupleNode(t);
            }
            return children[t];
        }

        TupleNode* check(int t){
            auto it = children.find(t);
            if(it==children.end()){
                return NULL;
            }
            return it->second;
        }

        void setTuple(TupleLight* t){
            tuple=t;
        }
        TupleLight* getTuple(){return tuple;}

        bool existsTuple()const{return tuple!=NULL;}
        int getChilderCount()const{return children.size();}
        std::unordered_map<int,TupleNode*> getChildren()const {return children;}
        const TupleNode* getChild(int id)const {
            return children.find(id)->second;
        }
};
class TupleTrieSet{

    private:
        TupleNode* root;
        unordered_map<const std::string*,int> predIdMap;
    public:
        TupleTrieSet(){root=new TupleNode(INT_MAX);}
        ~TupleTrieSet(){delete root;}
        
        TupleNode* addNodeForTuple(TupleLight* t){
            auto it = predIdMap.emplace(t->getPredicateName(),predIdMap.size());
            TupleNode* current = root->add(it.first->second);
            for(int i=0;i<t->size();i++){
                current = current->add(t->at(i));
            }
            return current;
        }

        TupleLight* find(TupleLight* t){
            auto it = predIdMap.find(t->getPredicateName());
            if(it==predIdMap.end())
                return NULL;
            TupleNode* current = root->check(it->second);
            for(int i=0;i<t->size();i++){
                current = current->check(t->at(i));
                if(current==NULL)
                    return NULL;
            }
            return current->getTuple();
        }
        void printStats()const{
            for(auto predicates:predIdMap){
                int levelsize = 1;
                float avg=0;
                float max=0;
                float count=0;
                
                std::vector<std::vector<float>> metrics;
                std::vector<const TupleNode*> visited({root->getChild(predicates.second)});
                for(int i=0;i<visited.size();i++){
                    if(visited[i]->getChildren().size() > max){
                        max=visited[i]->getChildren().size();
                    }
                    avg+=visited[i]->getChildren().size();
                    count++;
                    for(auto pair : visited[i]->getChildren()){
                        visited.push_back(pair.second);
                    }
                    levelsize--;
                    if(levelsize==0){
                        metrics.push_back({avg/count,max,count});
                        avg=0;
                        count=0;
                        max=0;
                        levelsize=visited.size()-i-1;
                    }
                }
                for(int i=0;i<metrics.size();i++){
                    std::cout << "Predicate "<<*predicates.first<<" Level "<<i+1<<" avg "<<metrics[i][0]<<" max "<<metrics[i][1]<<" count "<<metrics[i][2]<<std::endl;
                }
            }
        }
};
#endif