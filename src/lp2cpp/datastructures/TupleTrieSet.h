#ifndef TUPLE_TRIE_SET
#define TUPLE_TRIE_SET
#include "TupleLight.h"
#include <unordered_map>
const int HALF_INT_MAX = INT_MAX/2; 

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

        TupleNode* add(size_t t){
            if(children.count(t)==0){
                children[t]=new TupleNode(t);
            }
            return children[t];
        }

        TupleNode* check(size_t t){
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
    public:
        TupleTrieSet(){root=new TupleNode(INT_MAX);}
        ~TupleTrieSet(){delete root;}
        
        TupleNode* addNodeForTuple(TupleLight* t){
            TupleNode* current = root;
            for(int i=0;i<t->size();i++){
                current = current->add(t->at(i));
            }
            return current;
        }

        TupleLight* find(TupleLight* t){
            TupleNode* current = root;
            for(int i=0;i<t->size();i++){
                current = current->check(t->at(i));
                if(current==NULL)
                    return NULL;
            }
            return current->getTuple();
        }
        void printStats()const{
        }
};
#endif