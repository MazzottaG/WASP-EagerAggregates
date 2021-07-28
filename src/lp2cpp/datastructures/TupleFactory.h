#ifndef TUPLEFACTORY_H
#define TUPLEFACTORY_H
#include <unordered_map>
#include <list>
#include <cassert>
#include "TupleLight.h"
struct TuplePointerHash {

   inline std::size_t operator()(const TupleLight* v) const {
        std::size_t seed = 0;
        for (int i=0; i < v->size(); i++) {
            seed ^= v->at(i) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

struct TuplePointerEq {
   bool operator()(const TupleLight *val1, const TupleLight* val2) const{
      return *val1 == *val2;
   }
};
class TupleFactory{
    private:
        std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq> tupleToInternalVar;
        std::vector<TupleLight*> internalIDToTuple;
        std::unordered_map<int,TupleLight*> waspIDToTuple;
        std::list<TupleLight> storage;

    public:
        static TupleLight bufferTuple;
        void setBufferedTupleStorage(int* vectorData,int size,const std::string* predName){
            bufferTuple.setContent(vectorData,size,predName);
        }
        TupleFactory(/* args */){
            storage.push_back(TupleLight());
            internalIDToTuple.push_back(&storage.back());
        }
        
        ~TupleFactory(){

        }
        void removeFromCollisionsList(int id){
            if(id < internalIDToTuple.size()){
                TupleLight* tupleToRemove = internalIDToTuple[id];
                // std::cout<<"Removing from collisionsList ";tupleToRemove->print();std::cout<<std::endl;
                std::vector<std::pair<std::vector<unsigned>*,unsigned>>* collisionsLists = &tupleToRemove->getCollisionsLists();
                for (unsigned i=0; i<collisionsLists->size(); i++) {
                    std::vector<unsigned> & collisionList = *(collisionsLists->at(i).first);
                    // std::cout<<"Original collisions list: "<<std::endl;
                    // for(unsigned id : collisionList){
                    //     internalIDToTuple[id]->print();
                    // }
                    // std::cout<<std::endl;
                    unsigned index = collisionsLists->at(i).second;
                    collisionList[index] = collisionList[collisionList.size() - 1];
                    // std::cout<<"Swapping with ";internalIDToTuple[collisionList[index]]->print();std::cout<<std::endl;
                    internalIDToTuple[collisionList[index]]->setCollisionListIndex(&collisionList, index,i);
                    collisionList.pop_back();
                    // std::cout<<"New collisions list: "<<std::endl;
                    // for(unsigned id : collisionList){
                    //     internalIDToTuple[id]->print();
                    // }
                    // std::cout<<std::endl;
                }
                tupleToRemove->clearCollisionsList();
            }
        }
        //store new wasp tuple and return a smart reference to it
        TupleLight* addNewTuple(std::vector<int> terms,const std::string* predName, unsigned id){
            // std::cout<<"addNewTuple"<<std::endl;
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            // SmartTuple smart(&tuple);
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                // tuple.shrink_to_fit();
                // TupleLight tuple(terms,predName);
                storage.push_back(bufferTuple);
                TupleLight* reference = &storage.back();
                tupleToInternalVar.insert(reference);
                internalIDToTuple.push_back(reference);
                waspIDToTuple.insert({id,reference});
                reference->setWaspID(id);
                reference->setId(storage.size()-1);
                bufferTuple.clearContent();
                // std::cout<<reference->getWaspID()<<" "<<reference->getId()<<" ";reference->print();std::cout<<" "<<id<<std::endl;
                return &storage.back();
            }
            bufferTuple.clearContent();
            // std::cout<<"Already added"<<std::endl;
            // assert(it->getWaspID() == id);
            return *it;
        }
        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalTuple(std::vector<int> terms,const std::string* predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                
                storage.push_back(bufferTuple);
                TupleLight* trueReference = &storage.back();
                tupleToInternalVar.insert(trueReference);
                internalIDToTuple.push_back(trueReference);
                trueReference->setId(storage.size()-1);
                bufferTuple.clearContent();
                return trueReference;
            }
            bufferTuple.clearContent();

            // assert(it->second == -1);
            return *it;
        }
        TupleLight* find(std::vector<int> terms,const std::string* predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                bufferTuple.clearContent();
                return NULL;
            }
            bufferTuple.clearContent();
            // assert(it->second == -1);
            return *it;
        }
        TupleLight* find(const TupleLight& t){
            TupleLight* tuple = const_cast<TupleLight *>(&t);
            auto it = tupleToInternalVar.find(tuple);
            if(it==tupleToInternalVar.end()){
                // std::cout<<"Not found"<<std::endl;
                return NULL;
            }
            // assert(it->second == -1);
            return *it;
        }
        TupleLight* getTupleFromWASPID(int id){
            if(waspIDToTuple.count(id)!=0)
                return waspIDToTuple[id];
            return NULL;

        }

        TupleLight* getTupleFromInternalID(int id)const{
            if(id<internalIDToTuple.size())
                return internalIDToTuple[id];
            return NULL;
        }

        void printModelAsConstraint()const {
            std::cout<<"Tuple factory"<<std::endl;
            for(auto tuple : storage){
                if(tuple.getWaspID()!=0){
                    tuple.printAsConstraint();
                }
                
            }
        }
        void print()const {
            std::cout<<"Tuple factory"<<std::endl;
            bool first=true;
            for(auto tuple : storage){
                if(!first)
                    tuple.print();
                else
                    first=false;
            }
        }
        void printSize(){
            std::cout<<storage.size()<<std::endl;
        }
};


#endif