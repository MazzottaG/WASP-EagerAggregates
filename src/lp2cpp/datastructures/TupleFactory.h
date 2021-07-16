#ifndef TUPLEFACTORY_H
#define TUPLEFACTORY_H
#include <unordered_map>
#include "SmartTuple.h"
#include <list>

class TupleFactory{
    private:
        std::unordered_map<SmartTuple,int,SmartTuplesHash> tupleToInternalVar;
        std::vector<SmartTuple> internalIDToTuple;
        std::unordered_map<int,SmartTuple> waspIDToTuple;
        std::list<TupleLight> storage;

    public:
        TupleFactory(/* args */){

        }
        ~TupleFactory(){

        }
        //store new wasp tuple and return a smart reference to it
        TupleLight* addNewTuple(std::vector<int> terms,const std::string* predName, unsigned id){
            // std::cout<<"addNewTuple"<<std::endl;
            TupleLight tuple (terms,predName);
            SmartTuple smart(&tuple);
            auto it = tupleToInternalVar.find(smart);
            if(it==tupleToInternalVar.end()){
                // tuple.shrink_to_fit();
                storage.push_back(tuple);
                SmartTuple trueReference(&storage.back());
                tupleToInternalVar.insert({trueReference,internalIDToTuple.size()});
                internalIDToTuple.push_back(trueReference);
                waspIDToTuple.insert({id,trueReference});
                trueReference.getReal()->setWaspID(id);
                trueReference.getReal()->setId(storage.size());
                // std::cout<<trueReference.getReal()->getWaspID()<<" "<<trueReference.getReal()->getId()<<" ";trueReference.getReal()->print();std::cout<<" "<<id<<std::endl;
                return trueReference.getReal();
            }
            assert(it->second == id);
            return it->first.getReal();
        }
        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalTuple(std::vector<int> terms,const std::string* predName){
            TupleLight tuple (terms,predName);
            SmartTuple smart(&tuple);
            auto it = tupleToInternalVar.find(smart);
            if(it==tupleToInternalVar.end()){
                storage.push_back(tuple);
                SmartTuple trueReference(&storage.back());
                tupleToInternalVar.insert({trueReference,internalIDToTuple.size()});
                internalIDToTuple.push_back(trueReference);
                trueReference.getReal()->setId(storage.size());
                return trueReference.getReal();
            }
            // assert(it->second == -1);
            return it->first.getReal();
        }
        TupleLight* find(std::vector<int> terms,const std::string* predName){
            TupleLight tuple (terms,predName);
            SmartTuple smart(&tuple);
            auto it = tupleToInternalVar.find(smart);
            if(it==tupleToInternalVar.end()){
                return NULL;
            }
            // assert(it->second == -1);
            return it->first.getReal();
        }
        TupleLight* find(const TupleLight& t){
            TupleLight tuple (t);
            SmartTuple smart(&tuple);
            auto it = tupleToInternalVar.find(smart);
            if(it==tupleToInternalVar.end()){
                return NULL;
            }
            // assert(it->second == -1);
            return it->first.getReal();
        }
        TupleLight* getTupleFromWASPID(int id){
            if(waspIDToTuple.count(id)!=0)
                return waspIDToTuple[id].getReal();
            return NULL;

        }

        TupleLight* getTupleFromInternalID(int id){
            if(id<=internalIDToTuple.size())
                return internalIDToTuple[id-1].getReal();
            return NULL;
        }
        void print()const {
            for(auto pair : waspIDToTuple){
                std::cout<<"Wasp id: "<<pair.first<<" ";
                pair.second.getReal()->print();
            }
        }
};

#endif