#ifndef TUPLEFACTORY_H
#define TUPLEFACTORY_H
#include <unordered_map>
#include "TupleWithReasons.h"
#include "SmartTupleWithReason.h"
#include <list>

class TupleFactory{
    private:
        std::unordered_map<SmartTupleWithReasons,int,SmartTuplesHash> tupleToInternalVar;
        std::vector<SmartTupleWithReasons> internalIDToTuple;
        std::unordered_map<int,SmartTupleWithReasons> waspIDToTuple;
        std::list<TupleWithReasons> storage;

    public:
        TupleFactory(/* args */){

        }
        ~TupleFactory(){

        }
        //store new wasp tuple and return a smart reference to it
        TupleWithReasons* addNewTuple(std::vector<int> terms,const std::string* predName, unsigned id){
            // std::cout<<"addNewTuple"<<std::endl;
            TupleWithReasons tuple (terms,predName);
            SmartTupleWithReasons smart(&tuple);
            auto it = tupleToInternalVar.find(smart);
            if(it==tupleToInternalVar.end()){
                
                storage.push_back(tuple);
                SmartTupleWithReasons trueReference(&storage.back());
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
        TupleWithReasons* addNewInternalTuple(std::vector<int> terms,const std::string* predName){
            TupleWithReasons tuple (terms,predName);
            SmartTupleWithReasons smart(&tuple);
            auto it = tupleToInternalVar.find(smart);
            if(it==tupleToInternalVar.end()){
                storage.push_back(tuple);
                SmartTupleWithReasons trueReference(&storage.back());
                tupleToInternalVar.insert({trueReference,internalIDToTuple.size()});
                internalIDToTuple.push_back(trueReference);
                trueReference.getReal()->setId(storage.size());
                return trueReference.getReal();
            }
            // assert(it->second == -1);
            return it->first.getReal();
        }

        TupleWithReasons* getTupleFromWASPID(int id){
            if(waspIDToTuple.count(id)!=0)
                return waspIDToTuple[id].getReal();
            return NULL;

        }
        TupleWithReasons* getTupleFromInternalID(int id){
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