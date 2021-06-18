#ifndef SMARTTUPLEWITHREASONS_H
#define SMARTTUPLEWITHREASONS_H
#include <vector>
#include <string>
#include <unordered_set>
#include "TupleWithReasons.h"
#include <iostream>
using namespace std;

class SmartTupleWithReasons {
    public:
        SmartTupleWithReasons(const SmartTupleWithReasons& t):realTuple(t.realTuple){

        }
        SmartTupleWithReasons(TupleWithReasons* t):realTuple(t){

        }
        SmartTupleWithReasons(){
            realTuple=NULL;
        }
        bool isNull(){
            return realTuple==NULL;
        }

        void addPositiveReason(const TupleWithReasons* r) const {
            realTuple->addPositiveReason(r);
        }

        void addNegativeReason(const TupleWithReasons & r) const {
            realTuple->addNegativeReason(r);
        }

        const vector<const TupleWithReasons*> & getPositiveReasons() const {
            return realTuple->getPositiveReasons();
        }

        const vector<TupleWithReasons> & getNegativeReasons() const {
            return realTuple->getNegativeReasons();
        }

        bool operator==(const TupleWithReasons& right) const {
            return realTuple->operator==(right);
        }
        bool operator==(const SmartTupleWithReasons& right) const {
            return realTuple->operator==(*right.realTuple);
        }
        
        TupleWithReasons& operator=(const TupleWithReasons& right){
            return realTuple->operator=(right);
        }
        SmartTupleWithReasons& operator=(const SmartTupleWithReasons& right){
            *realTuple=*right.realTuple;
            return *this;
        }
        int& operator[](unsigned i)const{
            return realTuple->operator[](i);
        }
        int& at(unsigned i)const{
            return realTuple->operator[](i);
        }
        const std::string* getPredicateName() const {
            return realTuple->getPredicateName();
        }

        bool isNegated() const {
            return realTuple->isNegated();
        }

        void setNegated(bool negated) {
            realTuple->setNegated(negated);
        }

        unsigned getId() const {
            return realTuple->getId();
        }

        void setId(unsigned id) const {
            realTuple->setId(id);
        }
        
        void print() const {
            realTuple->print();
        }
        
        unsigned size()const{
            return realTuple->size();
        }

        TupleWithReasons* getReal()const {return realTuple;}

    private:
        TupleWithReasons* realTuple;

};

struct SmartTuplesHash {

    inline std::size_t operator()(const SmartTupleWithReasons & v) const {
        std::size_t seed = 0;
        for (int i=0; i<v.size(); i++) {
            seed ^= v[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

#endif /* TUPLE_H */

