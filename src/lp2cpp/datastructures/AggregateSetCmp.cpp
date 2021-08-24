#include "TupleFactory.h"
#include "AggregateSetCmp.h"

bool AggregateSetCmp::cmp(const int& l1,const int& l2)const{
    TupleLight* first = factory->getTupleFromInternalID(l1);
    TupleLight* second = factory->getTupleFromInternalID(l2);
    unsigned firstAggrVarIndex = factory->getIndexForAggrSet(first->getPredicateName());
    int v1 = first->at(firstAggrVarIndex);
    int v2 = second->at(firstAggrVarIndex);
    if(v1 == v2){
        return l1 > l2;
    }
    return v1 > v2;
}
TupleFactory* AggregateSetCmp::factory;
