#include "TupleFactory.h"
#include "AggregateSetCmp.h"

bool AggregateSetCmp::cmp(const int& l1,const int& l2)const{
    TupleLight* first = factory->getTupleFromInternalID(l1);
    unsigned firstAggrVarIndex = factory->getIndexForAggrSet(first->getPredicateName());
    int w = first->at(firstAggrVarIndex)-factory->getTupleFromInternalID(l2)->at(firstAggrVarIndex);
    return w==0 ? l1 > l2 : w > 0;
}
TupleFactory* AggregateSetCmp::factory;
