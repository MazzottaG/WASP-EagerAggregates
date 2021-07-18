#include "TupleFactory.h"

TupleLight* TupleFactory::getTupleFromInternalID(int id)const{
    if(id<=internalIDToTuple.size())
        return internalIDToTuple[id-1].getReal();
    return NULL;
}
