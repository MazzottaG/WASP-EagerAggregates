/*
 *
 *  Copyright 2021  BLIND.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */
#include "TupleFactory.h"
#include "AggregateSetCmp.h"

bool AggregateSetCmp::cmp(const int& l1,const int& l2)const{
    TupleLight* first = factory->getTupleFromInternalID(l1);
    unsigned firstAggrVarIndex = factory->getIndexForAggrSet(first->getPredicateName());
    int w = first->at(firstAggrVarIndex)-factory->getTupleFromInternalID(l2)->at(firstAggrVarIndex);
    return w==0 ? l1 > l2 : w > 0;
}
TupleFactory* AggregateSetCmp::factory;
