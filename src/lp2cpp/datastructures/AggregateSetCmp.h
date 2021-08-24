#ifndef AGGREGATESETCMP_H
#define AGGREGATESETCMP_H
class TupleFactory;
class AggregateSetCmp
{
    public:
        static TupleFactory* factory;
        bool cmp(const int& lit1,const int& lit2)const;
        bool operator()(const int& lit1,const int& lit2)const{
            return cmp(lit1,lit2);
        }
};

#endif