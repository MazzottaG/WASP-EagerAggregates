#include <iostream>
#include <vector>
#include <unordered_map>
#include <set>
#include <map>
#include <string>
// #include "../src/lp2cpp/datastructures/ReasonTable.h"
#include "../src/lp2cpp/datastructures/VarsIndex.h"
#include "../src/lp2cpp/datastructures/DynamicTrie.h"
#include "../src/lp2cpp/datastructures/VariablesMapping.h"
#include "../src/lp2cpp/datastructures/TupleWithReasons.h"
// #include "../src/lp2cpp/datastructures/PredicateSet.h"
using namespace std;
void backTrack(std::set<int> trueLit,std::set<int> falseLit,const std::unordered_map<int,std::string>&varToLit,std::vector<int> toVisit,int current){
    if(current==toVisit.size()){
        for(const auto & lit : varToLit){
            if(trueLit.count(lit.first)>0){
                std::cout<<lit.second<<" ";
            }else{
                std::cout<<"not "<<lit.second<<" ";
            }
        }
        std::cout<<std::endl;
        return;
    }
    trueLit.insert(toVisit[current]);
    backTrack(trueLit,falseLit,varToLit,toVisit,current+1);
    trueLit.erase(toVisit[current]);
    falseLit.insert(toVisit[current]);
    backTrack(trueLit,falseLit,varToLit,toVisit,current+1);
    falseLit.erase(toVisit[current]);

}
#include <bitset>
#include "../src/lp2cpp/datastructures/TupleLight.h"

struct TuplePointerHash {
    inline std::size_t operator()(const TupleLight* v) const {
        std::size_t seed=reinterpret_cast<size_t>(v->getPredicateName());
        int size =v->size();
        bool even = size%2==1;
        int start= even ? 1 : 0;
        if(even)
            seed ^= v->at(0) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        for (int i=start; i < size-1; i++) {
            seed ^= ((std::size_t)v->at(i)) + (((std::size_t)v->at(i+1))<<32) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};
struct TuplePointerHashPair {
    inline std::size_t operator()(const TupleLight* v) const {
        std::size_t seed=reinterpret_cast<size_t>(v->getPredicateName());
        int size =v->size();
        bool even = size%2==1;
        int start= even ? 1 : 0;
        if(even)
            seed ^= v->at(0) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        for (int i=start; i < size-1; i+=2) {
            seed ^= ((std::size_t)v->at(i)) + (((std::size_t)v->at(i+1))<<32) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};
const int predbits=8;
struct TuplePointerHashPredicate {
    inline std::size_t operator()(const TupleLight* v) const {
        std::size_t pred = reinterpret_cast<size_t>(v->getPredicateName());
        std::size_t seed=pred;
        int size =v->size();
        bool even = size%2==1;
        int start= even ? 1 : 0;
        if(even)
            seed ^= v->at(0) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        for (int i=start; i < size-1; i+=2) {
            seed ^= ((std::size_t)v->at(i)) + (((std::size_t)v->at(i+1))<<32) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed<<predbits | (~0UL >>(64-predbits) & pred);
    }
};

struct TuplePointerEq {
   bool operator()(const TupleLight *val1, const TupleLight* val2) const{
      return *val1 == *val2;
   }
};
template<class T>
void testReferenceHash(int threshold,const std::vector<const string*>& preds){
    std::vector<TupleLight> storage;
    std::unordered_set<TupleLight*,T,TuplePointerEq> tupleToInternalVar;
    int id=0;
    int HALF_MAX = INT_MAX/2;
    storage.reserve(threshold*threshold*2);
    for(int i=0;i<threshold;i++){
        for(int j=0;j<2*threshold;j++){
            TupleLight t({HALF_MAX+i,HALF_MAX+j},preds[id%preds.size()]);
            storage.push_back(t);
            tupleToInternalVar.insert(&storage.back());
            id++;
        }  
    }

            std::cout << "STATS FACTORY Bucket count: "<<tupleToInternalVar.bucket_count() << std::endl;
            std::cout << "STATS FACTORY Total Tuple Count: "<<tupleToInternalVar.size() << std::endl;
            std::vector<int> buckets;
            buckets.resize(tupleToInternalVar.bucket_count());
            for(TupleLight* t : tupleToInternalVar){
                buckets[tupleToInternalVar.bucket(t)]++;
            }
            int sum=0;
            float count=0;
            int min=0;
            int min_bucket=0;
            int max=0;
            int max_bucket=0;
            for(int i=0; i<tupleToInternalVar.bucket_count(); i++){
                if(buckets[i] > 0){
                    sum+=buckets[i];
                    count++;
                    if(buckets[i]<min || min==0){
                        min=buckets[i];
                        min_bucket=i;
                    }
                    if(buckets[i]>max){
                        max=buckets[i];
                        max_bucket=i;
                    }
                }
            }
            int avg=sum/count;
            int avg_bucket=0;
            for(int i=0; i<tupleToInternalVar.bucket_count(); i++){
                if(buckets[i] > avg - 5 && buckets[i] < avg + 5){
                    avg_bucket=i;
                    break;
                }
            }
            // std::cout << "Min Bucket: "<<min_bucket<<std::endl;
            // for(TupleLight* t : tupleToInternalVar){
            //     if(tupleToInternalVar.bucket(t) == min_bucket)
            //         t->print();
            // }
            std::cout << "Avg Bucket: "<<avg_bucket<<" "<<buckets[avg_bucket]<<std::endl;
            std::cout << "STATS FACTORY Not Empty buckets count: "<< count <<std::endl;
            std::cout << "STATS FACTORY Empty buckets percentage: "<<100-(100*(count/tupleToInternalVar.bucket_count()))<<std::endl;
            std::cout << "STATS FACTORY Min load for non empty buckets: "<<min<<std::endl;
            std::cout << "STATS FACTORY Average load for non empty buckets: "<<avg<<std::endl;
            std::cout << "STATS FACTORY Max load for non empty buckets: "<<max<<std::endl<<std::endl;

}
#include <stack>

int mainBucketAnalysis(){
    const std::string a="a";
    TupleLight t({1,2},&a);
    TupleLight* v = &t;
    std::size_t pred = reinterpret_cast<size_t>(v->getPredicateName());
    std::size_t seed=0;
    int size =v->size();
    bool even = size%2==1;
    int start= even ? 1 : 0;
    if(even)
        seed ^= v->at(0) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    for (int i=start; i < size-1; i++) {
        seed ^= ((std::size_t)v->at(i)) + (((std::size_t)v->at(i+1))<<32) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    }
    std::cout << 100-(100*23708167/49969847)<<std::endl;
    std::bitset<64> hash =seed;
    std::bitset<64> predinfo =pred;
    std::bitset<64> mask =0;
    std::cout << "Hash:                  " << hash <<std::endl; 
    std::cout << "Significant hash:      " << (hash << predbits) <<std::endl; 
    std::cout << "Predicate address:     " << predinfo <<std::endl; 
    std::cout << "Significant Predicate: " << ((~mask >> (64-predbits)) & predinfo) <<std::endl;
    std::cout << "Result:                " << ((hash << predbits) | ((~mask >> (64-predbits)) & predinfo)) <<std::endl; 
    std::bitset<64> result = ((hash << predbits) | ((~mask >> (64-predbits)) & predinfo));
    std::cout << result.to_ulong() << std::endl;
    TuplePointerHashPredicate h;
    std::cout << h(v) << std::endl;
    const std::string _a="a";
    const std::string _b="b";
    const std::string _c="c";
    const std::string _d="d";
    const std::string _e="e";
    std::vector<const std::string*> preds;
    preds.push_back(&_a);
    preds.push_back(&_b);
    preds.push_back(&_c);
    preds.push_back(&_d);
    preds.push_back(&_e);

    for(int threshold=1000;threshold<5000;threshold+=1000){
        testReferenceHash<TuplePointerHash>(threshold,preds);
        testReferenceHash<TuplePointerHashPair>(threshold,preds);
        testReferenceHash<TuplePointerHashPredicate>(threshold,preds);
    }
    return 0;
}
#include "../src/lp2cpp/datastructures/TupleFactoryTrie.h"
#include "../src/lp2cpp/datastructures/TupleLight.h"
#include <cstdlib>
int main(){
    const string a="a";
    const string b="b";
    const string c="c";
    std::vector<const string*> preds({&a,&b,&c});
    TupleFactoryTrie factory;
    std::vector<TupleLight> storage;
    for(int i=0; i<10;i++){
        int size = (i%preds.size())+2;
        std::vector<int> terms;
        for(int j=0;j<size;j++){
            terms.push_back(rand());
        }
        factory.addNewInternalTuple(terms,preds[i%preds.size()]);
        TupleLight t(terms,preds[i%preds.size()]);
        std::cout << i <<" " << t.toString() <<std::endl;
        storage.push_back(t);
    }

    TupleLight* findById = factory.getTupleFromInternalID(7);
    std::cout << findById->getId() <<" " << findById->toString() <<std::endl;

    int id =rand()%storage.size();
    if(id==0) id++;
    TupleLight* findByValue = factory.find(storage[id]);
    std::cout << storage[id].toString() << " " << findByValue->toString()<<std::endl;
    
    TupleLight* findByValue2 = factory.find(TupleLight({1804289383,2},&a));
    if(findByValue2 == NULL) 
    std::cout << "a(1804289383,2) not found"<<std::endl;
    const string d="d";

    TupleLight* findByValue3 = factory.find(TupleLight({1804289383,2},&d));
    if(findByValue3 == NULL) 
    std::cout << "d(1804289383,2) not found"<<std::endl;
    
}
