/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   Tuple.h
 * Author: bernardo
 *
 * Created on April 9, 2018, 1:19 PM
 */

#ifndef TUPLELIGHT_H
#define TUPLELIGHT_H
#include <vector>
#include <string>
#include <cstring>
#include <unordered_set>
#include <unordered_map>
#include <iostream>
#include <climits>

enum TruthStatus {
    True = 0, False, Undef, UNKNOWN
};
class TupleLight {
public:

    TupleLight() : predicateName(NULL),waspID(0),id(-INT_MAX),size_(0),content(NULL),status(UNKNOWN),collisionsListsSize(0) {
    }

    TupleLight(const std::string* predicateName, bool negated = false, int waspID = 0) : predicateName(predicateName), waspID(waspID),id(-INT_MAX),size_(0),content(NULL),status(UNKNOWN),collisionsListsSize(0) {
    }
    TupleLight(const std::string* predicateName,std::vector<int> v, bool negated = false, int waspID = 0) : predicateName(predicateName),/*std::vector<int>(v),*/ waspID(waspID),id(-INT_MAX),size_(v.size()),status(UNKNOWN),collisionsListsSize(0) {
        content = new int[v.size()];
        std::copy(v.begin(), v.end(), content);
    }
    
    TupleLight(const TupleLight& orig) : size_(orig.size()), /*std::vector<int>(orig),*/ predicateName(orig.predicateName), id(orig.id), waspID(orig.waspID),status(orig.status),collisionsListsSize(orig.collisionsListsSize) {
        content = new int[orig.size_];
        std::memcpy(content,orig.content,orig.size_*sizeof(int));
    }

    virtual ~TupleLight() {
        if(content != NULL){
            delete [] content;
        }
    }

    TupleLight(const std::initializer_list<int> & l, bool negated = false, int waspID = 0) :
    /*std::vector<int>(l),*/ size_(l.size()), predicateName(NULL), waspID(waspID),id(-INT_MAX),status(UNKNOWN),collisionsListsSize(0) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    TupleLight(const std::initializer_list<int> & l, const std::string * predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), predicateName(predicateName), waspID(waspID),id(-INT_MAX),status(UNKNOWN),collisionsListsSize(0) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }
    
    TupleLight(const std::vector<int> & l, const std::string * predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), predicateName(predicateName), waspID(waspID),id(-INT_MAX),status(UNKNOWN),collisionsListsSize(0) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    //WARNING: require l to be created on the fly new int[]{...}
    TupleLight(int* l, int size, const std::string * predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(size), predicateName(predicateName), waspID(waspID),id(-INT_MAX),status(UNKNOWN),collisionsListsSize(0){
        content = l;
    }
    TupleLight(const std::vector<int> & l, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), waspID(waspID),id(-INT_MAX),status(UNKNOWN),collisionsListsSize(0) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }
    //WARNING use only with bufferedTuple in TupleFactory
    inline void setContent(int* vectorData,int size,const std::string* predName){
        content = vectorData;
        size_=size;
        predicateName=predName;
    }
    //WARNING use only with bufferedTuple in TupleFactory
    inline void clearContent(){
        content = NULL;
    }
    //WARNING use only with bufferedTuple in TupleFactory
    inline int* getContent()const{
        return content ;
    }
    
    const std::string* getPredicateName() const {
        return predicateName;
    }
    int size()const {return size_;}
    void setSize(int s){size_=s;}

    int getId() const {
        return id;
    }

    void setId(int id) const {
        this->id = id;
    }
    
    void setCollisionListIndex(std::vector<int>* collisionList, unsigned index,int internalIndex=-1)const {
        if(internalIndex>=0){
            if(collisionsLists[internalIndex].first!=collisionList){
                std::cout<<"Error in swaping position in collision list"<<std::endl;
                exit(180);
            }
            collisionsLists[internalIndex].second=index;
            return;
        }
        if(collisionsListsSize>=collisionsLists.size()){
            collisionsLists.push_back(std::pair<std::vector<int>*,unsigned>(collisionList,index));
            collisionsListsSize++;
            return;
        }
        collisionsLists[collisionsListsSize]=std::pair<std::vector<int>*,unsigned>(collisionList,index);
        collisionsListsSize++;
    }

    // void removeFromCollisionsLists(const TupleFactory& factory) const ;
    std::vector<std::pair<std::vector<int>*,unsigned>>& getCollisionsLists()const{return collisionsLists;}
    void clearCollisionsList(){
        collisionsListsSize=0;
    }
    int operator[](unsigned i)const{
        return content[i];
    }
    int at(unsigned i)const{
        return content[i];
    }

    int& operator[](unsigned i){
        return content[i];
    }
    int& at(unsigned i){
        return content[i];
    }
    
    bool operator==(const TupleLight& right) const {
        if (predicateName != right.predicateName || size_ != right.size_) {
            return false;
        }
        for (unsigned i = 0; i < size_; i++) {
            if (operator[](i) != right[i]) {
                return false;
            }
        }
        return true;
    }

    TupleLight& operator=(const TupleLight& right) {
        if (this == &right)
            return *this;
        predicateName = right.predicateName;
        collisionsLists = right.collisionsLists;
        id = right.id;

        size_=right.size_;
        if(content!=NULL)
            delete [] content;
        content = new int[right.size_];
        memcpy ( content, right.content, size_ );
        return *this;
    }

    std::string toString()const{
        std::string tuple2String="";
        tuple2String+= *predicateName + "(";
        for (unsigned i = 0; i < size_; i++) {
            if (i > 0) {
                tuple2String+= ",";
            }
            tuple2String+= std::to_string(operator[](i));
        }
        tuple2String+= ")";
        return tuple2String;
    }

    void print() const {
        std::cout << *predicateName << "(";
        for (unsigned i = 0; i < size_; i++) {
            if (i > 0) {
                std::cout << ",";
            }
            std::cout << operator[](i);
        }
        std::cout << ")" <<std::endl;
    }
    void printAsConstraint() const {
        std::string sign = status == True ? "not" : "";
        std::cout << ":-" << sign << " " <<*predicateName << "(";
        for (unsigned i = 0; i < size_; i++) {
            if (i > 0) {
                std::cout << ",";
            }
            std::cout << operator[](i);
        }
        std::cout << ")." <<std::endl;
    }
    int getWaspID()const{
        return waspID;
    }
    void setWaspID(int waspID){
        this->waspID=waspID;
    }
    bool isTrue()const{
        return status == True;
    }
    bool isFalse()const{
        return status == False;
    }
    bool isUndef()const{
        return status == Undef;
    }
    std::pair<const TupleLight *, bool>  setStatus(TruthStatus t){
        if(status==t){
            return std::make_pair(this, false);
        }
        status=t;
        // removeFromCollisionsLists(factory);
        return std::make_pair(this, true);
    }

private:
    const std::string * predicateName;
    TruthStatus status;
    int waspID;
    mutable int id;
    int* content;
    int size_;
    mutable unsigned collisionsListsSize;
    mutable std::vector<std::pair<std::vector<int>*,unsigned>> collisionsLists;
    // mutable std::unordered_map<std::vector<unsigned>*, unsigned> collisionsLists;
};

struct TupleLightHash {

    inline std::size_t operator()(const TupleLight & v) const {
        std::size_t seed = 0;
        for (int i=0; i < v.size(); i++) {
            seed ^= v[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};



#endif

