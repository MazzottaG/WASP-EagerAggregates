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

    TupleLight() : predicateName(NULL),waspID(0),id(-INT_MAX),size_(0),content(NULL),status(UNKNOWN) {
    }

    TupleLight(const std::string* predicateName, bool negated = false, int waspID = 0) : predicateName(predicateName), negated(negated), waspID(waspID),id(-INT_MAX),size_(0),content(NULL),status(UNKNOWN) {
    }
    TupleLight(const std::string* predicateName,std::vector<int> v, bool negated = false, int waspID = 0) : predicateName(predicateName),/*std::vector<int>(v),*/ negated(negated), waspID(waspID),id(-INT_MAX),size_(v.size()),status(UNKNOWN) {
        content = new int[v.size()];
        std::copy(v.begin(), v.end(), content);
    }
    
    TupleLight(const TupleLight& orig) : size_(orig.size()), /*std::vector<int>(orig),*/ predicateName(orig.predicateName), negated(orig.negated), id(orig.id), waspID(orig.waspID),status(orig.status) {
        content = new int[orig.size_];
        for(int i=0;i<orig.size_;i++){
            content[i]=orig.content[i];
        }
    }

    virtual ~TupleLight() {
        delete [] content;
    }

    TupleLight(const std::initializer_list<int> & l, bool negated = false, int waspID = 0) :
    /*std::vector<int>(l),*/ size_(l.size()), predicateName(NULL), negated(negated), waspID(waspID),id(-INT_MAX),status(UNKNOWN) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    TupleLight(const std::initializer_list<int> & l, const std::string * predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), predicateName(predicateName), negated(negated), waspID(waspID),id(-INT_MAX),status(UNKNOWN) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }
    
    TupleLight(const std::vector<int> & l, const std::string * predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), predicateName(predicateName), negated(negated), waspID(waspID),id(-INT_MAX),status(UNKNOWN) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    //WARNING: require l to be created on the fly new int[]{...}
    TupleLight(int* l, int size, const std::string * predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(size), predicateName(predicateName), negated(negated), waspID(waspID),id(-INT_MAX),status(UNKNOWN){
        content = l;
    }
    TupleLight(const std::vector<int> & l, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), negated(negated), waspID(waspID),id(-INT_MAX),status(UNKNOWN) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    const std::string* getPredicateName() const {
        return predicateName;
    }
    int size()const {return size_;}
    void setSize(int s){size_=s;}

    bool isNegated() const {
        return negated;
    }

    void setNegated(bool negated) {
        this->negated = negated;
    }

    int getId() const {
        return id;
    }

    void setId(int id) const {
        this->id = id;
    }

    void setCollisionListIndex(std::vector<const TupleLight *>* collisionList, unsigned index) const {
        collisionsLists[collisionList] = index;
        
    }

    void removeFromCollisionsLists() const {
        for (auto & collisionListAndIndex : collisionsLists) {
            std::vector<const TupleLight *> & collisionList = *(collisionListAndIndex.first);
            unsigned index = collisionListAndIndex.second;
            collisionList[index] = collisionList[collisionList.size() - 1];
            collisionList[index]->setCollisionListIndex(&collisionList, index);
            collisionList.pop_back();
        }
        collisionsLists.clear();
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
        negated = right.negated;

        size_=right.size_;
        if(content!=NULL)
            delete [] content;
        content = new int[right.size_];
        memcpy ( content, right.content, size_ );
        return *this;
    }

    std::string toString()const{
        std::string tuple2String="";
        if (negated) {
            tuple2String+= "-";
        }
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
        if (negated) {
            std::cout << "-";
        }
        std::cout << *predicateName << "(";
        for (unsigned i = 0; i < size_; i++) {
            if (i > 0) {
                std::cout << ",";
            }
            std::cout << operator[](i);
        }
        std::cout << ")";
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
        removeFromCollisionsLists();
        return std::make_pair(this, true);
    }

private:
    const std::string * predicateName;
    bool negated; //cadidate to remove
    TruthStatus status;
    int waspID;
    mutable int id;
    int* content;
    int size_;
    mutable std::unordered_map<std::vector<const TupleLight *>*, unsigned> collisionsLists;
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



#endif /* TUPLE_H */

