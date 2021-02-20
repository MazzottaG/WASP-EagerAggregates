#ifndef VARSINDEX_H
#define VARSINDEX_H
#include "DynamicCompilationVector.h"

class VarsIndex{

    public:
        VarsIndex(){
            v=-1;
            index=-1;

        }
        ~VarsIndex(){

        }
        VarsIndex(const VarsIndex& other ){

            setV(other.getV());
            setIndex(other.getIndex());
        }
        VarsIndex& operator=(const VarsIndex& other ){

            setV(other.getV());
            setIndex(other.getIndex());
            return *this;
        }
        VarsIndex(int vv,unsigned int iindex){
            setV(vv);
            setIndex(iindex);
        }
        void setV(int vv){this->v=vv;}

        void setIndex(unsigned int iindex){this->index=iindex;}

        int getV()const{return v;}
        
        unsigned int getIndex()const{return index;}
    
        inline bool operator==(const VarsIndex& b){ 
            return getV() == b.getV() && getIndex()==b.getIndex();
        }
        friend bool operator< (const VarsIndex& a, const VarsIndex& b){
            return (a.getV() < b.getV()) || (a.getV()==b.getV() && a.getIndex()<b.getIndex());
        }
        
        void print()const{
            std::cout<<"Var: "<<v;
            std::cout<<"Key: "<<index;
        }
    private:
        int v;
        unsigned int index;
        
    
};
#endif