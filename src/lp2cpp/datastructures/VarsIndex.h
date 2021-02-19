#ifndef VARSINDEX_H
#define VARSINDEX_H
#include "DynamicCompilationVector.h"

class VarsIndex{

    public:
        VarsIndex(){
            v=-1;
            index=nullptr;
        }
        ~VarsIndex(){

        }
        VarsIndex(int vv,DynamicCompilationVector* iindex){
            setV(vv);
            setIndex(iindex);
        }
        void setV(int vv){this->v=vv;}
        void setIndex(DynamicCompilationVector* iindex){this->index=iindex;}
        int getV()const{return v;}
        DynamicCompilationVector* getIndex()const{return index;}
        inline bool operator==(const VarsIndex& other){ 
            return getV() == other.getV() && getIndex()==other.getIndex();
        }
        friend bool operator< (const VarsIndex& a, const VarsIndex& b){
            return (a.getV() < b.getV()) || (a.getV()==b.getV() && a.getIndex()!=b.getIndex());
        }
    private:
        int v;
        DynamicCompilationVector* index;
    
};
#endif