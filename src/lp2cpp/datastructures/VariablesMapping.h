#ifndef VARIABLESMAPPING_H
#define VARIABLESMAPPING_H
#include <vector>
#include <map>
#include <cmath>
#include <sstream>

class VariablesMapping: public std::map<std::vector<int> ,int> {
    
    public:
        VariablesMapping(){
            count=-1;
        }
        void insert(const std::vector<int>& k){
            // std::string s=vecToString(k);
            if(this->find(k)==this->end()){
                this->operator[](k)=++count;
            }
        }
        
        int getId(const std::vector<int>& k){
            // std::string s=vecToString(k);
            if(this->find(k)==this->end()){
                insert(k);
            }
            return this->operator[](k);
            
        }

        bool hasKey(const std::vector<int>& k){
            // std::string s=vecToString(k);
            return this->find(k)!=this->end();
        }

        static std::vector<int>* getVecFromKey(const std::string & s){
            std::istringstream ss(s);
            std::vector<int>* v =new std::vector<int>();
            std::string val;
            while (std::getline(ss, val, ';')) {
                v->push_back(std::stoi(val));
            }
            return v;
        }
        
    private:
        std::string vecToString(const std::vector<int>& v){
            std::string s;
            for(int i=0;i<v.size();i++){
                if(i>0)
                    s+=";";
                s+=std::to_string(v[i]);
            }
            return s;
        }
        // void insert(const std::string& s){
        //     this->operator[](s)=++count;
        // }
        int count;
};
#endif /* AUXILIARYMAP_H */

