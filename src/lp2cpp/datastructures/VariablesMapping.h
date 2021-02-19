#ifndef VARIABLESMAPPING_H
#define VARIABLESMAPPING_H
#include <vector>
#include <unordered_map>
#include <cmath>
#include <sstream>
#include <cassert>

struct VectorsHash {

    inline std::size_t operator()(const std::vector<int> & v) const {
        std::size_t seed = 0;
        for (int i : v) {
            seed ^= i + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }

};

class VariablesMapping: public std::unordered_map<std::vector<int> ,int,VectorsHash> {
    
    public:
        VariablesMapping(){
        }
        void insert2(const std::vector<int>& k){
            // std::string s=vecToString(k);
            if(this->find(k)==this->end()){
                auto it = this->insert({k,data.size()});
                data.push_back(it.first);
            }
        }
        
        int getId(const std::vector<int>& k){
            // std::string s=vecToString(k);
            if(this->find(k)==this->end()){
                insert2(k);
            }
            return this->operator[](k);
            
        }

        const std::vector<int>& getKey(int v){
            assert(v<data.size());
            return data[v]->first;
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
        std::vector<unordered_map::iterator> data;
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

