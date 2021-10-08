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
#ifndef DYNAMIC_COMPILATION_VECTOR_H
#define DYNAMIC_COMPILATION_VECTOR_H

#include <vector>
using namespace std;

class DynamicCompilationVector {

    public:
        DynamicCompilationVector(vector<int>& tmp,unsigned int i) { id=i;v.swap(tmp); }
        
        int& operator[](unsigned int id) { return v[id]; }
        int operator[](unsigned int id) const { return v[id]; }        
        unsigned int size() { return v.size(); }
        
        DynamicCompilationVector(const DynamicCompilationVector&) = delete;
        DynamicCompilationVector& operator=(const DynamicCompilationVector&) = delete;
        
        vector<int>::iterator begin() { return v.begin(); }
        vector<int>::const_iterator begin() const { return v.begin(); }
        
        vector<int>::iterator end() { return v.end(); }
        vector<int>::const_iterator end() const { return v.end(); }
        
        void push_back(int n) { v.push_back(n); } 

        int at(unsigned int id) const { return operator[](id); }        
        unsigned getId()const{return id;}

    private:
        unsigned id;
        vector<int> v;
};

#endif