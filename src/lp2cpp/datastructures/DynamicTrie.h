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
#ifndef DYNAMIC_TRIE_H
#define DYNAMIC_TRIE_H

#include <cassert>
#include <climits>
#include <unordered_map>
#include <vector>
#include "DynamicCompilationVector.h"
using namespace std;

class DynamicTrie {
    public:

        DynamicTrie() { root = new Node(INT_MAX); }
        ~DynamicTrie() { if(root) clear(); }
        void clear() { delete root; root = nullptr; }
        inline DynamicCompilationVector* addElements(vector<int>& v) {
            Node* current = root;
            for(unsigned int i = 0; i < v.size(); i++) {
                current = current->add(v[i]);
            }
            return current->setLeaf(v,data);
        }
        
        DynamicCompilationVector* get(unsigned int id)const{
            assert(id<data.size());
            return data[id];
        }
        unsigned int size()const {return data.size();}
        inline void removeElements(const vector<int>& v) {
            Node* current = root;
            for(unsigned int i = 0; i < v.size(); i++) {
                current = current->add(v[i]);
            }
            return current->removeLeaf();
        }
            
    private:        
        class Node {

            public:
                inline Node(int content_for_node) : content(content_for_node), dynamic(nullptr) {}
                ~Node() {
                    delete dynamic;
                    for(auto it = childrenMap.begin(); it != childrenMap.end(); ++it) delete it->second;                    
                }
                inline int getContent() const { return content; }
                inline DynamicCompilationVector* setLeaf(vector<int>& v,vector<DynamicCompilationVector*>& data) {
                    if(dynamic == nullptr) {
                        dynamic = new DynamicCompilationVector(v,data.size());
                        data.push_back(dynamic);}
                    return dynamic;
                }
                inline void removeLeaf() { delete dynamic; dynamic = nullptr; }    
                inline Node* add(int c) {
                    if (childrenMap.find(c) == childrenMap.end()) childrenMap[c] = new Node(c);            
                    return childrenMap[c];
                }
        
            private:
                int content;
                DynamicCompilationVector* dynamic;
                unordered_map<int, Node*> childrenMap;        
        };        
        Node* root;        
        std::vector<DynamicCompilationVector*> data;
};

#endif
