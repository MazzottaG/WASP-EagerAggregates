/*
 *
 *  Copyright 2016 Bernardo Cuteri, Alessandro De Rosis, Francesco Ricca.
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

#ifndef __EXECUTOR_H__
#define __EXECUTOR_H__

#include <unordered_set>
#include <unordered_map>
#include <list>
#include <vector>
#include "language/Literal.h"
#include "datastructures/AuxiliaryMap.h"
#include "datastructures/PostponedReasons.h"
#include "../stl/UnorderedSet.h"
#include "../Solver.h"
#include <iostream>
#include <algorithm>


namespace aspc {

    struct PropComparator{
        const Solver* solver_;
        bool cmp(int &a, int &b){
            if(solver_->getActivityForLiteral(a)>solver_->getActivityForLiteral(b)){
                return true;
            }
            return false;
        }
        bool operator()(int& a,int& b){
            return cmp(a,b);
        }
        
    };
    struct LiteralHash {

        size_t operator()(const aspc::Literal & v) const {
            std::hash<unsigned> hasher;
            size_t seed = 0;
            for (unsigned i : v.getAtom().getIntTuple()) {
                seed ^= hasher(i) + (seed << 6) + (seed >> 2);
            }
            return (std::hash<std::string>()(v.getPredicateName())) ^ seed;
        }
    };
    class Executor {
    public:
        Executor();
        virtual ~Executor();
        virtual void undefLiteralsReceived()const;
        virtual void executeProgramOnFacts(const std::vector<aspc::Literal*> & facts);
        virtual void executeProgramOnFacts(const std::vector<int> & facts);
        virtual void onLiteralTrue(const aspc::Literal* l);
        virtual void onLiteralTrue(int var);
        virtual void onLiteralTrue(int var, const std::string&);
        virtual void onLiteralUndef(const aspc::Literal* l);
        virtual void onLiteralUndef(int var);
        virtual void addedVarName(int var, const std::string & atom);
        virtual void executeFromFile(const char* factsFile);
        virtual void init();
        virtual void clear();
        virtual void clearPropagations();
        virtual void explainAggrLiteral(int,UnorderedSet<int>&);
        virtual int explainExternalLiteral(int,UnorderedSet<int>&,std::unordered_set<int>&,bool=false);
        virtual void handleConflict(int);
        virtual void unRollToLevel(int);
        virtual void printInternalLiterals();
        virtual const std::vector<std::vector<aspc::Literal> > & getFailedConstraints() {
            return failedConstraints;
        }

        virtual const std::vector<std::string> & getBodyLiterals() {
            return bodyLiterals;
        }

        virtual void shuffleFailedConstraints() {
            std::random_shuffle(failedConstraints.begin(), failedConstraints.end());
        }
        virtual std::vector<int> & getPropagatedLiteralsAndClear(){   
            return propagatedLiterals;
        }
        virtual std::unordered_set<int> & getRemainingLiterals(){
            
            return remainingPropagatingLiterals;
        }
        virtual const std::unordered_map<int, std::vector<int> > & getPropagatedLiteralsAndReasons() const {
            return propagatedLiteralsAndReasons;
        }

        virtual const std::vector<int> & getPropagatedLiterals() const {
            return propagatedLiterals;
        }
        const UnorderedSet<int>& getConflictReason()const {return conflictReason;}
        void clearConflictReason(){conflictReason.clear();}
        void setSolver(const Solver* solver){
            this->solver = solver;
            propComparison.solver_=solver;
        }
        
    private:
        std::vector<std::vector<aspc::Literal> > failedConstraints;
        std::unordered_map<int, std::vector<int> > propagatedLiteralsAndReasons;
        std::vector<int> propagatedLiterals;
        std::unordered_set<int> remainingPropagatingLiterals;
        PostponedReasons reasonMapping;
        UnorderedSet<int> conflictReason;
        const Solver* solver;
        PropComparator propComparison;
        //std::unordered_map<aspc::Literal, std::vector<aspc::Literal>, LiteralHash> propagatedLiteralsAndReasons;
        std::vector<std::string> bodyLiterals;
        
    };
}
#endif
