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

/* 
 * File:   ExecutionManager.h
 * Author: bernardo
 *
 * Created on March 1, 2016, 2:43 PM
 */

#ifndef EXECUTIONMANAGER_H
#define EXECUTIONMANAGER_H

#include "language/Program.h"
#include <map>
#include "datastructures/AuxiliaryMap.h"
#include <iostream>
#include "Executor.h"
#include "../Reason.h"


class ExecutionManager : public Reason {
public:
    ExecutionManager();
    ~ExecutionManager();
    void compileDynamicLibrary(const std::string & executablePath, bool fileHasChanged);
    void parseFactsAndExecute(const char *filename);
    void launchExecutorOnFile(const char *filename);
    const std::vector<std::vector<aspc::Literal> > & getFailedConstraints();
    void executeProgramOnFacts(const std::vector<aspc::Literal*> & facts);
    void executeProgramOnFacts(const std::vector<int> & facts,std::vector<int>& propagatedLiterals);
    void initPropagator(const std::vector<int> & facts);
    const aspc::Executor & getExecutor();
    void shuffleFailedConstraints();
    void onLiteralTrue(const aspc::Literal* l);
    void onLiteralUndef(const aspc::Literal* l);
    void onLiteralTrue(int var);
    void onLiteralTrue(int var,const std::string& literalString);

    void onLiteralUndef(int var);
    void notifyStartingSolver()const{executor->undefLiteralsReceived();}
    void addedVarName(int var, const std::string & literalString);
    void callGenerator(){executor->undefLiteralsReceived();}
    const std::unordered_map<int, std::vector<int> > & getPropagatedLiteralsAndReasons() const;
    // const std::vector<int> & getPropagatedLiterals() const;
    // std::vector<int> & getPropagatedLiteralsAndClear();
    std::unordered_set<int> & getRemainingLiterals();
    void initCompiled();
    void simplifyAtLevelZero(std::vector<int>& output);
    void clearPropagations();
    bool postponedReason()const{return true;}
    void unRollToLevel(int decisionLevel){executor->unRollToLevel(decisionLevel);}
    void undefReceived(){executor->undefLiteralsReceived();}
    string printInternalLiterals(){ return executor->printInternalLiterals();}
    void printStatus(){executor->printStatus();}
    void checkUnfoundedSet(std::vector<int>& literalToPropagate){executor->checkUnfoundedSets(literalToPropagate,executor);}
    Reason* getPostponedeReason(Literal lit);
    virtual void onLearning( const Solver& solver, Learning* strategy, Literal lit );
    virtual bool onNavigatingLiteralForAllMarked( const Solver& solver, Learning* strategy, Literal lit );
    virtual bool isLearned() const { return false; }
    virtual ostream& print( ostream& o ) const;
    virtual void onNavigatingForUnsatCore( const Solver& solver, vector< unsigned int >& visited, unsigned int numberOfCalls, Literal lit );
    void setSolver(const Solver* s){executor->setSolver(s);}
    void setMinConflict(unsigned minConflict){executor->setMinConflict(minConflict);}
    void setMinHeapSize(unsigned minHeapSize){executor->setMinHeapSize(minHeapSize);}
    void setMaxHeapSize(unsigned maxHeapSize){executor->setMaxHeapSize(maxHeapSize);}
    void computeHeapSize(){executor->computeHeapSize();}
private:
    aspc::Executor* executor;
    void (*destroy)(aspc::Executor*);
};

#endif /* EXECUTIONMANAGER_H */

