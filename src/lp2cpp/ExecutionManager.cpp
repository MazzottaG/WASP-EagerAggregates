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
 * File:   ExecutionManager.cpp
 * Author: bernardo
 * 
 * Created on March 1, 2016, 2:43 PM
 */

#include "ExecutionManager.h"
#include "DLV2libs/input/InputDirector.h"
#include "parsing/AspCore2InstanceBuilder.h"
#include "Executor.h"
#include <dlfcn.h>
#include <stdlib.h>
#include "language/Program.h"
#include "utils/FilesManagement.h"
#include <cassert>
#include "../Literal.h"
#include "../Clause.h"
#include "../Solver.h"
#include "../stl/UnorderedSet.h"

using namespace std;

ExecutionManager::ExecutionManager() {
}

ExecutionManager::~ExecutionManager() {
// #ifndef LP2CPP_DEBUG
//     if (executor)
//         destroy(executor);
//     // delete executor;
// #else 
//     delete executor;
// #endif
#ifndef STATIC_COMPILE
    if (executor)
        destroy(executor);
#else 
    delete executor;
#endif
}

void ExecutionManager::launchExecutorOnFile(const char *filename) {
    executor->executeFromFile(filename);
    //print failed constraints
    if (!executor->getFailedConstraints().empty()) {
        cout << "failed constraints:" << endl;
    }
    for (unsigned i = 0; i < executor->getFailedConstraints().size(); i++) {
        for (unsigned j = 0; j < executor->getFailedConstraints()[i].size(); j++) {
            executor->getFailedConstraints()[i][j].print();
            cout << " ";
        }
        cout << "\n";
    }
}
void ExecutionManager::onLearning( const Solver& solver, Learning* strategy, Literal lit ){
    // std::cout << "onLearning" << lit.getId() <<std::endl;
    
    UnorderedSet<int> reason;
    // executor->explainAggrLiteral(lit.getOppositeLiteral().getId(),reason);
    executor->explainExternalLiteral(lit.getOppositeLiteral().getId(),reason);
    // sort(reason.begin(),reason.end());
    // auto it = unique(reason.begin(),reason.end());
    // reason.resize(distance(reason.begin(),it));

    for(int i=0;i<reason.size();i++){
        Literal l = Literal::createLiteralFromInt(-reason[i]);
        if(solver.getDecisionLevel(l) > 0){
            strategy->onNavigatingLiteral( l );
        }
    }
}
Reason* ExecutionManager::getPostponedeReason(Literal lit){
    if(lit == Literal::null){
        return this;
    }
    if(lit.getVariable()==1){
        const UnorderedSet<int>* conflictReason = &executor->getConflictReason();
        Clause* clause = new Clause();
        clause->addLiteral(Literal::null);
        for(int i=0;i<conflictReason->size();i++){
            clause->addLiteral(Literal::createLiteralFromInt(-conflictReason->at(i)));
        }
        executor->clearConflictReason();
        return clause;
    }

    UnorderedSet<int> reason;
    // executor->explainAggrLiteral(lit.getId(),reason);
    executor->explainExternalLiteral(lit.getId(),reason);
    // sort(reason.begin(),reason.end());
    // auto it = unique(reason.begin(),reason.end());
    // reason.resize(distance(reason.begin(),it));

    Clause* clause = new Clause();
    clause->addLiteral(Literal::null);
    for(int i=0;i<reason.size();i++){
        clause->addLiteral(Literal::createLiteralFromInt(-reason[i]));
    }

    return clause;

}
bool ExecutionManager::onNavigatingLiteralForAllMarked( const Solver& solver, Learning* strategy, Literal lit ) {
    // std::cout << "onNavigatingLiteralForAllMarked Execution Manager" <<std::endl;

    UnorderedSet<int> reas ;
    // executor->explainAggrLiteral(lit.getOppositeLiteral().getId(),reas);
    executor->explainExternalLiteral(lit.getOppositeLiteral().getId(),reas);
    // for(int i=0;i<reas.size();i++){
    //     Literal l = Literal::createLiteralFromInt(-reas[i]);
    //     std::cout<<"Reas: "<<l<<" For lit: "<<lit<<std::endl;
    // }
    for(int i=0;i<reas.size();i++){
    
        Literal l = Literal::createLiteralFromInt(-reas[i]);
        // std::cout<<"Nav: "<<l<<" For lit: "<<lit<<std::endl;
        if( !strategy->onNavigatingLiteralForAllMarked( l ) )
            return false;
    }
    return true;
}
ostream& ExecutionManager::print( ostream& out ) const{
    out << "Executor Manager" ;
    return out ;
}
void ExecutionManager::onNavigatingForUnsatCore( const Solver& solver, vector< unsigned int >& visited, unsigned int numberOfCalls, Literal lit ){
    // std::cout << "onNavigatingForUnsatCore" <<std::endl;
    
    UnorderedSet<int> reas ;
    // executor->explainAggrLiteral(lit.getOppositeLiteral().getId(),reas);
    executor->explainExternalLiteral(lit.getOppositeLiteral().getId(),reas);
    
    for(int i=0;i<reas.size();i++){
        Var v = reas[i]>0 ? reas[i] : -reas[i];
        if( solver.getDecisionLevel( v ) > 0 )
            visited[ v ] = numberOfCalls;
    }
}
void ExecutionManager::parseFactsAndExecute(const char *filename) {
    DLV2::InputDirector director;
    AspCore2InstanceBuilder* builder = new AspCore2InstanceBuilder();
    director.configureBuilder(builder);
    vector<const char*> fileNames;
    fileNames.push_back(filename);
    director.parse(fileNames);
    executeProgramOnFacts(builder->getProblemInstance());
    delete builder;

}

#ifndef LP2CPP_DEBUG

void ExecutionManager::compileDynamicLibrary(const string & executablePath, bool fileHasChanged) {


    string executorFile = executablePath + "/Executor.so";
    FilesManagement fileManagement;
    //if(false){

    if (fileHasChanged || !fileManagement.exists(executorFile)) {
        string command = "cd " + executablePath + " && make -f DynamicLibraryMake -s";
        cout<<command<<endl;
        int commandReturn = system(command.c_str());
        if (commandReturn) {
            throw std::runtime_error("Failed to execute command " + command);
        }
    }

    void* handle = dlopen(executorFile.c_str(), RTLD_LAZY);
    if (!handle) {
        fprintf(stderr, "%s\n", dlerror());
        exit(EXIT_FAILURE);
    }
    #ifndef STATIC_COMPILE
        aspc::Executor * (*create)();


        create = (aspc::Executor * (*)())dlsym(handle, "create_object");

        destroy = (void (*)(aspc::Executor*))dlsym(handle, "destroy_object");

        executor = (aspc::Executor*) create();
    #else
        executor = new aspc::Executor();
    #endif
}
#else 

void ExecutionManager::compileDynamicLibrary(const string &, bool) {
    executor = new aspc::Executor();
}
#endif

void ExecutionManager::executeProgramOnFacts(const std::vector<aspc::Literal*> & facts) {
    executor->executeProgramOnFacts(facts);

}
void ExecutionManager::initPropagator(const std::vector<int> & facts) {
    if(executor) {
        executor->initPropagator(facts);
    }
}
void ExecutionManager::executeProgramOnFacts(const std::vector<int> & facts,std::vector<int>& propagatedLiterals) {
    
    if(executor) {
        executor->executeProgramOnFacts(facts,propagatedLiterals);
    }

}

const std::vector<std::vector<aspc::Literal> > & ExecutionManager::getFailedConstraints() {
    return executor->getFailedConstraints();
}

const aspc::Executor & ExecutionManager::getExecutor() {
    return *executor;
}

void ExecutionManager::shuffleFailedConstraints() {
    executor-> shuffleFailedConstraints();

}
void ExecutionManager::onLiteralTrue(int var,const std::string& literalString) {
    executor->onLiteralTrue(var,literalString);
}

void ExecutionManager::onLiteralTrue(int var) {
    executor->onLiteralTrue(var);
}

void ExecutionManager::onLiteralUndef(int var) {
    executor->onLiteralUndef(var);
}


void ExecutionManager::onLiteralTrue(const aspc::Literal* l) {
    executor->onLiteralTrue(l);
}

void ExecutionManager::onLiteralUndef(const aspc::Literal* l) {
    executor->onLiteralUndef(l);
}

const std::unordered_map<int, std::vector<int> > & ExecutionManager::getPropagatedLiteralsAndReasons() const {

    return executor->getPropagatedLiteralsAndReasons();
}

// const std::vector<int> & ExecutionManager::getPropagatedLiterals() const {

//     return executor->getPropagatedLiterals();
// }
// std::vector<int> & ExecutionManager::getPropagatedLiteralsAndClear() {

//     return executor->getPropagatedLiteralsAndClear();
// }

std::unordered_set<int> & ExecutionManager::getRemainingLiterals() {

    return executor->getRemainingLiterals();
}
void ExecutionManager::initCompiled() {
    executor->init();
}

void ExecutionManager::addedVarName(int var, const std::string& literalString) {
    executor->addedVarName(var, literalString);
}


void ExecutionManager::simplifyAtLevelZero(std::vector<int>& output) {
// #ifdef EAGER_DEBUG
//     std::cout<<"simplifyAtLevelZero"<<endl;
// #endif
//     if(!executor) {
//         //no constraints and no variables
//         return;
//     }
//     for(auto & e: executor->getPropagatedLiteralsAndReasons()) {
// #ifdef EAGER_DEBUG
//         std::cout<<"derived at level 0 "<<-e.first<<endl;
// #endif
//         output.push_back(-e.first);
//     }
//     for(unsigned int i=0;i<executor->getPropagatedLiterals().size();i++) {
// #ifdef EAGER_DEBUG
//         std::cout<<"derived at level 0 "<<-e.first<<endl;
// #endif
//         output.push_back(-executor->getPropagatedLiterals()[i]);
//     }
    
}

void ExecutionManager::clearPropagations() {
    executor->clearPropagations();
}
