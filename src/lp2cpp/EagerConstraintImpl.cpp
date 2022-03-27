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
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   EagerConstrainImpl.cpp
 * Author: bernardo
 * 
 * Created on March 27, 2019, 3:20 PM
 */

#include "EagerConstraintImpl.h"
#include <fstream>
#include "CompilationManager.h"
#include "ExecutionManager.h"
#include "language/Literal.h"
#include "../util/WaspOptions.h"
#include "utils/FilesManagement.h"
#include "../util/VariableNames.h"

#ifdef PRINT_EXEC_TIMES
#include <chrono>
using namespace std::chrono;
#endif

EagerConstraintImpl::EagerConstraintImpl() : compilationManager(EAGER_MODE) {
}

EagerConstraintImpl::~EagerConstraintImpl() {
    //for (auto & a : literals) {
    //delete a.second;
    //}
}

void EagerConstraintImpl::performCompilation() {
    
    string executablePathAndName = wasp::Options::arg0;
    string executablePath = executablePathAndName;
    for (int i = executablePath.size() - 1; i >= 0; i--) {
        if (executablePath[i] == '/') {
            executablePath = executablePath.substr(0, i);
            break;
        }
    }
    if(!wasp::Options::compilerDisabled){
        FilesManagement fileManagement;
        string executorPath = executablePath + "/src/lp2cpp/Executor.cpp";
        int fd = fileManagement.tryGetLock(executorPath);
        string hash = fileManagement.computeMD5(executorPath);
    #ifndef LP2CPP_DEBUG
        std::ofstream outfile(executorPath);
        compilationManager.setOutStream(&outfile);
        compilationManager.lp2cpp();
        outfile.close();
    #endif
        string newHash = fileManagement.computeMD5(executorPath) ;
        executionManager.compileDynamicLibrary(executablePath, newHash != hash);
        fileManagement.releaseLock(fd, executorPath);
        
    }else{
        executionManager.compileDynamicLibrary(executablePath, false);
    }
    compilationDone = true;
    executionManager.setSolver(solver);
    // unsigned minConflict = wasp::Options::eagerPropMinConflict != 0 ? wasp::Options::eagerPropMinConflict : defaultMinConflict;
    // unsigned minHeapSize = wasp::Options::eagerPropMinHeapSize != 0 ? wasp::Options::eagerPropMinHeapSize : defaultMinHeapSize;
    // unsigned maxHeapSize = wasp::Options::eagerPropMaxHeapSize != 0 ? wasp::Options::eagerPropMaxHeapSize : defaultMaxHeapSize; 
    executionManager.setMinConflict(defaultMinConflict);
    executionManager.setMinHeapSize(defaultMinHeapSize);
    executionManager.setMaxHeapSize(defaultMaxHeapSize);
    executionManager.computeHeapSize();
}

void EagerConstraintImpl::setFilename(const std::string & fileDirectory, const std::string & filename) {
    this-> fileDirectory = fileDirectory;
    this -> filename = filename;
    this -> filepath = filename;
    // this -> filepath = fileDirectory + "/" + filename;
    FilesManagement fileManagement;
    if (!fileManagement.exists(filepath)) {
        throw std::runtime_error("Failed to compile eager program: file " + filepath + " does not exist.");
    }
    compilationManager.loadProgram(filepath);

};

#ifdef PRINT_EXEC_TIMES
long prop_time_e = 0;
long solv_time_e = 0;

high_resolution_clock::time_point t1_e;
high_resolution_clock::time_point t2_e = high_resolution_clock::now();
#endif
void EagerConstraintImpl::endPropagation(std::vector<int>& literalToPropagate){
    executionManager.checkUnfoundedSet(literalToPropagate);
}
void EagerConstraintImpl::onAnswerSet(const std::vector<int>& answerSet){

    // std::unordered_map<int,string> watchedLiterals;
    for(unsigned i=0; i<answerSet.size();i++){
        if(answerSet[i]>0 && watchedAtomsSetNotCompletion.count(answerSet[i])!=0){
            executionManager.onLiteralTrue(answerSet[i],VariableNames::getName(Literal::createLiteralFromInt(answerSet[i]).getVariable()));
            // watchedLiterals[answerSet[i]]=VariableNames::getName(Literal::createLiteralFromInt(answerSet[i]).getVariable());
        }
    }
    std::string modelAsConstraint = executionManager.printInternalLiterals();
    #ifdef PRINTCONSTRAINT
        solver->printConstraints(modelAsConstraint);
    #endif
}
void EagerConstraintImpl::onLiteralTrue(int var, int decisionLevel, std::vector<int> & propagatedLiterals) {
    // std::cout<<"Onlittrue "<<var<<std::endl;

#ifdef PRINT_EXEC_TIMES
    t1_e = high_resolution_clock::now();
    auto solve_duration_e = duration_cast<microseconds>(t1_e - t2_e).count();
    solv_time_e += solve_duration_e;
    cout << "START eager evaluation" << endl;
#endif
#ifdef EAGER_DEBUG
    std::cout << "on literal true" << std::endl;
#endif
    
    /*
    aspc::Literal* lit = NULL;
    //std::cout << "lit true " << var << std::endl;
    if (var > 0 && literals.count(var)) {
        lit = literals[var];
        lit->setNegated(false);

    } else if (literals.count(-var)) {
        lit = literals[-var];
        lit->setNegated(true);
    }*/
    //std::cout << "lit true ";
    //lit->print();
    //std::cout << std::endl;
    //std::vector<aspc::Literal*> inputInterpretation;
    std::vector<int> inputInterpretation;
    inputInterpretation.push_back(decisionLevel);
    inputInterpretation.push_back(var);

#ifdef PRINT_EXEC_TIMES
    cout << "On literal true" << endl;
#endif    
    executionManager.executeProgramOnFacts(inputInterpretation,propagatedLiterals);
#ifdef PRINT_EXEC_TIMES
    cout << "Propagated: " << executionManager.getPropagatedLiteralsAndReasons().size() << endl;
#endif   
#ifdef PRINT_EXEC_TIMES
    cout << "END eager evaluation" << endl;
    t2_e = high_resolution_clock::now();
    auto duration_e = duration_cast<microseconds>(t2_e - t1_e).count();

    prop_time_e += duration_e;

    cout << "tot_propr " << prop_time_e / 1000 << endl;
    cout << "tot_solv " << solv_time_e / 1000 << endl;
#endif
    // std::cout<<"exit Onlittrue"<<std::endl;

};

void EagerConstraintImpl::onLiteralsUndefined(const std::vector<int> & params) {

#ifdef EAGER_DEBUG
    std::cout << "on literals undef at decision level" << params[0] << std::endl;
#endif
    //params[0] is the decision level
    for (unsigned i = 1; i < params.size(); i++) {
        //        int lit = params[i];
        executionManager.onLiteralUndef(params[i]);
        //        if (lit > 0) {
        //            executionManager.onLiteralUndef(literals[lit]);
        //        } else {
        //            executionManager.onLiteralUndef(literals[-lit]);
        //        }
    }
    executionManager.unRollToLevel(params[0]);
    // executionManager.undefReceived();
}

void EagerConstraintImpl::getReasonForLiteral(int lit, std::vector<int> & reason) {

    //std::cout << lit << "->";
    for (const auto& it : executionManager.getPropagatedLiteralsAndReasons().at(-lit)) {
        reason.push_back(-it);
        //std::cout << -it << " ";
    }
    //std::cout << std::endl;

}
//std::cout << "asking reason for " << lit << std::endl;
//    if (lit < 0) {
//        lit = -lit;
//    }
//    const std::unordered_map<aspc::Literal, std::vector<aspc::Literal>, LiteralHash> & propagatedLiteralsAndReasons = executionManager.getPropagatedLiteralsAndReasons();
//    for (const auto& it : propagatedLiteralsAndReasons.at(*(literals[lit]))) {
//        reason.push_back(-literalsMap[it]);
//    }




//TODO remove duplication

aspc::Literal parseLiteral2(const std::string & literalString) {
    string predicateName;
    unsigned i = 0;
    for (i = 0; i < literalString.size(); i++) {
        if (literalString[i] == '(') {
            predicateName = literalString.substr(0, i);
            break;
        }
        if (i == literalString.size() - 1) {
            predicateName = literalString.substr(0);
        }
    }
    aspc::Literal literal(predicateName);
    for (; i < literalString.size(); i++) {
        char c = literalString[i];
        if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
            int start = i;
            int openBrackets = 0;
            while ((c != ' ' && c != ',' && c != ')') || openBrackets > 0) {
                if (c == '(') {
                    openBrackets++;
                } else if (c == ')') {

                    openBrackets--;
                }
                i++;
                c = literalString[i];
            }
            literal.addTerm(literalString.substr(start, i - start));
        }
    }
    return literal;
}

void EagerConstraintImpl::addedVarName(int var, const std::string & literalString) {

#ifdef EAGER_DEBUG
    std::cout << "addedVarName " << var << " -> " << literalString << std::endl;
#endif

#ifdef GROUNDING
    std::cout << "Undefined literal: " << literalString << std::endl;
#endif

    if (!compilationDone) {
        performCompilation();
        executionManager.initCompiled();
    }

    int uVar=var>0 ? var : -var; 

    aspc::Literal atom = parseLiteral2(literalString);
    //this->literals[var] = atom;
    //literalsMap[*atom] = var;
    
    if (compilationManager.getBodyPredicates().count(atom.getPredicateName())) {
        executionManager.addedVarName(var, literalString);
    }
    
    if (compilationManager.getBodyPredicatesNotCompletion().count(atom.getPredicateName())) {
        watchedAtomsSetNotCompletion.insert(uVar);
        atomsToFreeze.push_back(uVar);
        
    }
    compilationManager.insertModelGeneratorPredicate(atom.getPredicateName());
    

    if (compilationManager.getBodyPredicates().count(atom.getPredicateName())) {
        if (facts.count(var)) {            
            executionManager.onLiteralTrue(var);
        } else {
            atomsToFreeze.push_back(uVar);
            watchedLiterals.push_back(var);
            watchedLiterals.push_back(-var);            
            executionManager.onLiteralUndef(var);
        }
        //std::cout<<"Watch "<<var<<" ";
        //atom.print();
        //std::cout<<std::endl;
        watchedLiteralsSet.insert(var);
        watchedLiteralsSet.insert(-var);
    }


}

void EagerConstraintImpl::simplifyAtLevelZero(std::vector<int>& output) {
    std::cout << "simplifyAtLevelZero" << std::endl;
    std::vector<int> inputInterpretation;
    inputInterpretation.push_back(-1);
    for(int fact:facts) {
        if(watchedLiteralsSet.find(fact)!=watchedLiteralsSet.end()) {            
            inputInterpretation.push_back(fact);
        }
    }
    executionManager.executeProgramOnFacts(inputInterpretation,output);
    // executionManager.simplifyAtLevelZero(output);
    //executionManager.clearPropagations();
    
}


void EagerConstraintImpl::onFact(int var) {
#ifdef EAGER_DEBUG
    std::cout << "onFact " << var << std::endl;
#endif

    facts.insert(var);

};

const std::vector<unsigned int> & EagerConstraintImpl::getVariablesToFreeze() {
    
    return atomsToFreeze;
};
const std::vector<int> & EagerConstraintImpl::getWatchedLiterals() {
    return watchedLiterals;
};

const string& EagerConstraintImpl::getFilepath() const {
    return filepath;
}