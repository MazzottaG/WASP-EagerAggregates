/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   EagerConstrainImpl.h
 * Author: bernardo
 *
 * Created on March 27, 2019, 3:20 PM
 */

#ifndef EAGERCONSTRAINIMPL_H
#define EAGERCONSTRAINIMPL_H

#include "EagerConstraint.h"
#include <vector>
#include "language/Atom.h"
#include "ExecutionManager.h"
#include "CompilationManager.h"
#include "datastructures/DenseMap.h"
#include <unordered_map>
#include "../Literal.h"
class Solver;
class EagerConstraintImpl : public EagerConstraint {
public:
    EagerConstraintImpl();
    virtual ~EagerConstraintImpl();
    virtual bool check_postponed()const{return executionManager.postponedReason();}
    virtual void setFilename(const std::string & executablePath, const std::string & filename);
    virtual void onLiteralTrue(int var, int decisionLevel, std::vector<int> & propagatedLiterals);
    virtual void onLiteralsUndefined(const std::vector<int> & lits);
    virtual void getReasonForLiteral(int lit, std::vector<int> & reason);
    virtual void addedVarName(int var, const std::string & atomString);
    virtual void onFact(int var);
    virtual void onAnswerSet(const std::vector<int>& answerSet);
    virtual void simplifyAtLevelZero(std::vector<int> & output);
    virtual const std::vector<unsigned int> & getVariablesToFreeze();
    virtual const std::vector<int> & getWatchedLiterals();
    virtual const std::string & getFilepath() const;
    void notifyStartingSolver()const{ executionManager.notifyStartingSolver();}
    virtual Reason* getPostponedeReason(Literal lit){return executionManager.getPostponedeReason(lit);}
    virtual void addSolver(const Solver& solver){this->solver = &solver;}
private:
    
    void performCompilation();
    
    ExecutionManager executionManager;
    CompilationManager compilationManager;
    std::vector<unsigned> atomsToFreeze;
    std::vector<int> watchedLiterals;
    std::vector<unsigned> watchedAtomsNotCompletion;
    std::unordered_set<int> watchedLiteralsSet;
    std::unordered_set<unsigned> watchedAtomsSetNotCompletion;
    std::vector<unsigned> idbWatchedAtoms;
    std::unordered_set<int> facts;
    std::string filepath;
    bool compilationDone = false;
    std::string fileDirectory;
    std::string filename;
    const Solver* solver;
};

#endif /* EAGERCONSTRAINIMPL_H */