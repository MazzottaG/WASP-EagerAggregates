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
 * File:   EagerConstraint.h
 * Author: bernardo
 *
 * Created on March 27, 2019, 3:18 PM
 */

#ifndef EAGERCONSTRAINT_H
#define EAGERCONSTRAINT_H
#include <string>
#include <vector>

class EagerConstraint {
public:

    virtual ~EagerConstraint() {
    };
    virtual void setFilename(const std::string & executablePath, const std::string & filename) = 0;
    virtual void onLiteralTrue(int var, int decisionLevel, std::vector<int> & propagatedLiterals) = 0;
    virtual void onLiteralsUndefined(const std::vector<int> & lits) = 0;
    virtual void getReasonForLiteral(int lit, std::vector<int> & reason) = 0;
    virtual void addedVarName(int var, const std::string & atomString) = 0;
    virtual void onFact(int var) = 0;
    virtual const std::vector<unsigned int> & getVariablesToFreeze() = 0;
};

#endif /* EAGERCONSTRAINT_H */