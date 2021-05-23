#ifndef AGGRSETPREDICATE_H
#define	AGGRSETPREDICATE_H

#include <unordered_map>
#include <vector>
#include <string>
#include <unordered_set>
#include "../language/Literal.h"
#include "../language/ArithmeticRelation.h"

class AggrSetPredicate {
    private:
        std::vector<std::string> terms;
        std::vector<aspc::Literal> literals;
        std::vector<aspc::ArithmeticRelation> inequalities;
    public:
        void addTerm(std::string t){terms.push_back(t);}
        void addLiteral(aspc::Literal l){literals.push_back(l);}
        void addInequality(aspc::ArithmeticRelation r){inequalities.push_back(r);}
        std::vector<std::string> getTerms()const{return terms;}
        // AggrSetPredicate(){}
        // AggrSetPredicate(const AggrSetPredicate& other){
        //     for(std::string t : other.terms){
        //         terms.push_back(t);
        //     }
        //     for(aspc::Literal l : other.literals){
        //         literals.push_back(l);
        //     }
        //     for(aspc::ArithmeticRelation r : other.inequalities){
        //         inequalities.push_back(r);
        //     }
        // }
        bool operator==(const AggrSetPredicate& predicate){
            std::cout<<"operator =="<<std::endl;
            if(this->terms.size() != predicate.terms.size()){
                return false;
            }

            for(unsigned i=0; i<terms.size(); i++){
                if(terms[i]!=predicate.terms[i])
                    return false;
            }

            if(this->literals.size() != predicate.literals.size()){
                return false;
            }
            for(unsigned i=0; i<literals.size(); i++){
                if(literals[i]==predicate.literals[i]){
                }else{
                    return false;
                }
            }

            if(this->inequalities.size() != predicate.inequalities.size()){
                return false;
            }
            for(unsigned i=0; i<inequalities.size(); i++){
                if(inequalities[i]==predicate.inequalities[i]){
                }else{
                    return false;
                }
            }
            return true;

        }
};
#endif
