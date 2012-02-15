/*****************************************************************************/
/*!
 *\file minisat_derivation.h
 *\brief MiniSat proof logging
 *
 * Author: Alexander Fuchs
 *
 * Created: Sun Dec 07 11:09:00 2007
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 */
/*****************************************************************************/

#ifndef _cvc3__sat__minisat_derivation_h_
#define _cvc3__sat__minisat_derivation_h_


#include "minisat_types.h"
#include <hash_map.h>
#include <hash_set.h>
#include <vector>
#include <deque>
#include <algorithm>
#include <string>

namespace MiniSat {
  // a resolution inference as a sequence of binary resolution steps
  class Inference {
  public:
    typedef std::vector<std::pair<Lit, int> > TSteps;

  private:
    // id of first clause
    int d_start;

    // binary resolution step:
    // result of previous step (or d_start)
    // on literal with next clause (given by id)
    TSteps d_steps;

  public:
    Inference(int clauseID) : d_start(clauseID) {};

    void add(Lit lit, int clauseID) {
      d_steps.push_back(std::make_pair(lit, clauseID));
    };

    void add(Lit lit, Clause* clause) {
      add(lit, clause->id());
    };

    int getStart() const {
      return d_start;
    }

    const TSteps& getSteps() const {
      return d_steps;
    }

    // returns steps as a lits: clauseId0 literal0.toString clauseID1 ...
    std::string toString() const;
  };



  class Solver;

  // Heavily based on the proof logging version of MiniSat (1.14p)
  //
  // Note: this implementation keeps the whole derivation in memory -
  // for many problems this is not feasible.
  // should provide an alternative implementation that logs the derivation
  // to a file and constructs the proof from it.
  class Derivation {
  public:
    typedef Hash::hash_map<int, Clause*> TClauses;
    typedef Hash::hash_set<int> TInputClauses;
    typedef Hash::hash_map<int, Inference*> TInferences;

  private:
    // mapping from id to clause
    TClauses d_clauses;

    // as an additional check, explicitely mark which clauses are input clauses
    // by adding their id to this set.
    //
    // as an invariant an id should be either in d_inferences or d_inputClauses,
    // as a clause does exactly have no inference attached if it is an input clause.
    TInputClauses d_inputClauses;

    // unit clauses derived with computeRootReason
    // mapping from index of literal to clause
    TClauses d_unitClauses;

    // mapping from clause id to the inference it was derived by
    TInferences d_inferences;

    // clauses removed from the solver
    std::deque<Clause*> d_removedClauses;

    // empty clause of derivation, if derived
    Clause* d_emptyClause;

  public:
    Derivation() : d_emptyClause(NULL) {};
    ~Derivation();

    // note: allow for duplicate insertion of clauses registerClause and registerInputClause,
    // as this can happen in the current implementation
    // for theory clauses which are inconsistent on insertion.

    // register a new clause
    void registerClause(Clause* clause) {
      // if clause with id does already exist,
      // then it must be the same clause wrt. its literals
      IF_DEBUG (
        if (d_clauses.contains(clause->id())) {
	  Clause* old = d_clauses[clause->id()];
	  DebugAssert(old->size() == clause->size(),
		      "MiniSat::Derivation::registerClause: two clauses of different size registered with same id");

	  std::vector<int> oldLiterals;
	  for (int i = 0; i < old->size(); ++i) {
	    oldLiterals.push_back((*old)[i].index());
	  }
	  
	  std::vector<int> newLiterals;
	  for (int i = 0; i < clause->size(); ++i) {
	    newLiterals.push_back((*clause)[i].index());
	  }

	  std::sort(oldLiterals.begin(), oldLiterals.end());
	  std::sort(newLiterals.begin(), newLiterals.end());
	  for (std::vector<int>::size_type i = 0; i < oldLiterals.size(); ++i) {
	    DebugAssert(oldLiterals[i] == newLiterals[i],
			"MiniSat::Derivation::registerClause: two clauses with different literals registered with same id");
	  }
        }
      )

      d_clauses[clause->id()] = clause;
    };

    // mark clause as input clause, i.e. true without premises
    void registerInputClause(int clauseID) {
      d_inputClauses.insert(clauseID);
    };

    // clause has been removed from the solver or created internally in Derivation,
    // so store it here for later garbage collection.
    void removedClause(Clause* clause) {
      DebugAssert(clause != NULL, "MiniSat::derivation:removedClause: NULL");
      d_removedClauses.push_back(clause);
    };

    // register the inference of a clause; takes ownership of inference
    void registerInference(int clauseID, Inference* inference) {
      DebugAssert(!d_inferences.contains(clauseID),
		  "MiniSat::Derivation::registerInference: inference for clauseID already registered");
      d_inferences[clauseID] = inference;
    };

    // implied is a literal that is implied at the root level.
    // return the id of the implying unit clause [literal], if it exists.
    //
    // otherwise derive it from its reasons and return the new clause id.
    // derived unit clauses are stored internally, independently of the Solver
    //
    // may resolve theory implications with Solver::resolveTheoryImplication
    int computeRootReason(Lit implied, Solver* solver);


    // register the empty clause (or a clause falsified in the root level)
    // showing that the clause set is unsatisfiable.
    //
    // if clause is not the empty clause, the empty clause is derived from it,
    // possible using computeRootReason
    void finish(Clause* clause, Solver* solver);


    // print the derivation of the given clause
    //
    // output is of the form:
    // ID D : L1 ... Ln : C1 K1 C2 K2 ... Cm
    // where:
    // ID - the id of a clause
    // D - 'I' for an input clause, 'D' for a clause derived from other clauses
    // Li - the clause literals
    // Ci Ki - the clause is derived from these clauses by binary resolution on the given literals
    //
    // factoring is done after each resolution step, i.e. duplicate literals are removed from the clause.
    //
    // example:
    // 3 D : +12 -2 -33 : 1 +10 2
    // says that the clause with the id 3 consists of the literals +12, -2, -33,
    // and was derived by resolution between the clauses with ids 1 and 2,
    // where the literal +10 is in clause 1 and -10 is in clause 2.
    //
    // for example, 1 may be the clause +12 +10 -2, and 2 may be -10 -2 -33,
    // which resolved on +10 yield the clause +12 -2 -2 -33,
    // which after factoring simplified to +12 -2 -33.
    void printProof(Clause* clause);

    // print the derivation of the empty clause.
    void printProof();

    // see Solver::push - clauseID is the highest currently used clause id
    void push(int clauseID);

    // see Solver::pop - clauseID corresponds to a clause id used in a push
    void pop(int clauseID);
  };
}


#endif
