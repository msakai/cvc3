/*****************************************************************************/
/*!
 *\file minisat_derivation.cpp
 *\brief Proof logging minisat
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


#include "minisat_derivation.h"
#include "minisat_solver.h"
#include <set>
#include <iostream>

using namespace MiniSat;
using namespace std;

std::string Inference::toString() const {
  ostringstream buffer;
  buffer << getStart();
  for (Inference::TSteps::const_iterator step = d_steps.begin(); step != d_steps.end(); ++step) {
    buffer << " " << step->first.toString() << " " << step->second;
  }
  return buffer.str();
}





Derivation::~Derivation() {
  // deallocate generated unit clauses
  for (TClauses::iterator i = d_unitClauses.begin(); i != d_unitClauses.end(); ++i) {
    xfree(i->second);
  }
  
  // deallocate removed clauses
  for (std::deque<Clause*>::iterator i = d_removedClauses.begin(); i != d_removedClauses.end(); ++i) {
    xfree(*i);
  }
  
  // deallocate inferences
  for (TInferences::iterator i = d_inferences.begin(); i != d_inferences.end(); ++i) {
    delete i->second;
  }
}


int Derivation::computeRootReason(Lit implied, Solver* solver) {
  Clause* reason = solver->getReason(implied);
  DebugAssert(reason != NULL, "MiniSat::Derivation::computeRootReason: implied reason is NULL");
  DebugAssert(reason != Clause::Decision(), "MiniSat::Derivation::computeRootReason: implied is a decision");
  DebugAssert((*reason)[0] == implied, "MiniSat::Derivation::computeRootReason: implied is not in its reason");
  IF_DEBUG (
    DebugAssert(solver->getValue((*reason)[0]) == l_True,
		"MiniSat::Derivation::computeRootReason: literal not implied (TRUE)");
    for (int i = 1; i < reason->size(); ++i) {
      DebugAssert(solver->getValue((*reason)[i]) == l_False,
		  "MiniSat::Derivation::computeRootReason: literal not implied (FALSE)");
    }
  )

  // already a unit clause, so done
  if (reason->size() == 1) {
    return reason->id();
  }

  // already derived the unit clause internally
  TClauses::const_iterator iter = d_unitClauses.find(implied.index());
  if (iter != d_unitClauses.end()) {
    return iter->second->id();
  }


  // otherwise resolve the reason ...
  Inference* inference = new Inference(reason->id());
  for (int i = 1; i < reason->size(); ++i) {
    Lit lit((*reason)[i]);
    inference->add(lit, computeRootReason(~lit, solver));
  }

  // and create the new unit clause
  // (after resolve, so that clause ids are chronological wrt. inference)
  vector<Lit> literals;
  literals.push_back(implied);
  Clause* unit = Clause_new(literals, solver->nextClauseID());

  d_unitClauses[implied.index()] = unit;
  registerClause(unit);
  registerInference(unit->id(), inference);

  return unit->id();
}


void Derivation::finish(Clause* clause, Solver* solver) {
  DebugAssert(clause != NULL, "MiniSat::derivation:finish:");

  // already the empty clause
  if (clause->size() == 0) {
    d_emptyClause = clause;
  }
  // derive the empty clause
  else {
    Inference* inference = new Inference(clause->id());
    for (int i = 0; i < clause->size(); ++i) {
      Lit lit((*clause)[i]);
      inference->add(lit, computeRootReason(~lit, solver));
    }
    vector<Lit> literals;
    Clause* empty = Clause_new(literals, solver->nextClauseID());
    removedClause(empty);
    d_emptyClause = empty;
    registerClause(empty);
    registerInference(empty->id(), inference);
  }

//     cout << "PROOF_START" << endl;
//     printProof();
//     cout << "PROOF_END" << endl;
};


void Derivation::printProof() {
  DebugAssert(d_emptyClause != NULL, "MiniSat::Derivation:printProof: no empty clause");
  printProof(d_emptyClause);
}

void Derivation::printProof(Clause* clause) {
  // find all relevant clauses

  // - relevant: set clauses used in derivation
  // - regress: relevant clauses whose antecedents have to be checked
  std::set<int> relevant;
  std::set<int> regress;

  regress.insert(clause->id());
  while (!regress.empty()) {
    // pick next clause to derive - start from bottom, i.e. latest derived clause
    int clauseID = *(regress.rbegin());
    regress.erase(clauseID);

    // move to clauses relevant for the derivation
    DebugAssert(relevant.count(clauseID) == 0, "Solver::printProof: already in relevant");
    relevant.insert(clauseID);

    // process antecedents
    TInferences::const_iterator iter = d_inferences.find(clauseID);
    // input clause
    if (iter == d_inferences.end()) {
      DebugAssert(d_inputClauses.contains(clauseID),
		  "Solver::printProof: clause without antecedents is not marked as input clause");
    }

    else {
      Inference* inference = iter->second;
      regress.insert(inference->getStart());
      const Inference::TSteps& steps = inference->getSteps();
      for (Inference::TSteps::const_iterator step = steps.begin(); step != steps.end(); ++step) {
	regress.insert(step->second);
      }
    }
  }


  // print proof
  for (std::set<int>::iterator i = relevant.begin(); i != relevant.end(); ++i) {
    int clauseID = *i;
    DebugAssert(d_clauses.contains(clauseID), "Solver::printProof: clause id in proof is not in clauses");
    Clause* clause = d_clauses.find(clauseID)->second;

    Inference* inference = NULL;
    TInferences::const_iterator j = d_inferences.find(clauseID);
    if (j != d_inferences.end()) {
      inference = j->second;
    }

    // ID D : L1 ... Ln : C1 K1 C2 K2 ... Cm
    cout << clauseID;
    // input clause or derived clause?
    if (d_inputClauses.contains(clauseID)) {
      cout << " I ";
    } else {
      cout << " D ";
    }      
    cout << ": " << clause->toString() << " : ";
    if (inference != NULL) cout << inference->toString();
    cout << endl;    
  }
}


void Derivation::push(int clauseID) {
}

void Derivation::pop(int clauseID) {
  // remove all popped clauses
  TClauses::iterator i = d_clauses.begin();
  while (i != d_clauses.end()) {
    if ((*i).second->pushID() > clauseID) {
      int id = (*i).first;
      ++i;
      d_clauses.erase(id);
      d_unitClauses.erase(id);
      d_inferences.erase(id);
    }
    else {
      ++i;
    }
  }

  // undo conflicting clause
  if (d_emptyClause != NULL && d_emptyClause->pushID() > clauseID)
    d_emptyClause = NULL;

  // delete popped and removed clauses
  std::deque<Clause*>::iterator j = d_removedClauses.begin();
  while (j != d_removedClauses.end()) {
    if ((*j)->pushID() > clauseID) {
      xfree(*j);
      j = d_removedClauses.erase(j);
    } else {
      ++j;
    }
  }
}
