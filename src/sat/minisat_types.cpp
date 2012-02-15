/*****************************************************************************/
/*!
 *\file minisat_types.cpp
 *\brief MiniSat internal types
 *
 * Author: Alexander Fuchs
 *
 * Created: Fri Sep 08 11:04:00 2006
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



#include "minisat_types.h"

using namespace std;

namespace MiniSat {

  // static class members
  Clause* Clause::s_decision = NULL;
  Clause* Clause::s_theoryImplication = NULL;

  Clause* Clause_new(const vector<Lit>& ps, int id) {
    DebugAssert(sizeof(Lit)   == sizeof(uint), "MiniSat::Types::Clause_new Lit");
    DebugAssert(sizeof(float) == sizeof(uint), "MiniSat::Types::Clause_new float");
    DebugAssert(sizeof(id)    == sizeof(uint), "MiniSat::Types::Clause_new id");

    //   size_learnt
    // + literals
    // + id
    void* mem = xmalloc<char>(sizeof(uint)*(ps.size() + 2));
    return new (mem) Clause(false, ps, id);
  }

  Clause* Lemma_new(const vector<Lit>& ps, int id, int pushID) {
    DebugAssert(sizeof(Lit)      == sizeof(uint), "MiniSat::Types::Lemma_new Lit");
    DebugAssert(sizeof(float)    == sizeof(uint), "MiniSat::Types::Lemma_new float");
    DebugAssert(sizeof(id)       == sizeof(uint), "MiniSat::Types::Lemma_new id");

    //   size_learnt
    // + literals
    // + id
    // + pushID
    // + activity
    void* mem = xmalloc<char>(sizeof(uint)*(ps.size() + 4));
    Clause* clause = new (mem) Clause(true, ps, id);
    clause->pushID() = pushID;
    return clause;
  }

  Clause* Clause::Decision() {
    if (s_decision == NULL) {
      vector<Lit> lits;
      s_decision = Clause_new(lits, -1);
    }
    
    return s_decision;
  }
  
  Clause* Clause::TheoryImplication() {
    if (s_theoryImplication == NULL) {
      vector<Lit> lits;
      s_theoryImplication = Clause_new(lits, -2);
    }
    
    return s_theoryImplication;
  }

  void Clause::toLit(vector<Lit>& literals) const {
    for (int i = 0; i < size(); ++i) {
      literals.push_back(data[i]);
    }
  }

}
