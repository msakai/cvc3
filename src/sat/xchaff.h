///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// File: xchaff.h       						     //
// Author: Clark Barrett                                                     //
// Created: Wed Oct 16 17:31:50 2002					     //
// Description: Enhanced C++ API for Chaff                                   //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////

#ifndef _XCHAFF_H_
#define _XCHAFF_H_

#include "sat_api.h"
#include "xchaff_solver.h"

using namespace std;

class Xchaff :public SatSolver {
  CSolver *_solver;

  Lit  (*_decision_hook)(void *, bool *);
  void (*_assignment_hook)(void *, Var, int);
  void *_decision_hook_cookie;
  void *_assignment_hook_cookie;

  static Var mkVar(int id) { Var v; v.id = id; return v; }
  static Lit mkLit(int id) { Lit l; l.id = id; return l; }
  static Clause mkClause(int id) { Clause c; c.id = id; return c; }

public:
  Xchaff()  { _solver = new CSolver; }
  ~Xchaff() { delete _solver; }

  /////////////////////////////////////////////////////////////////////////////
  // Implementation of SAT_API                                               //
  /////////////////////////////////////////////////////////////////////////////

  int   NumVariables()
        { return _solver->num_variables(); }
  Var   AddVariables(int nvars)
        { return mkVar(_solver->add_variables(nvars)); }
  Var   GetVar(int varIndex)
        { return mkVar(varIndex); }
  int   GetVarIndex(Var v)
        { return v.id; }
  Var   GetFirstVar()
        { Var v; if (_solver->num_variables() != 0) v.id = 1; return v; }
  Var   GetNextVar(Var var)
        { Var v;
	  if (var.id != _solver->num_variables()) v.id = var.id+1; return v; }
  Lit   MakeLit(Var var, int phase)
        { return mkLit((var.id << 1)+phase); }
  Var   GetVarFromLit(Lit lit)
        { return mkVar(lit.id >> 1); }
  int   GetPhaseFromLit(Lit lit)
        { return lit.id & 1; }
  int   NumClauses()
        { return _solver->num_clauses(); }
  Clause AddClause(vector<Lit>& lits)
        { return mkClause(_solver->add_clause((vector<long>&)lits)); }
  Clause GetClause(int clauseIndex);
  Clause GetFirstClause()
        { Clause c;
	  for (unsigned i=0; i< _solver->clauses().size(); ++i)
	    if ( _solver->clause(i).in_use()) { c.id = i; break; }
	  return c; }
  Clause GetNextClause(Clause clause)
        { Clause c;
	  for (unsigned i= clause.id + 1; i< _solver->clauses().size(); ++i)
            if ( _solver->clause(i).in_use()) { c.id = i; break; }
          return c; }
  void  GetClauseLits(Clause clause, vector<Lit>* lits);
  SatSolver::SATStatus Satisfiable(bool allowNewClauses);
  int   GetVarAssignment(Var var)
        { return _solver->variable(var.id).value(); }

  // Not implemented yet:
  SatSolver::SATStatus Continue();
  void Restart() { assert(0); }
  void Reset() { assert(0); }

  void  RegisterDLevelHook(void (*f)(void *, int), void *cookie)
        { _solver->RegisterDLevelHook(f, cookie); }

  static int TranslateDecisionHook(void *cookie, bool *done)
  {
    Xchaff *b = (Xchaff*)cookie;
    Lit lit = b->_decision_hook(b->_decision_hook_cookie, done);
    return lit.id;
  }

  void  RegisterDecisionHook(Lit (*f)(void *, bool *), void *cookie)
        { _decision_hook = f; _decision_hook_cookie = cookie;
	  _solver->RegisterDecisionHook(TranslateDecisionHook, this); }

  static void TranslateAssignmentHook(void *cookie, int var, int value)
  {
    Xchaff *b = (Xchaff*)cookie;
    b->_assignment_hook(b->_assignment_hook_cookie, mkVar(var), value);
  }

  void  RegisterAssignmentHook(void (*f)(void *, Var, int), void *cookie)
        { _assignment_hook = f; _assignment_hook_cookie = cookie;
	  _solver->RegisterAssignmentHook(TranslateAssignmentHook, this); }
  void  RegisterDeductionHook(void (*f)(void *), void *cookie)
        { _solver->RegisterDeductionHook(f, cookie); }
  bool  SetBudget(int budget)  // budget is time in seconds
        { _solver->set_time_limit(float(budget)); return true; }
  bool  SetMemLimit(int mem_limit)
        { _solver->set_mem_limit(mem_limit); return true; }
  bool  SetRandomness(int n)
        { _solver->set_randomness(n); return true; }
  bool  SetRandSeed(int seed)
        { _solver->set_random_seed(seed); return true; }
  bool  EnableClauseDeletion()
        { _solver->enable_cls_deletion(true); return true; }
  bool  DisableClauseDeletion()
        { _solver->enable_cls_deletion(false); return true; }
  int   GetBudgetUsed()
        { return int(_solver->total_run_time()); }
  int   GetMemUsed()
        { return _solver->estimate_mem_usage(); }
  int   GetNumDecisions()
        { return _solver->num_decisions(); }
  int   GetNumConflicts()
        { return -1; }
  int   GetNumExtConflicts()
        { return -1; }
  float GetTotalTime()
        { return _solver->total_run_time(); }
  float GetSATTime()
        { return -1; }
  int   GetNumLiterals()
        { return _solver->num_literals(); }
  int   GetNumDeletedClauses()
        { return _solver->num_deleted_clauses(); }
  int   GetNumDeletedLiterals()
        { return _solver->num_deleted_literals(); }
  int   GetNumImplications()
        { return _solver->num_implications(); }
  int   GetMaxDLevel()
        { return _solver->max_dlevel(); }
};

#endif







