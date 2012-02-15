///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// File: xchaff.cpp     						     //
// Author: Clark Barrett                                                     //
// Created: Wed Oct 16 17:31:50 2002					     //
// Description: Enhanced C++ API for Chaff                                   //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////


#include "xchaff.h"


SatSolver *SatSolver::Create()
{
  return new Xchaff();
}


SatSolver::Clause Xchaff::GetClause(int clauseIndex)
{
  int i,j;
  SatSolver::Clause c;
  assert(clauseIndex >= 0 && clauseIndex < _solver->num_clauses());
  if (clauseIndex >= _solver->init_num_clauses()) {
    for (i = j = _solver->init_num_clauses()-1; j < clauseIndex;)
      if (_solver->clause(++i).in_use()) j++;
    c.id = j;
  }
  else c.id = clauseIndex;
  return c;
}


void Xchaff::GetClauseLits(SatSolver::Clause clause, vector<Lit>* lits)
{
  int i;
  for (i = 0; i < _solver->clause(clause.id).num_lits(); ++i)
    lits->push_back(mkLit(_solver->clause(clause.id).literal(i).s_var()));
}


SatSolver::SATStatus Xchaff::Satisfiable(bool allowNewClauses)
{
  int status;
  status = _solver->solve(allowNewClauses);
  switch (status) {
    case UNSATISFIABLE: return SatSolver::UNSATISFIABLE;
    case SATISFIABLE: return SatSolver::SATISFIABLE;
    case TIME_OUT: return SatSolver::BUDGET_EXCEEDED;
    case MEM_OUT: return SatSolver::OUT_OF_MEMORY;
  }
  return SatSolver::UNKNOWN;
}


SatSolver::SATStatus Xchaff::Continue()
{
  int status;
  status = _solver->continueCheck();
  switch (status) {
    case UNSATISFIABLE: return SatSolver::UNSATISFIABLE;
    case SATISFIABLE: return SatSolver::SATISFIABLE;
    case TIME_OUT: return SatSolver::BUDGET_EXCEEDED;
    case MEM_OUT: return SatSolver::OUT_OF_MEMORY;
  }
  return SatSolver::UNKNOWN;
}
