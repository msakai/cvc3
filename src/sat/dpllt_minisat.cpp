/*****************************************************************************/
/*!
 *\file dpllt_minisat.cpp
 *\brief Implementation of dpllt module using MiniSat
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


#include "dpllt_minisat.h"
#include "minisat_solver.h"
#include "exception.h"

using namespace std;
using namespace CVC3;
using namespace SAT;


DPLLTMiniSat::DPLLTMiniSat(TheoryAPI* theoryAPI, Decider* decider, bool printStats)
  : DPLLT(theoryAPI, decider), d_printStats(printStats) {
  pushSolver();
};

DPLLTMiniSat::~DPLLTMiniSat() {
  while (!d_solvers.empty()) {
    // don't pop theories, this is not allowed when cvc shuts down.
    delete (d_solvers.top());
    d_solvers.pop();
  }
}

MiniSat::Solver* DPLLTMiniSat::getActiveSolver() {
  DebugAssert(!d_solvers.empty(), "DPLLTMiniSat::getActiveSolver: no solver");
  return d_solvers.top();
};


void DPLLTMiniSat::pushSolver() {
  if (d_solvers.empty()) {
    d_solvers.push(new MiniSat::Solver(d_theoryAPI, d_decider));
  }
  else {
    d_solvers.push(MiniSat::Solver::createFrom(getActiveSolver()));
  }
}

QueryResult DPLLTMiniSat::search()
{
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::search: no solver");
  DebugAssert(getActiveSolver()->inPush(), "DPLLTMiniSat::search: solver not pushed");

  // search
  MiniSat::Solver* solver = getActiveSolver();
  QueryResult result = solver->search();

  // print statistics
  if (d_printStats) {
    switch (result) {
    case SATISFIABLE:
      break;
    case UNSATISFIABLE:
      cout << "Instance unsatisfiable" << endl;
      break;
    case ABORT:
      cout << "aborted, unable to determine the satisfiablility of the instance" << endl;
      break;
    case UNKNOWN:
      cout << "unknown, unable to determing the satisfiablility of the instance" << endl;
      break;
    default:
      FatalAssert(false, "DPLTBasic::handle_result: Unknown outcome");
    }
    
    cout << "Number of Decisions\t\t\t" << solver->getStats().decisions << endl;
    cout << "Number of Propagations\t\t\t" << solver->getStats().propagations << endl;
    cout << "Number of Propositional Conflicts\t"
	 << (solver->getStats().conflicts - solver->getStats().theory_conflicts) << endl;
    cout << "Number of Theory Conflicts\t\t" << solver->getStats().theory_conflicts << endl;
    cout << "Number of Variables\t\t\t" << solver->nVars() << endl;
    cout << "Number of Literals\t\t\t"
	 << (solver->getStats().clauses_literals + solver->getStats().learnts_literals) << endl;
    cout << "Max. Number of Literals\t\t\t" << solver->getStats().max_literals << endl;
    cout << "Number of Clauses\t\t\t" << solver->getClauses().size() << endl;
    cout << "Number of Lemmas\t\t\t" << solver->getLemmas().size() << endl;
    cout << "Max. Decision Level\t\t\t" << solver->getStats().max_level << endl;
    cout << "Number of Deleted Clauses\t\t" << solver->getStats().del_clauses << endl;
    cout << "Number of Deleted Lemmas\t\t" << solver->getStats().del_lemmas << endl;
    cout << "Number of Database Simplifications\t" << solver->getStats().db_simpl << endl;
    cout << "Number of Lemma Cleanups\t\t" << solver->getStats().lm_simpl << endl;
    
    cout << "Debug\t\t\t\t\t" << solver->getStats().debug << endl;
  }

  // the dpllt interface requires that for an unsat result
  // all theory pops are undone right away.
  if (result == UNSATISFIABLE) {
    d_solvers.top()->popTheories();
    d_theoryAPI->pop();
  }

  return result;
}


QueryResult DPLLTMiniSat::checkSat(const CNF_Formula& cnf)
{
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::checkSat: no solver");

  // perform any requested solver pops
  getActiveSolver()->doPops();

  DebugAssert(!getActiveSolver()->inSearch(), "DPLLTMiniSat::checkSat: solver already in search");

  // required by dpllt interface: theory push before search
  d_theoryAPI->push();
    
  // solver already in use, so create a new solver
  if (getActiveSolver()->inSearch()) {
    pushSolver();
  }

  // add new formula and search
  getActiveSolver()->addFormula(cnf, false);
  return search();
}


QueryResult DPLLTMiniSat::continueCheck(const CNF_Formula& cnf) 
{
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::continueCheck: no solver");

  // if the current solver has no push, all its pushes have already been undone,
  // so remove it
  if (!getActiveSolver()->inPush()) {
    DebugAssert(!getActiveSolver()->inSearch(), "DPLLTMiniSat::continueCheck: solver without push in search");
    delete getActiveSolver();
    d_solvers.pop();
  }

  // perform any requested solver pops
  getActiveSolver()->doPops();

  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::continueCheck: no solver (2)");
  DebugAssert(getActiveSolver()->inPush(), "DPLLTMiniSat::continueCheck: solver not in push");
  DebugAssert(getActiveSolver()->inSearch(), "DPLLTMiniSat::continueCheck: solver not in search");

  // add new formula and search
  getActiveSolver()->addFormula(cnf, false);
  return search();
}


void DPLLTMiniSat::push() {
  // perform any requested solver pops
  getActiveSolver()->doPops();

  // if the current solver is already in a search, then create a new one
  if (getActiveSolver()->inSearch()) {
    pushSolver();
  }
  
  getActiveSolver()->push();
  d_theoryAPI->push();
}

void DPLLTMiniSat::pop() {
  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::pop: no solver");

  // if the current solver has no push, all its pushes have already been undone,
  // so remove it
  if (!getActiveSolver()->inPush()) {
    DebugAssert(!getActiveSolver()->inSearch(), "DPLLTMiniSat::pop: solver without push in search");
    delete getActiveSolver();
    d_solvers.pop();
  }

  DebugAssert(d_solvers.size() > 0, "DPLLTMiniSat::pop: no solver 2");
  DebugAssert(getActiveSolver()->inPush(), "DPLLTMiniSat::pop: solver not in push");

  // undo checkSat theory push for an invalid query.
  // for a valid query this is done in search right away.
  if (getActiveSolver()->inSearch() && getActiveSolver()->isConsistent()) {
    d_theoryAPI->pop();  
  }
  getActiveSolver()->requestPop();
  d_theoryAPI->pop();
}


void DPLLTMiniSat::addAssertion(const CNF_Formula& cnf) {
  // perform any requested solver pops
  getActiveSolver()->doPops();

  // if the current solver is already performing a search create a new solver
  if (getActiveSolver()->inSearch()) {
    pushSolver();
  }

  getActiveSolver()->addFormula(cnf, false);

  // Immediately assert unit clauses -
  // the intention is to make these immediately available for interactive use
  for (CNF_Formula::const_iterator i = cnf.begin(); i != cnf.end(); ++i) {
    if ((*i).isUnit()) d_theoryAPI->assertLit(*(*i).begin());
  }
}


Var::Val DPLLTMiniSat::getValue(Var var) {
  DebugAssert(d_solvers.size() > 0,
	      "DPLLTMiniSat::getValue: should be called after a previous satisfiable result");

  MiniSat::lbool value = getActiveSolver()->getValue(MiniSat::cvcToMiniSat(var));
  if (value == MiniSat::l_True)
    return Var::TRUE_VAL;
  else if (value == MiniSat::l_False)
    return Var::FALSE_VAL;
  else
    return Var::UNKNOWN;
}
