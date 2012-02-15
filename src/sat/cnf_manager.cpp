/*****************************************************************************/
/*!
 *\file cnf_manager.cpp
 *\brief Implementation of CNF_Manager
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 02:30:02 2006
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


#include "cnf_manager.h"
#include "cnf_rules.h"
#include "common_proof_rules.h"
#include "theorem_manager.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


CNF_Manager::CNF_Manager(TheoremManager* tm)
  : d_commonRules(tm->getRules()),
    //    d_theorems(tm->getCM()->getCurrentContext()),
    d_clauseIdNext(0),
    //    d_translated(tm->getCM()->getCurrentContext()),
    d_bottomScope(-1),
    d_cnfCallback(NULL)
{
  d_rules = createProofRules(tm);
  // Push dummy varinfo onto d_varInfo since Var's are indexed from 1 not 0
  Varinfo v;
  d_varInfo.push_back(v);
}


CNF_Manager::~CNF_Manager()
{
  delete d_rules;
}


void CNF_Manager::registerAtom(const Expr& e, const Theorem& thm)
{
  DebugAssert(!e.isRegisteredAtom() || e.isUserRegisteredAtom(), "Atom already registered");
  if (d_cnfCallback && !e.isRegisteredAtom()) d_cnfCallback->registerAtom(e, thm);
}


Theorem CNF_Manager::replaceITErec(const Expr& e, Var v, bool translateOnly)
{
  // Quick exit for atomic expressions
  if (e.isAtomic()) return d_commonRules->reflexivityRule(e);

  // Check cache
  Theorem thm;
  bool foundInCache = false;
  ExprMap<Theorem>::iterator iMap = d_iteMap.find(e);
  if (iMap != d_iteMap.end()) {
    thm = (*iMap).second;
    foundInCache = true;
  }

  if (e.getKind() == ITE) {
    // Replace non-Bool ITE expressions
    DebugAssert(!e.getType().isBool(), "Expected non-Bool ITE");
    // generate e = x for new x
    if (!foundInCache) thm = d_commonRules->varIntroSkolem(e);
    Theorem thm2 = d_commonRules->symmetryRule(thm);
    thm2 = d_commonRules->iffMP(thm2, d_rules->ifLiftRule(thm2.getExpr(), 1));
    d_translateQueueVars.push_back(v);
    d_translateQueueThms.push_back(thm2);
    d_translateQueueFlags.push_back(translateOnly);
  }
  else {
    // Recursively traverse, replacing ITE's
    vector<Theorem> thms;
    vector<unsigned> changed;
    unsigned index = 0;
    Expr::iterator i, iend;
    if (foundInCache) {
      for(i = e.begin(), iend = e.end(); i!=iend; ++i, ++index) {
        replaceITErec(*i, v, translateOnly);
      }
    }
    else {
      for(i = e.begin(), iend = e.end(); i!=iend; ++i, ++index) {
        thm = replaceITErec(*i, v, translateOnly);
        if(thm.getLHS() != thm.getRHS()) {
          thms.push_back(thm);
          changed.push_back(index);
        }
      }
      if(changed.size() > 0) {
        thm = d_commonRules->substitutivityRule(e, changed, thms);
      }
      else thm = d_commonRules->reflexivityRule(e);
    }
  }

  // Update cache and return
  if (!foundInCache) d_iteMap[e] = thm;
  return thm;
}


Lit CNF_Manager::translateExprRec(const Expr& e, CNF_Formula& cnf, const Theorem& thmIn)
{
  if (e.isFalse()) return Lit::getFalse();
  if (e.isTrue()) return Lit::getTrue();
  if (e.isNot()) return !translateExprRec(e[0], cnf, thmIn);

  ExprMap<Var>::iterator iMap = d_cnfVars.find(e);

  if (e.isTranslated()) {
    DebugAssert(iMap != d_cnfVars.end(), "Translated expr should be in map");
    return Lit((*iMap).second);
  }
  else e.setTranslated(d_bottomScope);

  Var v(int(d_varInfo.size()));
  bool translateOnly = false;

  if (iMap != d_cnfVars.end()) {
    v = (*iMap).second;
    translateOnly = true;
    d_varInfo[v].fanouts.clear();
  }
  else {
    d_varInfo.resize(v+1);
    d_varInfo.back().expr = e;
    d_cnfVars[e] = v;
  }

  Expr::iterator i, iend;

  bool isAnd = false;
  switch (e.getKind()) {
    case AND:
      isAnd = true;
    case OR: {
      vector<Lit> lits;
      unsigned idx;
      for (i = e.begin(), iend = e.end(); i != iend; ++i) {
        lits.push_back(translateExprRec(*i, cnf, thmIn));
      }
      for (idx = 0; idx < lits.size(); ++idx) {
        cnf.newClause();
        cnf.addLiteral(Lit(v),isAnd);
        cnf.addLiteral(lits[idx], !isAnd);
      }
      cnf.newClause();
      cnf.addLiteral(Lit(v),!isAnd);
      for (idx = 0; idx < lits.size(); ++idx) {
        cnf.addLiteral(lits[idx], isAnd);
      }
      break;
    }
    case IMPLIES: {
      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg1,true);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);
      break;
    }
    case IFF: {
      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1,true);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1,true);
      break;
    }
    case XOR: {
      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1,true);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg1,true);
      break;
    }
    case ITE:
    {
      Lit arg0 = translateExprRec(e[0], cnf, thmIn);
      Lit arg1 = translateExprRec(e[1], cnf, thmIn);
      Lit arg2 = translateExprRec(e[2], cnf, thmIn);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg2);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0);
      cnf.addLiteral(arg2,true);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1,true);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg0,true);
      cnf.addLiteral(arg1);

      cnf.newClause();
      cnf.addLiteral(Lit(v));
      cnf.addLiteral(arg1,true);
      cnf.addLiteral(arg2,true);

      cnf.newClause();
      cnf.addLiteral(Lit(v),true);
      cnf.addLiteral(arg1);
      cnf.addLiteral(arg2);
      break;
    }
    default:
      DebugAssert(!e.isAbsAtomicFormula() || d_varInfo[v].expr == e,
                  "Corrupted Varinfo");
      if (e.isAbsAtomicFormula()) {
        registerAtom(e, thmIn);
        return Lit(v);
      }
      Theorem thm = replaceITErec(e, v, translateOnly);
      const Expr& e2 = thm.getRHS();
      DebugAssert(e2.isAbsAtomicFormula(), "Expected AbsAtomicFormula");
      if (e2.isTranslated()) {
        // Ugly corner case: we happen to create an expression that has been
        // created before.  We remove the current variable and fix up the
        // translation stack.
        if (translateOnly) {
          DebugAssert(v == d_cnfVars[e2], "Expected literal match");
        }
        else {
          d_varInfo.resize(v);
          while (!d_translateQueueVars.empty() &&
                 d_translateQueueVars.back() == v) {
            d_translateQueueVars.pop_back();
          }
          DebugAssert(d_cnfVars.find(e2) != d_cnfVars.end(),
                      "Expected existing literal");
          v = d_cnfVars[e2];
          d_cnfVars[e] = v;
          while (d_translateQueueVars.size() < d_translateQueueThms.size()) {
            d_translateQueueVars.push_back(v);
          }
        }
      }
      else {
        e2.setTranslated(d_bottomScope);
        registerAtom(e2, thmIn);
        if (!translateOnly) {
          DebugAssert(d_cnfVars.find(e2) == d_cnfVars.end(),
                      "Expected new literal");
          d_varInfo[v].expr = e2;
          d_cnfVars[e2] = v;
        }
      }
      return Lit(v);
  }

  // Record fanins / fanouts
  Lit l;
  for (i = e.begin(), iend = e.end(); i != iend; ++i) {
    l = getCNFLit(*i);
    DebugAssert(!l.isNull(), "Expected non-null literal");
    if (!translateOnly) d_varInfo[v].fanins.push_back(l);
    if (l.isVar()) d_varInfo[l.getVar()].fanouts.push_back(v);
  }
  return Lit(v);
}

Lit CNF_Manager::translateExpr(const Theorem& thmIn, CNF_Formula& cnf)
{
  Lit l;
  Var v;
  Expr e = thmIn.getExpr();
  Theorem thm;
  bool translateOnly;

  Lit ret = translateExprRec(e, cnf, thmIn);

  while (d_translateQueueVars.size()) {
    v = d_translateQueueVars.front();
    d_translateQueueVars.pop_front();
    thm = d_translateQueueThms.front();
    d_translateQueueThms.pop_front();
    translateOnly = d_translateQueueFlags.front();
    d_translateQueueFlags.pop_front();
    l = translateExprRec(thm.getExpr(), cnf, thmIn);
    cnf.newClause();
    cnf.addLiteral(l);
    cnf.registerUnit();
    //    d_theorems.insert(d_clauseIdNext, thm);
    cnf.getCurrentClause().setId(d_clauseIdNext++);
    FatalAssert(d_clauseIdNext != 0, "Overflow of clause id's");
    if (!translateOnly) d_varInfo[v].fanins.push_back(l);
    d_varInfo[l.getVar()].fanouts.push_back(v);
  }
  return ret;
}


void CNF_Manager::convertLemma(const Theorem& thm, Clause& c)
{
  DebugAssert(c.size() == 0, "Expected empty clause");
  Theorem clause = d_rules->learnedClause(thm);

  const Expr& e = clause.getExpr();
  if (!e.isOr()) {
    DebugAssert(!getCNFLit(e).isNull(), "Unknown literal");
    c.addLiteral(getCNFLit(e));
  }
  else {
    Expr::iterator iend = e.end();
    for (Expr::iterator i = e.begin(); i != iend; ++i) {
      DebugAssert(!getCNFLit(*i).isNull(), "Unknown literal");
      c.addLiteral(getCNFLit(*i));
    }
  }
  if (c.size() == 1) c.setUnit();

  //  d_theorems.insert(d_clauseIdNext, clause);
  c.setId(d_clauseIdNext++);
  FatalAssert(d_clauseIdNext != 0, "Overflow of clause id's");
}


Lit CNF_Manager::addAssumption(const Theorem& thm, CNF_Formula& cnf)
{
  Lit l = translateExpr(thm, cnf);
  cnf.newClause();
  cnf.addLiteral(l);
  cnf.registerUnit();

  //  d_theorems[d_clauseIdNext] = thm;
  cnf.getCurrentClause().setId(d_clauseIdNext++);
  FatalAssert(d_clauseIdNext != 0, "Overflow of clause id's");

  return l;
}


Lit CNF_Manager::addLemma(const Theorem& thm, CNF_Formula& cnf)
{
  Theorem clause = d_rules->learnedClause(thm);

  Lit l = translateExpr(clause, cnf);
  cnf.newClause();
  cnf.addLiteral(l);
  cnf.registerUnit();

  //  d_theorems.insert(d_clauseIdNext, clause);
  cnf.getCurrentClause().setId(d_clauseIdNext++);
  FatalAssert(d_clauseIdNext != 0, "Overflow of clause id's");

  return l;
}
