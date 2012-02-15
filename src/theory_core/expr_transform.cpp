/*****************************************************************************/
/*!
 * \file expr_transform.cpp
 * 
 * Author: Ying Hu, Clark Barrett
 * 
 * Created: Jun 05 2003
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/


#include "expr_transform.h"
#include "theory_core.h"
#include "command_line_flags.h"
#include "core_proof_rules.h"


using namespace std;
using namespace CVC3;


ExprTransform::ExprTransform(TheoryCore* core) : d_core(core)
{
  d_commonRules = d_core->getCommonRules();  
  d_rules = d_core->getCoreRules();
}


Theorem ExprTransform::smartSimplify(const Expr& e, ExprMap<bool>& cache)
{
  ExprMap<bool>::iterator it;
  vector<Expr> operatorStack;
  vector<int> childStack;
  Expr e2;

  operatorStack.push_back(e);
  childStack.push_back(0);

  while (!operatorStack.empty()) {
    DebugAssert(operatorStack.size() == childStack.size(), "Invariant violated");
    if (childStack.back() < operatorStack.back().arity()) {
      e2 = operatorStack.back()[childStack.back()++];
      it = cache.find(e2);
      if (it != cache.end() || e2.hasFind() ||
          e2.validSimpCache() || e2.arity() == 0) continue;
      if (operatorStack.size() >= 5000) {
        smartSimplify(e2, cache);
        cache[e2] = true;
      }
      else {
        operatorStack.push_back(e2);
        childStack.push_back(0);
      }
    }
    else {
      cache[operatorStack.back()] = true;
      operatorStack.pop_back();
      childStack.pop_back();
    }
  }
  DebugAssert(childStack.empty(), "Invariant violated");
  return d_core->simplify(e);
}


Theorem ExprTransform::preprocess(const Expr& e)
{
  if (!d_core->getFlags()["preprocess"].getBool())
    return d_commonRules->reflexivityRule(e);
  Theorem thm1;
  if (d_core->getFlags()["pp-pushneg"].getBool())
    thm1 = pushNegation(e);
  else
    thm1 = d_commonRules->reflexivityRule(e);
  {
    ExprMap<bool> cache;
    thm1 = d_commonRules->transitivityRule(thm1, smartSimplify(thm1.getRHS(), cache));
  }
  if (d_core->getFlags()["pp-bryant"].getBool())
     thm1 = d_commonRules->transitivityRule(thm1, dobryant(thm1.getRHS()));
 
  ExprMap<bool> cache;
  thm1 = d_commonRules->transitivityRule(thm1, smartSimplify(thm1.getRHS(), cache));
  return thm1;
}


Theorem ExprTransform::preprocess(const Theorem& thm)
{
  return d_commonRules->iffMP(thm, preprocess(thm.getExpr()));
}


// We assume that the cache is initially empty
Theorem ExprTransform::pushNegation(const Expr& e) {
  if(e.isTerm()) return d_commonRules->reflexivityRule(e);
  Theorem res(pushNegationRec(e, false));
  d_pushNegCache.clear();
  return res;
}


// Recursively descend into the expression e, keeping track of whether
// we are under even or odd number of negations ('neg' == true means
// odd, the context is "negative").

// Produce a proof of e <==> e' or !e <==> e', depending on whether
// neg is false or true, respectively.
Theorem ExprTransform::pushNegationRec(const Expr& e, bool neg) {
  TRACE("pushNegation", "pushNegationRec(", e,
	", neg=" + string(neg? "true":"false") + ") {");
  DebugAssert(!e.isTerm(), "pushNegationRec: not boolean e = "+e.toString());
  ExprMap<Theorem>::iterator i = d_pushNegCache.find(neg? !e : e);
  if(i != d_pushNegCache.end()) { // Found cached result
    TRACE("pushNegation", "pushNegationRec [cached] => ", (*i).second, "}");
    return (*i).second;
  }
  // By default, do not rewrite
  Theorem res(d_core->reflexivityRule((neg)? !e : e));
  if(neg) {
    switch(e.getKind()) {
      case TRUE_EXPR: res = d_commonRules->rewriteNotTrue(!e); break;
      case FALSE_EXPR: res = d_commonRules->rewriteNotFalse(!e); break;
      case NOT: 
        res = pushNegationRec(d_commonRules->rewriteNotNot(!e), false);
        break;
      case AND:
        res = pushNegationRec(d_rules->rewriteNotAnd(!e), false);
        break;
      case OR: 
        res = pushNegationRec(d_rules->rewriteNotOr(!e), false);
        break;
      case IMPLIES: {
        vector<Theorem> thms;
        thms.push_back(d_rules->rewriteImplies(e));
        res = pushNegationRec
          (d_commonRules->substitutivityRule(NOT, thms), true);
        break;
      }
//       case IFF:
// 	// Preserve equivalences to explore structural similarities
// 	if(e[0].getKind() == e[1].getKind())
// 	  res = d_commonRules->reflexivityRule(!e);
// 	else
// 	  res = pushNegationRec(d_commonRules->rewriteNotIff(!e), false);
//         break;
      case ITE:
        res = pushNegationRec(d_rules->rewriteNotIte(!e), false);
        break;

      // Replace LETDECL with its definition.  The
      // typechecker makes sure it's type-safe to do so.
      case LETDECL: {
        vector<Theorem> thms;
        thms.push_back(d_rules->rewriteLetDecl(e));
        res = pushNegationRec
          (d_commonRules->substitutivityRule(NOT, thms), true);
        break;
      }
      default:
        res = d_commonRules->reflexivityRule(!e);
    } // end of switch(e.getKind())
  } else { // if(!neg)
    switch(e.getKind()) {
      case NOT: res = pushNegationRec(e[0], true); break;
      case AND:
      case OR:
      case IFF:
      case ITE: {
        Op op = e.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec(*i, false));
        res = d_commonRules->substitutivityRule(op, thms);
        break;
      }
      case IMPLIES:
        res = pushNegationRec(d_rules->rewriteImplies(e), false);
        break;
      case LETDECL:
        res = pushNegationRec(d_rules->rewriteLetDecl(e), false);
        break;
      default:
        res = d_commonRules->reflexivityRule(e);
    } // end of switch(e.getKind())
  }
  TRACE("pushNegation", "pushNegationRec => ", res, "}");
  d_pushNegCache[neg? !e : e] = res;
  return res;
}


Theorem ExprTransform::pushNegationRec(const Theorem& thm, bool neg) {
  DebugAssert(thm.isRewrite(), "pushNegationRec(Theorem): bad theorem: "
	      + thm.toString());
  Expr e(thm.getRHS());
  if(neg) {
    DebugAssert(e.isNot(), 
		"pushNegationRec(Theorem, neg = true): bad Theorem: "
		+ thm.toString());
    e = e[0];
  }
  return d_commonRules->transitivityRule(thm, pushNegationRec(e, neg));
}


Theorem ExprTransform::pushNegation1(const Expr& e) {
  TRACE("pushNegation1", "pushNegation1(", e, ") {");
  DebugAssert(e.isNot(), "pushNegation1("+e.toString()+")");
  Theorem res;
  switch(e[0].getKind()) {
    case TRUE_EXPR: res = d_commonRules->rewriteNotTrue(e); break;
    case FALSE_EXPR: res = d_commonRules->rewriteNotFalse(e); break;
    case NOT: 
      res = d_commonRules->rewriteNotNot(e);
      break;
    case AND:
      res = d_rules->rewriteNotAnd(e);
      break;
    case OR: 
      res = d_rules->rewriteNotOr(e);
      break;
    case IMPLIES: {
      vector<Theorem> thms;
      thms.push_back(d_rules->rewriteImplies(e[0]));
      res = d_commonRules->substitutivityRule(e.getOp(), thms);
      res = d_commonRules->transitivityRule(res, d_rules->rewriteNotOr(res.getRHS()));
      break;
    }
    case ITE:
      res = d_rules->rewriteNotIte(e);
      break;
      // Replace LETDECL with its definition.  The
      // typechecker makes sure it's type-safe to do so.
    case LETDECL: {
      vector<Theorem> thms;
      thms.push_back(d_rules->rewriteLetDecl(e[0]));
      res = d_commonRules->substitutivityRule(e.getOp(), thms);
      res = d_commonRules->transitivityRule(res, pushNegation1(res.getRHS()));
      break;
    }
    default:
      res = d_commonRules->reflexivityRule(e);
  }
  TRACE("pushNegation1", "pushNegation1 => ", res.getExpr(), " }");
  return res;
}
