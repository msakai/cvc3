/*****************************************************************************/
/*!
 *\file cnf_theorem_producer.cpp
 *\brief Implementation of CNF_TheoremProducer
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 05:49:24 2006
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

#include "cnf_manager.h"

#define _CVC3_TRUSTED_
#include "cnf_theorem_producer.h"


using namespace std;
using namespace CVC3;
using namespace SAT;


/////////////////////////////////////////////////////////////////////////////
// class CNF_Manager trusted methods
/////////////////////////////////////////////////////////////////////////////


CNF_Rules* CNF_Manager::createProofRules(TheoremManager* tm) {
  return new CNF_TheoremProducer(tm);
}


/////////////////////////////////////////////////////////////////////////////
// Proof rules
/////////////////////////////////////////////////////////////////////////////


Theorem CNF_TheoremProducer::learnedClause(const Theorem& thm)
{
  IF_DEBUG(if(debugger.trace("cnf proofs")) {
    ostream& os = debugger.getOS();
    os << "learnedClause {" << endl;
    os << thm;
  });

  if(CHECK_PROOFS) {
    CHECK_SOUND(withAssumptions(),
		"learnedClause: called while running without assumptions");
  }

  vector<Expr> assumptions;

  thm.getLeafAssumptions(assumptions, true /*negate*/);

  vector<Expr>::iterator iend = assumptions.end();
  for (vector<Expr>::iterator i = assumptions.begin();
       i != iend; ++i) {
    DebugAssert(i->isAbsLiteral(), "Expected only literal assumptions");
  }

  if (!thm.getExpr().isFalse())
    assumptions.push_back(thm.getExpr());

  Proof pf;

  if(withProof()) {
    pf = newPf("learned_clause", thm.getProof());
  }

  // Use ExprManager in newExpr, since assumptions may be empty
  DebugAssert(assumptions.size() > 0, "Expected at least one entry");

  Theorem thm2;
  if (assumptions.size() == 1) {
    thm2 = newTheorem(assumptions[0], Assumptions::emptyAssump(), pf);
  }
  else {
    thm2 = newTheorem(Expr(OR, assumptions), Assumptions::emptyAssump(), pf);
  }
  thm2.setQuantLevel(thm.getQuantLevel());
  return thm2;
}


Theorem CNF_TheoremProducer::ifLiftRule(const Expr& e, int itePos) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getType().isBool(),
		"CNF_TheoremProducer::ifLiftRule("
		"input must be a Predicate: e = " + e.toString()+")");
    CHECK_SOUND(itePos >= 0, "itePos negative"+int2string(itePos));
    CHECK_SOUND(e.arity() > itePos && e[itePos].isITE(),
		"CNF_TheoremProducer::ifLiftRule("
		"input does not have an ITE: e = " + e.toString()+")");
  }
  const Expr& ite = e[itePos];
  const Expr& cond = ite[0];
  const Expr& t1 = ite[1];
  const Expr& t2 = ite[2];

  if(CHECK_PROOFS) {
    CHECK_SOUND(cond.getType().isBool(),
		"CNF_TheoremProducer::ifLiftRule("
		"input does not have an ITE: e = " + e.toString()+")");
  }    

  vector<Expr> k1 = e.getKids();
  Op op(e.getOp());

  k1[itePos] = t1;
  Expr pred1 =  Expr(op, k1);

  k1[itePos] = t2;
  Expr pred2 =  Expr(op, k1);

  Expr resultITE = cond.iteExpr(pred1, pred2);

  Proof pf;
  if (withProof())
    pf = newPf("if_lift_rule", e, d_em->newRatExpr(itePos));
  return newRWTheorem(e, resultITE, Assumptions::emptyAssump(), pf);
}
