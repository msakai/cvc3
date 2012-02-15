/*****************************************************************************/
/*!
 * \file theory_core.cpp
 * 
 * Author: Clark Barrett, Vijay Ganesh (CNF converter)
 * 
 * Created: Thu Jan 30 16:57:52 2003
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


#include "command_line_flags.h"
#include "expr.h"
#include "notifylist.h"
#include "pretty_printer.h"
#include "common_proof_rules.h"
#include "parser_exception.h"
#include "typecheck_exception.h"
#include "smtlib_exception.h"
#include "eval_exception.h"
#include "theory_core.h"
#include "expr_transform.h"
#include "core_proof_rules.h"
#include "theorem_manager.h"
#include "translator.h"


using namespace std;


namespace CVC3 {


  //! Implementation of PrettyPrinter class
  /*! \ingroup PrettyPrinting */
  class PrettyPrinterCore: public PrettyPrinter {
  private:
    TheoryCore *d_core;
    //! Disable the default constructor
    PrettyPrinterCore() { }
  public:
    //! Constructor
    PrettyPrinterCore(TheoryCore* core): d_core(core) { }
    ExprStream& print(ExprStream& os, const Expr& e)
    {
      if(e.isString())
	return e.print(os);
      else if (e.isApply())
        return d_core->theoryOf(e)->print(os, e);
      else if(d_core->hasTheory(e.getKind()))
	return d_core->theoryOf(e.getKind())->print(os, e);
      else
	return e.print(os);
    }
  };


  class TypeComputerCore: public ExprManager::TypeComputer {
    TheoryCore *d_core;
  public:
    TypeComputerCore(TheoryCore* core): d_core(core) { }
    void computeType(const Expr& e)
    {
      DebugAssert(!e.isVar(), "Variables should have a type: "+e.toString());
      Theory* i = d_core->theoryOf(e.getKind());
      if (e.isApply()) i = d_core->theoryOf(e);
      i->computeType(e);
      DebugAssert(!e.lookupType().getExpr().isNull(), "Type not set by computeType");
    }
    void checkType(const Expr& e)
    {
      if (!e.isType()) throw Exception
          ("Tried to use non-type as a type: "+e.toString());
      d_core->theoryOf(e)->checkType(e);
      e.setValidType();
    }
  };


  ostream& operator<<(ostream& os, const NotifyList& l)
  {
    os << "NotifyList(\n";
    for(size_t i=0,iend=l.size(); i<iend; ++i) {
      os << "[" << l.getTheory(i)->getName() << ", " << l.getExpr(i) << "]\n";
    }
    return os << ")";
  }


}


using namespace CVC3;


/*****************************************************************************/
/*
 * Private helper functions
 */
/*****************************************************************************/


IF_DEBUG(
bool TheoryCore::isSorted(const vector<Expr>& v)
{
  Expr prev;
  for(vector<Expr>::const_iterator i=v.begin(), iend=v.end(); i!=iend;
      prev = *i, ++i) {
    if(prev.isNull()) continue;
    if(!(prev < *i)) return false;
  }
  return true;
}
)


void TheoryCore::intersect(const vector<Expr>& a, const vector<Expr>& b,
                           vector<Expr>& res)
{
  DebugAssert(isSorted(a) && isSorted(b), "intersect()");
  size_t i(0), j(0), iend(a.size()), jend(b.size());
  while(i<iend && j<jend) {
    if(a[i] == b[j]) {
      res.push_back(a[i]);
      i++; j++;
    } else if(a[i] < b[j]) i++;
    else j++; // a[i] > b[j]
  }
}


void TheoryCore::difference(const vector<Expr>& a, const vector<Expr>& b,
                            vector<Expr>& res)
{
  DebugAssert(isSorted(a) && isSorted(b), "difference()");
  size_t i(0), j(0), iend(a.size()), jend(b.size());
  while(i < iend) {
    if(j >= jend) { res.push_back(a[i]); i++; }
    else if(a[i]==b[j]) { i++; j++; }
    else if(a[i]<b[j]) { res.push_back(a[i]); i++; }
    else j++; // a[i] > b[j]
  }
}


bool TheoryCore::processFactQueue(EffortLevel effort)
{
  Theorem thm;
  int i;
  bool lemmasAdded = false;
  do {
    processUpdates();
    while (!d_queue.empty() && !d_inconsistent) {
      thm = d_queue.front();
      d_queue.pop();
      assertFactCore(thm);
      if (d_inconsistent) {
        d_update_thms.clear();
        d_update_data.clear();
        break;
      }
      processUpdates();
    }
    if (d_inconsistent) {
      while(d_queue.size()) d_queue.pop();
      d_queueSE.clear();
      return false;
    }
    // Flush search engine queue inside the main loop; search engine
    // may add new facts to d_queue in the process.
    if(d_queue.empty()) {
      // The queue may be emptied in the process due to
      // setInconsistent() call from the SearchEngine.  Monitor it at
      // every iteration.
      while(!d_queueSE.empty()) {
	// Copy a Theorem by value, to guarantee valid reference down
	// the call chain
        lemmasAdded = true;
	Theorem thm(d_queueSE.back());
	d_queueSE.pop_back();
        d_coreSatAPI->addLemma(thm);
      }
      if (effort > LOW) {
        for(i=0; d_queue.empty() && i<getNumTheories() && !d_inconsistent; ++i) {
          d_theories[i]->checkSat(effort == FULL && !lemmasAdded);
        }
      }
    }
  } while (!d_queue.empty());
  return lemmasAdded;
}


void TheoryCore::processNotify(const Theorem& e, NotifyList *L)
{
  DebugAssert(L, "Expected non-NULL notify list");
  for(unsigned k = 0; k < L->size() && !d_inconsistent; ++k) {
    L->getTheory(k)->update(e, L->getExpr(k));
  }
}


Theorem TheoryCore::simplify(const Expr& e)
{
  DebugAssert(d_simpStack.count(e) == 0, "TheoryCore::simplify: loop detected over e =\n"
	      +e.toString());
  DebugAssert(d_simpStack.size() < 10000,
	      "TheoryCore::simplify: too deep recursion depth");
  IF_DEBUG(d_simpStack[e] = true);
  if(e.hasFind()) {
    DebugAssert(find(e).getRHS().hasFind() &&
                find(e).getRHS().isTerm() ||
                find(e).getRHS().isTrue() ||
                find(e).getRHS().isFalse(), "Unexpected find pointer");
    IF_DEBUG(d_simpStack.erase(e));
    return find(e);
  }

  if(e.validSimpCache()) {
    IF_DEBUG(d_simpStack.erase(e));
    return e.getSimpCache();
  }

  Theorem thm;
  if (e.isVar()) {
    thm = rewriteCore(e);
  }
  else if (e.isApply()) {
    thm = rewriteCore(theoryOf(e.getOpKind())->simplifyOp(e));
  }
  else {
    thm = rewriteCore(theoryOf(e.getKind())->simplifyOp(e));
  }

  const Expr& e2 = thm.getRHS();
#ifdef DEBUG
  if (!e2.isTerm() || !e2.hasFind()) {
    // The rewriter should guarantee that all of its children are simplified.
    for (int k=0; k<e2.arity(); ++k) {
      Expr simplified(simplify(e2[k]).getRHS());
      DebugAssert(e2[k]==simplified,"Simplify Error 1:\n e2[k="+int2string(k)
                  +"] = "
                  +e2[k].toString() + "\nSimplified = "
                  +simplified.toString()
                  +"\ne2 = "+e2.toString());
    }
  }
  Expr rewritten(rewriteCore(e2).getRHS());
  DebugAssert(e2==rewritten,"Simplify Error 2: e2 = \n"
              +e2.toString() + "\nSimplified rewritten = \n"
              +rewritten.toString());
#endif
  e.setSimpCache(thm);
  if (e != e2 && !e2.hasFind()) {
    e2.setSimpCache(reflexivityRule(e2));
  }
  IF_DEBUG(d_simpStack.erase(e));
  return thm;
}


Theorem TheoryCore::rewriteCore(const Theorem& e)
{
  DebugAssert(e.isRewrite(),
	      "rewriteCore(thm): not equality or iff:\n  " + e.toString());
  return transitivityRule(e, rewriteCore(e.getRHS()));
}


/* Recurse through s looking for atomic formulas (or terms in the case of
 * then/else branches of ite's) and use the notifylist mechanism to indicate
 * that the atomic formula e depends on these atomic formulas and terms.  Used
 * by registerAtom. */
void TheoryCore::setupSubFormulas(const Expr& s, const Expr& e,
                                  const Theorem& thm)
{
  if (s.isAtomic()) {
    setupTerm(s, theoryOf(s), thm);
    s.addToNotify(this, e);
  }
  else if (s.isAbsAtomicFormula()) {
    setupTerm(s, theoryOf(s), thm);
    for (int i = 0; i < s.arity(); ++i) {
      s[i].addToNotify(this, e);
    }
    if (s != e) s.addToNotify(this, e);
  }
  else {
    for (int i = 0; i < s.arity(); ++i) {
      setupSubFormulas(s[i], e, thm);
    }
  }
}


void TheoryCore::processUpdates()
{
  Theorem e;
  Expr d;
  DebugAssert(d_update_thms.size() == d_update_data.size(),
              "Expected same size");
  while (!d_update_thms.empty()) {
    if (d_inconsistent) {
      d_update_thms.clear();
      d_update_data.clear();
      break;
    }
    e = d_update_thms.back();
    d_update_thms.pop_back();
    d = d_update_data.back();
    d_update_data.pop_back();

    DebugAssert(d.isAbsAtomicFormula(), "Expected atomic formula");
    Theorem thm = simplify(d);
    if (thm.getRHS().isTrue()) {
      setFindLiteral(d_commonRules->iffTrueElim(thm));
    }
    else if (thm.getRHS().isFalse()) {
      setFindLiteral(d_commonRules->iffFalseElim(thm));
    }
    else {
      DebugAssert(e.isRewrite(), "Unexpected theorem in TheoryCore::update");
      if (e.getRHS().getType().isBool()) continue;
      find(e.getRHS()).getRHS().addToNotify(this, d);
      if (thm.getRHS().isAbsAtomicFormula()) thm.getRHS().addToNotify(this, d);
    }
  }
}


void TheoryCore::assertFactCore(const Theorem& e)
{
  IF_DEBUG(string indentStr(getCM()->scopeLevel(), ' '));
  TRACE("assertFactCore", indentStr, "AssertFactCore: ", e.getExpr().toString(PRESENTATION_LANG));

  const Expr& e2 = e.getExpr();
  Theorem equiv = simplify(e2);

  Theorem estarThm(iffMP(e, equiv));
  Expr estar = estarThm.getExpr();

  // Make sure originally asserted atomic formulas have a find pointer
  if(e2 != estar && !e2.isTrue() && e2.isAbsLiteral())
    setFindLiteral(e);
  
  if(estar.isAnd()) {
    for(int i=0,iend=estar.arity(); i<iend && !d_inconsistent; ++i)
      assertFactCore(d_commonRules->andElim(estarThm, i));
    return;
  }

  if (estar.isAbsLiteral()) {
    if (estar.isEq()) {
      // Notify the search engine
      Theorem solvedThm(solve(estarThm));
      // Search engine doesn't have to know about estar at this point
      if(estar != solvedThm.getExpr()) setFindLiteral(estarThm);
      assertEqualities(solvedThm);
    }
    else if (estar.isFalse()) {
      IF_DEBUG(debugger.counter("conflicts from simplifier")++);
      setInconsistent(estarThm);
    }
    else if (!estar.isTrue()) {
      assertFormula(estarThm);
    }
  } else {
    // Notify the search engine
    enqueueSE(estarThm);
  }

  DebugAssert(!e2.isAbsLiteral() || e2.hasFind()
	      || (e2.isNot() && e2[0].hasFind()),
	      "assertFactCore: e2 = "+e2.toString());
  DebugAssert(!estar.isAbsLiteral() || estar.hasFind()
	      || (estar.isNot() && estar[0].hasFind()),
	      "assertFactCore: estar = "+estar.toString());
}


void TheoryCore::assertFormula(const Theorem& thm)
{
  const Expr& e = thm.getExpr();
  DebugAssert(e.isAbsLiteral(),"assertFormula: nonliteral asserted:\n  "
              +thm.toString());
#ifdef DEBUG
  std::stringstream ss;
  ss<<getCM()->scopeLevel();
  std::string temp;
  ss>>temp;
  TRACE("asserts","Assert: ", temp+"|L| ", e.toString(PRESENTATION_LANG));
#endif
  Theory* i = theoryOf(e);
  // (Dis)equalities should also be asserted to the theories of
  // their types for concrete model generation 
  Theory* i2(NULL);
  // Treat disequality as a separate theory, so that terms are
  // reported as shared
  //  if(e.isNot() && e[0].isEq())
  //    setupTerm(e, this);
  //  else
  setupTerm(e,i,thm);

  // Use find to force af to rewrite to TRUE and NOT af to rewrite to FALSE,
  // where af is an atomic formula.  If af is an equality, make sure its lhs
  // is greater than its rhs so the simplifier will be able to use the find.
  DebugAssert(!e.isNot() || (!e.hasFind() && !e[0].hasFind()),
              "Expected negated argument to assertFormula to not have find");
  setFindLiteral(thm);
  Theorem thm2;
  if (e.isNot() && e[0].isEq()) {
    // Save the disequality for later processing
    e[0][0].addToNotify(this, e);
    e[0][1].addToNotify(this, e);

    // For concrete model generation
    i2 = theoryOf(getBaseType(e[0][0]).getExpr()); 

    if(e[0][0] < e[0][1]) {
      Expr e2 = e[0][1].eqExpr(e[0][0]);
      DebugAssert(!e2.hasFind(), "already has find");
      thm2 = transitivityRule(d_commonRules->rewriteUsingSymmetry(e2),
                              d_commonRules->notToIff(thm));
      setFindLiteral(d_commonRules->iffFalseElim(thm2));
    }
  }
  else {
    if(e.isEq() && e[0] < e[1]) {
      Expr e2 = e[1].eqExpr(e[0]);
      if (!e2.hasFind()) {
        thm2 = transitivityRule(d_commonRules->rewriteUsingSymmetry(e2),
                                d_commonRules->iffTrue(thm));
        setFindLiteral(d_commonRules->iffTrueElim(thm2));
      }
    }
  }

  // Do not send existential quantifiers to DPs; skolemize them and
  // notify the Search Engine about it.
  if(thm.getExpr().isExists())
    enqueueFact(d_commonRules->skolemize(thm));
  else {
    i->assertFact(thm);
    if(i2 != NULL && i != i2) {
      IF_DEBUG(debugger.counter("assertFact(diseq) by type")++);
      i2->assertFact(thm);
    }
  }
}


Theorem TheoryCore::rewriteCore(const Expr& e)
{
  if (e.hasFind()) {
    return find(e);
  }
  if (e.isRewriteNormal()) {
    IF_DEBUG(
      // Check that the RewriteNormal flag is set properly.  Note that we
      // assume theory-specific rewrites are idempotent
      e.clearRewriteNormal();
      Expr rewritten(rewriteCore(e).getRHS());
      e.setRewriteNormal(); // Restore the flag
      DebugAssert(rewritten == e, 
		  "Expected no change: e = " + e.toString()
		  +"\n rewriteCore(e) = "+rewritten.toString());
    )
    return reflexivityRule(e);
  }
  switch (e.getKind()) {
    case EQ:
      if (e[0] < e[1])
        return rewriteCore(d_commonRules->rewriteUsingSymmetry(e));
      else if (e[0] == e[1])
        return d_commonRules->rewriteReflexivity(e);
      break;
    case NOT:
      if (e[0].isNot())
        return rewriteCore(d_commonRules->rewriteNotNot(e));
      break;
    default:
      break;
  }
  Theorem thm = theoryOf(e)->rewrite(e);
  const Expr& e2 = thm.getRHS();

  // Theory-specific rewrites for equality should ensure that lhs >= rhs, or
  // there is danger of an infinite loop.
  DebugAssert(!e2.isEq() || e2[0] >= e2[1],
	      "theory-specific rewrites for equality should ensure lhs >= rhs");
  if (e != e2) {
    thm = rewriteCore(thm);
  }
  return thm;
}


void TheoryCore::setFindLiteral(const Theorem& thm)
{
  const Expr& e = thm.getExpr();
  NotifyList* L;
  if (e.isNot()) {
    if (!e[0].hasFind()) {
      Theorem findThm = d_commonRules->notToIff(thm);
      e[0].setFind(findThm);
      if (e[0].isRegisteredAtom()) {
        DebugAssert(!e.isImpliedLiteral(), "Should be new implied lit");
        e.setImpliedLiteral();
        d_impliedLiterals.push_back(thm);
      }
      d_em->invalidateSimpCache();
      L = e[0].getNotify();
      if (L) processNotify(findThm, L);
    } 
  }
  else if (!e.hasFind()) {
    Theorem findThm = d_commonRules->iffTrue(thm);
    e.setFind(findThm);
    if (e.isRegisteredAtom()) {
      DebugAssert(!e.isImpliedLiteral(), "Should be new implied lit");
      e.setImpliedLiteral();
      d_impliedLiterals.push_back(thm);
    }
    d_em->invalidateSimpCache();
    L = e.getNotify();
    if (L) processNotify(findThm, L);
  }
}


Theorem TheoryCore::rewriteIte(const Expr& e)
{
  if (e[0].isTrue())
    return d_rules->rewriteIteTrue(e);
  if (e[0].isFalse())
    return d_rules->rewriteIteFalse(e);
  if (e[1] == e[2])
    return d_rules->rewriteIteSame(e);
  // This results in exponential blowup
//   if(!isTerm(e1) && !isTerm(e2))
//     return d_commonRules->rewriteIteBool(c, e1, e2);
  // Default case: no rewrite
  return reflexivityRule(e);
}


Theorem TheoryCore::rewriteLitCore(const Expr& e)
{
  switch (e.getKind()) {
    case EQ:
      if (e[0] == e[1])
        return d_commonRules->rewriteReflexivity(e);
      else if (e[0] < e[1])
        return d_commonRules->rewriteUsingSymmetry(e);
      break;
    case NOT:
      if (e[0].isTrue())
        return d_commonRules->rewriteNotTrue(e);
      else if (e[0].isFalse())
        return d_commonRules->rewriteNotFalse(e);
      else if (e[0].isNot())
        return d_commonRules->rewriteNotNot(e);
      break;
    default:
      DebugAssert(false,
		  "TheoryCore::rewriteLitCore("
		  + e.toString()
		  + "): Not implemented");
      break;
  }
  return reflexivityRule(e);
}


Theorem TheoryCore::rewriteN(const Expr& e, int n)
{
  if(n <= 0) return reflexivityRule(e);
  if(theoryOf(e) != this) return reflexivityRule(e);
  if(n==1) return rewrite(e);
  vector<Theorem> thms;
  vector<unsigned> changed;
  for(int i=0; i<e.arity(); ++i) {
    Theorem thm = rewriteN(e[i], n-1);
    if(e[i] != thm.getRHS()) {
      thms.push_back(thm);
      changed.push_back(i);
    }
  }
  Theorem res;
  if(changed.size()>0) {
    res = substitutivityRule(e, changed, thms);
    res = transitivityRule(res, rewrite(res.getRHS()));
  } else {
    res = rewrite(e);
  }
  return res;
}


/*!
 * Fill in the copy of the equality queue with single equalities by
 * processing the input 'eq', which can be an equality, a conjunction
 * of equalities, or an existential quantifier of the above.
 */
bool TheoryCore::processEquality(const Theorem& thm, ExprMap<Theorem>& q)
{
  const Expr& e = thm.getExpr();
  bool res(false);

  switch(e.getKind()) {
  case FALSE_EXPR:
    IF_DEBUG(debugger.counter("conflicts from solver")++);
    setInconsistent(thm);
    res = true;
    break;
  case EXISTS:
    // Skolemize the quantifier and expect an equality or a
    // conjunction of equalities inside
    res = processEquality(d_commonRules->skolemize(thm), q);
    break;
  case AND: 
    for(int i=0, iend=e.arity(); i!=iend; ++i)
      if(res = processEquality(d_commonRules->andElim(thm, i), q)) break;
    break;
  case EQ:
    // find(e0) != e1 && find(e1) != e0
    if(find(e[0]).getRHS() != e[1] && e[0] != find(e[1]).getRHS()) {
      DebugAssert(e[0] != e[1], "processEquality: e = "+e.toString());
      DebugAssert(!e[1].hasFind() || find(e[1]).getRHS() == e[1],
		  "processEquality: e = "+e.toString()
		  +"\nfind(e[1]) = "+find(e[1]).getRHS().toString());
//       DebugAssert(!e[0].subExprOf(e[1]), "processEquality: e = "+e.toString());
      q[e] = thm;
    } else if(find(e).getRHS().isFalse()) {
      IF_DEBUG(debugger.counter("conflicts from find pointers")++);
      setInconsistent(d_commonRules->contradictionRule(thm,
                        d_commonRules->iffFalseElim(find(e))));
      res = true;
    }
    break;
  default:
    DebugAssert(false,
		"TheoryCore::processEquality(): bad input:\n "
		+thm.toString());
  }
  return res;
}


void TheoryCore::enqueueSE(const Theorem& thm)
{
  DebugAssert(d_inAddFact || d_inCheckSATCore || d_inRegisterAtom, "enqueueSE()");
  d_queueSE.push_back(thm);
}


Theorem TheoryCore::getModelValue(const Expr& e)
{
  ExprHashMap<Theorem>::iterator i=d_varAssignments.find(e),
    iend=d_varAssignments.end();
  if(i!=iend) return (*i).second;
  else return find(e);
}


//! An auxiliary recursive function to process COND expressions into ITE
Expr TheoryCore::processCond(const Expr& e, int i)
{
  DebugAssert(i < e.arity()-1, "e = "+e.toString()+", i = "+int2string(i));
  if(i == e.arity()-2) {
    if(e[i].getKind() == RAW_LIST && e[i].arity() == 2
       && e[i+1].getKind() == RAW_LIST  && e[i+1].arity() == 2
       && e[i+1][0].getKind() == ID && e[i+1][0][0].getString() == "ELSE") {
      Expr c(parseExpr(e[i][0]));
      Expr e1(parseExpr(e[i][1]));
      Expr e2(parseExpr(e[i+1][1]));
      return c.iteExpr(e1,e2);
    }
  } else {
    if(e[i].getKind() == RAW_LIST && e[i].arity() == 2
       && e[i+1].getKind() == RAW_LIST  && e[i+1].arity() == 2) {
      Expr c(parseExpr(e[i][0]));
      Expr e1(parseExpr(e[i][1]));
      Expr e2(processCond(e, i+1));
      return c.iteExpr(e1,e2);
    }
  }
  throw ParserException("Parse Error: bad COND expression: "+e.toString());
}


bool TheoryCore::isBasicKind(int kind)
{
  switch (kind) {
    case VARDECLS:
    case LETDECLS:
    case HELP:
    case DUMP_PROOF:
    case DUMP_ASSUMPTIONS:
    case DUMP_SIG:
    case DUMP_TCC:
    case DUMP_TCC_ASSUMPTIONS:
    case DUMP_TCC_PROOF:
    case DUMP_CLOSURE:
    case DUMP_CLOSURE_PROOF:
    case WHERE:
    case ASSERTIONS:
    case ASSUMPTIONS:
    case COUNTEREXAMPLE:
    case COUNTERMODEL:
    case ASSERT:
    case PRINT:
    case QUERY:
    case CHECKSAT:
    case CONTINUE:
    case RESTART:
    case TRACE:
    case ECHO:
    case UNTRACE:
    case VARLIST:
    case FORGET:
    case GET_TYPE:
    case IFF:
    case IMPLIES:
    case TYPEDEF:
    case OPTION:
    case AND:
    case OR:
    case XOR:
    case NOT:
    case EQ:
    case CALL:
    case TRANSFORM:
    case CHECK_TYPE:
    case VARDECL:
    case GET_CHILD:
    case SUBSTITUTE:
    case SEQ:
    case DBG:
    case PUSH:
    case POP:
    case POPTO:
    case PUSH_SCOPE:
    case POP_SCOPE:
    case POPTO_SCOPE:
    case LETDECL:
    case ELSE:
    case CONTEXT:
      return true;
    default:
      break;
  }
  return false;
}


TheoryCore::TheoryCore(ContextManager* cm,
                       ExprManager* em,
                       TheoremManager* tm,
                       Translator* translator,
                       const CLFlags& flags,
                       Statistics& statistics)
  : Theory(), d_cm(cm), d_tm(tm), d_flags(flags), d_statistics(statistics),
    d_translator(translator),
    d_inconsistent(cm->getCurrentContext(), false, 0), 
    d_incomplete(cm->getCurrentContext()),
    d_incThm(cm->getCurrentContext()),
    d_terms(cm->getCurrentContext()),
    d_predicates(cm->getCurrentContext()),
    d_vars(cm->getCurrentContext()),
    d_sharedTerms(cm->getCurrentContext()),
    d_solver(NULL),
    d_simplifyInPlace(false),
    d_currentRecursiveSimplifier(NULL),
    d_resourceLimit(0),
#ifdef DEBUG
    d_inCheckSATCore(false), d_inAddFact(false),
    d_inRegisterAtom(false),
#endif
    d_notifyObj(this, cm->getCurrentContext()),
    d_impliedLiterals(cm->getCurrentContext()),
    d_impliedLiteralsIdx(cm->getCurrentContext(), 0, 0),
    d_coreSatAPI(NULL)
{
  d_em = em;
  // Since we are in the middle of creating TheoryCore, we set the pointer to
  // TheoryCore in the Theory base class ourselves.
  d_theoryCore = this;
  d_commonRules = tm->getRules();
  d_name = "Core";
  d_theoryUsed = false;

  d_rules = createProofRules(tm);
  d_printer = new PrettyPrinterCore(this);
  d_typeComputer = new TypeComputerCore(this);
  d_em->registerTypeComputer(d_typeComputer);
  d_exprTrans = new ExprTransform(this);

  // Register the pretty-printer
  d_em->registerPrettyPrinter(*d_printer);

  // for (int i = 0; i < LAST_KIND; ++i) d_theoryMap[i] = NULL;

  vector<int> kinds;
  kinds.push_back(RAW_LIST);
  kinds.push_back(BOOLEAN);
  kinds.push_back(ANY_TYPE);
  kinds.push_back(SUBTYPE);
  kinds.push_back(STRING_EXPR);
  kinds.push_back(ID);
  kinds.push_back(TRUE_EXPR);
  kinds.push_back(FALSE_EXPR);
  kinds.push_back(UCONST);
  kinds.push_back(BOUND_VAR);
  kinds.push_back(SKOLEM_VAR);
  kinds.push_back(EQ);
  kinds.push_back(NEQ);
  kinds.push_back(ECHO);
  kinds.push_back(DBG);
  kinds.push_back(TRACE);
  kinds.push_back(UNTRACE);
  kinds.push_back(OPTION);
  kinds.push_back(HELP);
  kinds.push_back(AND);
  kinds.push_back(OR);
  kinds.push_back(IFTHEN);
  kinds.push_back(IF);
  kinds.push_back(ELSE);
  kinds.push_back(COND);
  kinds.push_back(XOR);
  kinds.push_back(NOT);
  kinds.push_back(ITE);
  kinds.push_back(IFF);
  kinds.push_back(IMPLIES);
  kinds.push_back(APPLY);
  // For printing LET expressions (in DAG printing mode)
  kinds.push_back(LET);
  kinds.push_back(LETDECLS);
  kinds.push_back(LETDECL);
  // For printing raw parsed quantifier expressions
  kinds.push_back(VARLIST);
  kinds.push_back(VARDECLS);
  kinds.push_back(VARDECL);

  // Type declarations and definitions
  kinds.push_back(TYPE);
  // For printing type declarations (or definitions)
  kinds.push_back(CONST);

  kinds.push_back(TYPEDEF);
  kinds.push_back(DEFUN);
  // Printing proofs
  kinds.push_back(PF_APPLY);
  kinds.push_back(PF_HOLE);
  // Register commands for pretty-printing.  Currently, only ASSERT
  // needs to be printed.
  kinds.push_back(ASSERT);
  kinds.push_back(QUERY);
  kinds.push_back(PRINT);

  kinds.push_back(DUMP_PROOF);
  kinds.push_back(DUMP_ASSUMPTIONS);
  kinds.push_back(DUMP_SIG);
  kinds.push_back(DUMP_TCC);
  kinds.push_back(DUMP_TCC_ASSUMPTIONS);
  kinds.push_back(DUMP_TCC_PROOF);
  kinds.push_back(DUMP_CLOSURE);
  kinds.push_back(DUMP_CLOSURE_PROOF);
  kinds.push_back(TRANSFORM);
  kinds.push_back(CALL);
  kinds.push_back(WHERE);
  kinds.push_back(ASSERTIONS);
  kinds.push_back(ASSUMPTIONS);
  kinds.push_back(COUNTEREXAMPLE);
  kinds.push_back(COUNTERMODEL);
  kinds.push_back(PUSH);
  kinds.push_back(POP);
  kinds.push_back(POPTO);
  kinds.push_back(PUSH_SCOPE);
  kinds.push_back(POP_SCOPE);
  kinds.push_back(POPTO_SCOPE);
  kinds.push_back(CONTEXT);
  kinds.push_back(FORGET);
  kinds.push_back(GET_TYPE);
  kinds.push_back(CHECK_TYPE);
  kinds.push_back(GET_CHILD);
  kinds.push_back(SUBSTITUTE);
  kinds.push_back(SEQ);
  kinds.push_back(THEOREM_KIND);

  
  kinds.push_back(AND_R);
  kinds.push_back(IFF_R);
  kinds.push_back(ITE_R);

  registerTheory(this, kinds);
}


TheoryCore::~TheoryCore()
{
  delete d_exprTrans;
  delete d_rules;
  delete d_typeComputer;
  d_em->unregisterPrettyPrinter();
  delete d_printer;
}


Theorem TheoryCore::getTheoremForTerm(const Expr& e)
{
// <<<<<<< theory_core_sat.cpp
//   //  DebugAssert(e.hasFind(), "getTheoremForTerm called on term without find");
//   CDMap<Expr, Theorem>::iterator i = d_termTheorems.find(e);
//   if( i == d_termTheorems.end()){
//    TRACE("quantlevel", "getTheoremForTerm: no theorem found: ", e , "");
//    Theorem nul;
//    return nul;
//   }
//   //  DebugAssert(i != d_termTheorems.end(), "getTheoremForTerm: no theorem found");
// =======
  DebugAssert(e.hasFind() || e.isStoredPredicate(), "getTheoremForTerm called on invalid term");
  hash_map<Expr, Theorem>::iterator i = d_termTheorems.find(e);
  DebugAssert(i != d_termTheorems.end(), "getTheoremForTerm: no theorem found");
// >>>>>>> 1.19
  return (*i).second;
}


unsigned TheoryCore::getQuantLevelForTerm(const Expr& e)
{
// <<<<<<< theory_core_sat.cpp
//   //  if (!e.hasFind()) return 0;
// =======
  if (!e.hasFind() && !e.isStoredPredicate()) {
    TRACE("quantlevel", "get 0 ", e , "");
    return 0;
  }
// >>>>>>> 1.19
  Theorem thm = getTheoremForTerm(e);
  if (thm.isNull()) {
    // Must be from user-registered atom
    TRACE("quantlevel", "get 0-1 ", e , "");
    return 0;
  }
  return thm.getQuantLevel();
}


///////////////////////////////////////////////////////////////////////////////
// Theory interface implementaion                                            //
///////////////////////////////////////////////////////////////////////////////


void TheoryCore::assertFact(const Theorem& e)
{
  DebugAssert(e.getExpr().unnegate().getKind() == SKOLEM_VAR ||
              e.getExpr().unnegate().getKind() == UCONST,
              "TheoryCore::assertFact("+e.toString()+")");
}


Theorem TheoryCore::rewrite(const Expr& e)
{
  Theorem thm;
  switch (e.getKind()) {
    case TRUE_EXPR:
    case FALSE_EXPR:
    case UCONST:
    case BOUND_VAR:
    case SKOLEM_VAR:
      thm = reflexivityRule(e);
      break; // do not rewrite
    case LETDECL:
      // Replace LETDECL with its definition.  The
      // typechecker makes sure it's type-safe to do so.
      thm = d_rules->rewriteLetDecl(e);
      break;
    case APPLY:
      //TODO: this is a bit of a hack
      if (e.getOpKind() == LAMBDA)
        thm = theoryOf(LAMBDA)->rewrite(e);
      else thm = reflexivityRule(e);
      break;
    case EQ:
    case NOT:
      thm = rewriteLitCore(e);
      break;
    case IMPLIES: {
      thm = d_rules->rewriteImplies(e);
      const Expr& rhs = thm.getRHS();
      // rhs = OR(!e1, e2).  Rewrite !e1, then top-level OR().
      DebugAssert(rhs.isOr() && rhs.arity() == 2,
		  "TheoryCore::rewrite[IMPLIES]: rhs = "+rhs.toString());
      Theorem rw = rewriteCore(rhs[0]);
      if(rw.getLHS() != rw.getRHS()) {
	vector<unsigned> changed;
	vector<Theorem> thms;
	changed.push_back(0);
	thms.push_back(rw);
	rw = substitutivityRule(rhs, changed, thms);
	// Simplify to the find pointer of the result
	rw = transitivityRule(rw, find(rw.getRHS()));
	// Now rw = Theorem(rhs = rhs')
	rw = transitivityRule(rw, rewrite(rw.getRHS()));
      } else
	rw = rewrite(rhs);
      thm = transitivityRule(thm, rw);
      //       thm = transitivityRule(thm, simplify(thm.getRHS()));
      break;
    }
    case XOR: {
      thm = d_commonRules->xorToIff(e);
      thm = transitivityRule(thm, simplify(thm.getRHS()));
      break;
    }
    case IFF: {
      thm = d_commonRules->rewriteIff(e);
      Expr e1 = thm.getRHS();
      // The only time we need to rewrite the result (e1) is when
      // e==(FALSE<=>e[1]) or (e[1]<=>FALSE), so e1==!e[1].
      if (e != e1 && e1.isNot())
	thm = transitivityRule(thm, rewriteCore(e1));
      break;
    }
    case ITE:
      if (e[0].isTrue())
	thm = d_rules->rewriteIteTrue(e);
      else if (e[0].isFalse())
	thm = d_rules->rewriteIteFalse(e);
      else if (e[1] == e[2])
	thm = d_rules->rewriteIteSame(e);
      else if (getFlags()["un-ite-ify"].getBool()) {
	// undo the rewriting of Boolean connectives to ITEs.
	// helpful for examples converted from SVC.
	// must rewrite again because we might create expressions
	// that can be further rewritten, and we must normalize.
	if (e[1].isFalse() && e[2].isTrue())
	  thm = rewriteCore(d_rules->rewriteIteToNot(e));
	else if (e[1].isTrue())
	  thm = rewriteCore(d_rules->rewriteIteToOr(e));
	else if (e[2].isFalse())
	  thm = rewriteCore(d_rules->rewriteIteToAnd(e));
	else if (e[2].isTrue())
	  thm = rewriteCore(d_rules->rewriteIteToImp(e));
	else if (e[1] == e[2].negate())
	  thm = rewriteCore(d_rules->rewriteIteToIff(e));
	else thm = reflexivityRule(e);
      }
      else if(getFlags()["ite-cond-simp"].getBool()) {
	thm = d_rules->rewriteIteCond(e);
	if(e != thm.getRHS())
	  thm = transitivityRule(thm, simplify(thm.getRHS()));
      }
      else thm = reflexivityRule(e);    
      break;
    case AND: {
      thm = rewriteAnd(e);
      Expr ee = thm.getRHS();
      break;
    }
    case OR: {
      thm = rewriteOr(e);
      Expr ee = thm.getRHS();
      break;
    }
      // Quantifiers
    case FORALL:
    case EXISTS:
      thm = d_commonRules->reflexivityRule(e);      
      break;
      // don't need to rewrite these
    case AND_R:
    case IFF_R:
    case ITE_R:
      thm = reflexivityRule(e);
      break;    
    default:
      DebugAssert(false,
		  "TheoryCore::rewrite("
		  + e.toString() + " : " + e.getType().toString()
		  + "): Not implemented");
      break;
  }

  DebugAssert(thm.getLHS() == e, "TheoryCore::rewrite("+e.toString()
	      +") = "+thm.getExpr().toString());
  
  Expr rhs = thm.getRHS();
  // Advanced Boolean rewrites
  switch(rhs.getKind()) {
  case AND:
    if(getFlags()["simp-and"].getBool()) {
      Theorem tmp(reflexivityRule(rhs));
      for(int i=0, iend=rhs.arity(); i<iend; ++i) {
	tmp = transitivityRule
	  (tmp, d_rules->rewriteAndSubterms(tmp.getRHS(), i));
      }
      if(tmp.getRHS() != rhs) { // Something changed: simplify recursively
	thm = transitivityRule(thm, tmp);
	thm = transitivityRule(thm, simplify(thm.getRHS()));
	rhs = thm.getRHS();
      }
    }
    break;
  case OR:
    if(getFlags()["simp-or"].getBool()) {
      Theorem tmp(reflexivityRule(rhs));
      for(int i=0, iend=rhs.arity(); i<iend; ++i) {
	tmp = transitivityRule
	  (tmp, d_rules->rewriteOrSubterms(tmp.getRHS(), i));
      }
      if(tmp.getRHS() != rhs) { // Something changed: simplify recursively
	thm = transitivityRule(thm, tmp);
	thm = transitivityRule(thm, simplify(thm.getRHS()));
	rhs = thm.getRHS();
      }
    }
    break;
  default:
    break;
  }
  if (theoryOf(rhs) == this) {
    // Core rewrites are idempotent (FIXME: are they, still?)
    rhs.setRewriteNormal();
  }  
  return thm;
}


/*! We use the update method of theory core to track registered atomic
 * formulas.  Updates are recorded and then processed by calling processUpdates
 * once all equalities have been processed. */
void TheoryCore::update(const Theorem& e, const Expr& d)
{
  // Disequalities
  if (d.isNot()) {
    const Expr& eq = d[0];
    DebugAssert(eq.isEq(), "Expected equality");
    Theorem thm1(find(eq[0]));
    Theorem thm2(find(eq[1]));
    const Expr& newlhs = thm1.getRHS();
    const Expr& newrhs = thm2.getRHS();
    if (newlhs == newrhs) {
      Theorem thm = find(eq);
      DebugAssert(thm.getRHS().isFalse(), "Expected disequality");

      Theorem leftEqRight = transitivityRule(thm1, symmetryRule(thm2));
      setInconsistent(iffMP(leftEqRight, thm));
    }
    else {
      e.getRHS().addToNotify(this, d);
      // propagate new disequality
      Theorem thm = d_commonRules->substitutivityRule(eq, thm1, thm2);
      if (newlhs < newrhs) {
        thm = transitivityRule(thm, d_commonRules->rewriteUsingSymmetry(thm.getRHS()));
      }
      const Expr& newEq = thm.getRHS();
      DebugAssert(!newEq.hasFind() ||
                  find(newEq).getRHS().isFalse(), "Can only be false");
      if (!newEq.hasFind()) {
        Theorem thm2 = find(eq);
        DebugAssert(thm2.getRHS().isFalse(), "Expected disequality");
        thm2 = transitivityRule(symmetryRule(thm),thm2);
        setFindLiteral(d_commonRules->iffFalseElim(thm2));
      }
    }
  }
  // Registered atoms
  else {
    DebugAssert(d.isRegisteredAtom(), "Expected registered atom");
    if (!d.isImpliedLiteral()) {
      d_update_thms.push_back(e);
      d_update_data.push_back(d);
    }
  }
}


/*****************************************************************************/
/*!
 * Function: TheoryCore::solve
 *
 * Author: Clark Barrett
 *
 * Created: Wed Feb 26 16:17:54 2003
 *
 * This is a generalization of what's in my thesis.  The goal is to rewrite e
 * into an equisatisfiable conjunction of equations such that the left-hand
 * side of each equation is a variable which does not appear as an i-leaf of
 * the rhs, where i is the theory of the primary solver.  Any solution which
 * satisfies this is fine.  "Solvers" from other theories can do whatever they
 * want as long as we eventually reach this form.
 */
/*****************************************************************************/
Theorem TheoryCore::solve(const Theorem& eThm)
{
  const Expr& e = eThm.getExpr();
  Theorem thm;
  Expr e2;
  if (d_solver) {
    thm = d_solver->solve(eThm);
    e2 = thm.getExpr();
    // FIXME: this stops other solvers from being run when arithmetic
    // solves into a system of equations.  This results in
    // INCOMPLETENESS.  In my opinion (Sergey), the correct fix is to
    // allow multiple independent solvers, just like rewriters.
    if (!e2.isEq() || theoryOf(e2) == d_solver) {
      return thm;
    }
  }
  else {
    thm = eThm;
    e2 = e;
  }
  Theory* i = theoryOf(e2);
  Theorem thm2 = i->solve(thm);
  IF_DEBUG(
    // Check that the result is in solved form according to the primary solver
    if (d_solver) {
      e2 = thm2.getExpr();
      if(e2.isEq()) {
	Expr solved(d_solver->solve(thm2).getExpr());
	DebugAssert(solved == e2, "e2 = "+e2.toString()
		    +"\nsolved = "+solved.toString());
      }
      // FIXME: how do we check it for AND and EXISTS?
    }
    );
  return thm2;
}


Theorem TheoryCore::simplifyOp(const Expr& e)
{
  int kind(e.getKind());

  switch(kind) {
  case EQ:
  case IFF:
    if(e[0]==e[1]) {
      IF_DEBUG(debugger.counter("simplified x=x")++);
      return d_commonRules->iffTrue(reflexivityRule(e[0]));
    }
    return Theory::simplifyOp(e);
  case AND:
  case OR: {
    // Stop when a child has this kind
    int endKind = (kind==AND)? FALSE_EXPR : TRUE_EXPR;
    int ar = e.arity();
    // Optimization: before simplifying anything recursively, check if
    // any kid is already TRUE or FALSE, and just return at that point
    int l(0);
    for(; l<ar && e[l].getKind() != endKind; ++l);
    if(l < ar) { // Found TRUE or FALSE: e simplifies to a const
      IF_DEBUG(debugger.counter("simplified AND/OR topdown")++);
      if(kind==AND)
	return rewriteAnd(e);
      else
	return rewriteOr(e);
    }
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    for(int k = 0; k < ar; ++k) {
      // Recursively simplify the kids
      Theorem thm = simplify(e[k]);
      if (thm.getLHS() != thm.getRHS()) {
	if (thm.getRHS().getKind() == endKind) {
	  newChildrenThm.clear();
	  changed.clear();
	  newChildrenThm.push_back(thm);
	  changed.push_back(k);
	  thm = substitutivityRule(e, changed, newChildrenThm);
	  // Simplify to TRUE or FALSE
	  if(kind==AND)
	    thm = transitivityRule(thm, rewriteAnd(thm.getRHS()));
	  else
	    thm = transitivityRule(thm, rewriteOr(thm.getRHS()));
	  IF_DEBUG(debugger.counter("simplified AND/OR: skipped kids")
		   += ar-k-1);
	  return thm;
	} else { // Child simplified to something else
	  newChildrenThm.push_back(thm);
	  changed.push_back(k);
	}
      }
    }
    if(changed.size() > 0)
      return substitutivityRule(e, changed, newChildrenThm);
    break;
  }
  case ITE: {
    DebugAssert(e.arity()==3, "Bad ITE in TheoryCore::simplify(e="
		+e.toString()+")");
    // Optimization: check if the two branches are the same, so we
    // don't have to simplify the condition
    if(e[1]==e[2]) {
      IF_DEBUG(debugger.counter("simplified ITE(c,e,e)")++);
      Theorem res = d_rules->rewriteIteSame(e);
      return transitivityRule(res, simplify(res.getRHS()));
    }
    // First, simplify the conditional
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    Theorem thm = simplify(e[0]);
    if(thm.getLHS() != thm.getRHS()) {
      newChildrenThm.push_back(thm);
      changed.push_back(0);
    }
    Expr cond = thm.getRHS();
    for(int k=1; k<=2; ++k) {
      // If condition value is known, only the appropriate branch
      // needs to be simplified
      if((k==1 && cond.isFalse()) || (k==2 && cond.isTrue())) {
	IF_DEBUG(debugger.counter("simplified ITE: skiped one branch")++);
	continue;
      }
      thm = simplify(e[k]);
      if(thm.getLHS() != thm.getRHS()) {
	newChildrenThm.push_back(thm);
	changed.push_back(k);
      }
    }
    if(changed.size() > 0)
      return substitutivityRule(e, changed, newChildrenThm);
    break;
  }
  case NOT: { // Push negation down
    if(!e.isAbsLiteral() && getFlags()["pushneg"].getBool()) {
      Theorem res = d_exprTrans->pushNegation1(e);
      if(res.getLHS() != res.getRHS())
	// Recurse; there may be shortcuts to take advantage of
	res = transitivityRule(res, simplifyOp(res.getRHS()));
      else {
	res = Theory::simplifyOp(e);
	// Try pushing negation once more
	Theorem thm = d_exprTrans->pushNegation1(res.getRHS());
	if(thm.getLHS() != thm.getRHS()) {
	  thm = transitivityRule(thm, simplify(thm.getRHS()));
	  res = transitivityRule(res, thm);
	}
      }
      return res;
    } else {
      Theorem res = simplify(e[0]);
      if (res.getLHS() != res.getRHS()) {
        return d_commonRules->substitutivityRule(e, res);
      }
    }
    break;
  }
  case IMPLIES: {
    Theorem res = d_rules->rewriteImplies(e);
    return transitivityRule(res, simplifyOp(res.getRHS()));
  }
  default:
    return Theory::simplifyOp(e);
  }
  return reflexivityRule(e);
}


void TheoryCore::checkType(const Expr& e)
{
  switch (e.getKind()) {
    case BOOLEAN:
      if (e.arity() > 0) {
        throw Exception("Ill-formed Boolean type:\n\n"+e.toString());
      }
      break;
    case SUBTYPE: {
        if (e.arity() != 1)
          throw Exception("Ill-formed SUBTYPE expression:\n\n"+e.toString());
        Type t = e[0].getType();
        if (!t.isFunction())
          throw Exception
            ("Non-function argument to SUBTYPE:\n\n"
             +e.toString());
        if (!t[1].isBool())
          throw Exception
            ("Non-predicate argument to SUBTYPE:\n\n"
             +e.toString());
      }
      break;
    case ANY_TYPE: {
      if (e.arity() != 0) {
        throw Exception("Expected no children: "+e.toString());
      }
      break;
    }
    default:
      DebugAssert(false, "Unexpected kind in TheoryCore::checkType"
                  +getEM()->getKindName(e.getKind()));
  }
}


void TheoryCore::computeType(const Expr& e)
{
  switch (e.getKind()) {
    case ITE: {
      Type t1(getBaseType(e[1])), t2(getBaseType(e[2]));
      if (e[0].getType() != boolType())
	throw TypecheckException
	  ("The conditional in IF-THEN-ELSE must be BOOLEAN, but is:\n\n"
	   +e[0].getType().toString()
	   +"\n\nIn the expression:\n\n  "
	   +e.toString());
      if(t1 != t2) {
	throw TypecheckException
	  ("The types of the IF-THEN-ELSE branches do not match.\n"
	   "THEN branch has the type:\n\n  "
	   +e[1].getType().toString()
	   +"\n\nELSE branch has the type:\n\n  "
	   +e[2].getType().toString()
	   +"\n\nIn expression:\n\n  "+e.toString());
      }
      Type res(e[1].getType());
      // If the precise types match in both branches, use it as the
      // result type.
      if(res == e[2].getType()) {
	e.setType(res);
      }
      else
	// Note: setting the base type, since e[1] and e[2] have
	// different exact types, and the base type is a conservative
	// approximation we can easily compute.
	e.setType(t1);
    }
      break;
    case EQ: {
      Type t0(getBaseType(e[0])), t1(getBaseType(e[1]));
      if (t0.isBool() || t1.isBool()) {
	throw TypecheckException
	  ("Cannot use EQ ('=') for BOOLEAN type; use IFF ('<=>') instead.\n"
	   "Error in the following expression:\n"+e.toString());
      }
      if (t0 != t1) {
	throw TypecheckException
	  ("Type mismatch in equality:\n\n LHS type:\n"+t0.toString()
	   +"\n\n RHS type: \n"+t1.toString()
	   +"\n\n in expression: \n"+e.toString());
      }
      e.setType(boolType());
    }
      break;
    case NOT:
    case AND:
    case OR:
    case XOR:
    case IFF:
    case IMPLIES:

    case AND_R:
    case IFF_R:
    case ITE_R:
    
      for (int k = 0; k < e.arity(); ++k) {
	if (e[k].getType() != boolType()) {
	  throw TypecheckException(e.toString());
	}
      }
      e.setType(boolType());
      break;
    case LETDECL: {
      Type varTp(getBaseType(e[0]));
      Type valTp(getBaseType(e[1]));
      if(valTp != varTp) {
	throw TypecheckException("Type mismatch for "+e[0].toString()+":"
				 +"\n  declared: "
				 + varTp.toString()
				 +"\n  derived: "+ valTp.toString());
      }
      e.setType(e[0].getType());
    }
      break;
    case APPLY:
    {
      DebugAssert(e.isApply(), "Should be application");
      DebugAssert(e.arity() > 0, "Expected non-zero arity in APPLY");
      Expr funExpr = e.getOpExpr();
      Type funType = funExpr.getType();

      if(!funType.isFunction()) {
	throw TypecheckException
	  ("Expected function type for:\n\n"
	   + funExpr.toString() + "\n\n but got this: "
	   +funType.getExpr().toString()
	   +"\n\n in function application:\n\n"+e.toString());
      }

      if(funType.arity() != e.arity()+1)
	throw TypecheckException("Type mismatch for expression:\n\n   "
				 + e.toString()
				 + "\n\nFunction \""+funExpr.toString()
				 +"\" expects "+int2string(funType.arity()-1)
				 +" argument"
				 +string((funType.arity()==2)? "" : "s")
				 +", but received "
				 +int2string(e.arity())+".");

      for (int k = 0; k < e.arity(); ++k) {
	Type valType(getBaseType(e[k]));
	if (funType[k] != Type::anyType(d_em) && valType != getBaseType(funType[k])) {
	  throw TypecheckException("Type mismatch for expression:\n\n   "
				   + e[k].toString()
				   + "\n\nhas the following type:\n\n  "
				   + e[k].getType().toString()
				   + "\n\nbut the expected type is:\n\n  "
				   + funType[k].getExpr().toString()
				   + "\n\nin function application:\n\n  "
				   + e.toString());
	}
      }
      e.setType(funType[funType.arity()-1]);
      break;
    }
    default:
      DebugAssert(false,"TheoryCore::computeType(" + e.toString()
		  + "):\nNot implemented");
      break;
  }
}


Type TheoryCore::computeBaseType(const Type& tp)
{
  const Expr& e = tp.getExpr();
  Type res;
  switch(e.getKind()) {
  case SUBTYPE: {
    DebugAssert(e.arity() == 1, "Expr::computeBaseType(): "+e.toString());
    Type lambdaTp = e[0].getType();
    Type lambdaBaseTp = getBaseType(lambdaTp);
    DebugAssert(lambdaBaseTp.isFunction(), 
		"Expr::computeBaseType(): lambdaBaseTp = "
		+lambdaBaseTp.toString()+" in e = "+e.toString());
    res = lambdaBaseTp[0];
    break;
  }
  case BOOLEAN:
  case ANY_TYPE:
    res = tp;
    break;
  case TYPEDEF: // Compute the base type of the definition
    res = getBaseType(Type(e[1]));
    break;
  default:
    DebugAssert(false, "TheoryCore::computeBaseType("+tp.toString()+")");
    res = tp;
  }
  return res;
}


Expr TheoryCore::computeTCC(const Expr& e)
{
  Expr res;
  switch (e.getKind()) {
  case NOT:
    res = getTCC(e[0]);
    break;
  case AND: {
    // ( (tcc(e1) & !e1) \/ ... \/ (tcc(en) & !en) \/ (tcc(e1)&...&tcc(en))
    vector<Expr> tccs;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      tccs.push_back(getTCC(*i));
    vector<Expr> pairs;
    pairs.push_back(rewriteAnd(andExpr(tccs)).getRHS());
    for(size_t i=0, iend=tccs.size(); i<iend; ++i)
      pairs.push_back(rewriteAnd(tccs[i].andExpr(e[i].negate())).getRHS());
    res = rewriteOr(orExpr(pairs)).getRHS();
    break;
  }
  case OR: {
    // ( (tcc(e1) & e1) \/ ... \/ (tcc(en) & en) \/ (tcc(e1)&...&tcc(en))
    vector<Expr> tccs;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      tccs.push_back(getTCC(*i));
    vector<Expr> pairs;
    pairs.push_back(rewriteAnd(andExpr(tccs)).getRHS());
    for(size_t i=0, iend=tccs.size(); i<iend; ++i)
      pairs.push_back(rewriteAnd(tccs[i].andExpr(e[i])).getRHS());
    res = rewriteOr(orExpr(pairs)).getRHS();
    break;
  }
  case ITE: {
    Expr tcc1(getTCC(e[1])), tcc2(getTCC(e[2]));
    // Optimize: if TCCs on both branches are the same, skip the ITE
    Expr tccITE((tcc1 == tcc2)? tcc1 : e[0].iteExpr(tcc1, tcc2));
    res = rewriteAnd(getTCC(e[0]).andExpr(tccITE)).getRHS();
    break;
  }
  case IMPLIES:
    res = getTCC(e[0].negate().orExpr(e[1]));
    break;
  case APPLY: {
    Theory* i = theoryOf(e);
    if (i != this) return i->computeTCC(e);
    // fall through
  }
  default: // All the other operators are strict
    res = Theory::computeTCC(e);
    break;
  }
  return res;
}


Expr TheoryCore::computeTypePred(const Type& t, const Expr& e)
{
  Expr tExpr = t.getExpr();
  switch(tExpr.getKind()) {
    case SUBTYPE: {
      Expr pred = tExpr[0];
      const Type& argTp = pred.lookupType()[0];
      return Expr(pred.mkOp(), e).andExpr(getTypePred(argTp, e));
    }
    case APPLY: {
      Theory* i = theoryOf(e);
      if (i != this) return i->computeTypePred(t, e);
      // fall through
    }
    default:
      return e.getEM()->trueExpr();
  }
}


Expr TheoryCore::parseExprOp(const Expr& e)
{
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  switch(e.getKind()) {
  case ID: {
    int kind = getEM()->getKind(e[0].getString());
    switch(kind) {
    case NULL_KIND: return e; // nothing to do
    case TRUE_EXPR:
    case FALSE_EXPR:
    case TYPE:
    case BOOLEAN: return getEM()->newLeafExpr(kind);
    default:
      DebugAssert(false, "Bad use of bare keyword: "+e.toString());
      return e;
    }
  }
  case RAW_LIST: break; // break out of switch, do the work
  default:
    return e;
  }
  DebugAssert(e.getKind()==RAW_LIST && e.arity() > 0 && e[0].getKind()==ID,
	      "TheoryCore::parseExprOp:\n e = "+e.toString());
  /* The first element of the list (e[0] is an ID of the operator. 
     ID string values are the dirst element of the expression */ 	      
  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());

  if (isBasicKind(kind)) {
    vector<Expr> operatorStack;
    vector<Expr> operandStack;
    vector<int> childStack;
    Expr e2;

    operatorStack.push_back(e);
    childStack.push_back(1);

    while (!operatorStack.empty()) {
      DebugAssert(operatorStack.size() == childStack.size(), "Invariant violated");

      if (childStack.back() < operatorStack.back().arity()) {

        e2 = operatorStack.back()[childStack.back()++];

        ExprMap<Expr>::iterator iParseCache = d_parseCache.find(e2);
        if (iParseCache != d_parseCache.end()) {
          operandStack.push_back((*iParseCache).second);
        }
        else if (e2.getKind() == RAW_LIST &&
                 e2.arity() > 0 &&
                 e2[0].getKind() == ID &&
                 isBasicKind(getEM()->getKind(e2[0][0].getString()))) {
          operatorStack.push_back(e2);
          childStack.push_back(1);
        }
        else {
          operandStack.push_back(parseExpr(e2));
        }
      }
      else {
        e2 = operatorStack.back();
        operatorStack.pop_back();
        childStack.pop_back();
        vector<Expr> children;
        vector<Expr>::iterator childStart = operandStack.end() - (e2.arity() - 1);
        children.insert(children.begin(), childStart, operandStack.end());
        operandStack.erase(childStart, operandStack.end());
        kind = getEM()->getKind(e2[0][0].getString());
        operandStack.push_back(Expr(kind, children, e2.getEM()));
        d_parseCache[e2] = operandStack.back();
        if (!getEM()->isTypeKind(operandStack.back().getKind())) {
          operandStack.back().getType();
        }
      }
    }
    DebugAssert(childStack.empty(), "Invariant violated");
    DebugAssert(operandStack.size() == 1, "Expected single operand left");
    return operandStack.back();
  }

  switch(kind) {
  case SUBTYPE:
    if (e.arity() <= 3) {
      Expr witness;
      if (e.arity() == 3) {
        witness = parseExpr(e[2]);
      }
      return newSubtypeExpr(parseExpr(e[1]), witness).getExpr();
    }
    else {
      throw ParserException("Expected one or two arguments to SUBTYPE");
    }
  case NEQ:
    if(e.arity()==3)
      return !(parseExpr(e[1]).eqExpr(parseExpr(e[2])));
    else
      throw ParserException("Disequality requires exactly two arguments: "
			    +e.toString());
    break;
  case TYPE: {
    if(e.arity()==2) {
      const Expr& types = e[1];
      if(types.getKind() == RAW_LIST) {
	vector<Expr> names;
	for(Expr::iterator i=types.begin(), iend=types.end(); i!=iend; ++i)
	  names.push_back(*i);
	return Expr(TYPEDECL, names, getEM());
      }
    }
    else if(e.arity() == 3 && e[1].getKind() == ID)
      return Expr(TYPEDEF, e[1], parseExpr(e[2]));
    throw ParserException("Bad TYPE declaration: "+e.toString());
    break;
  }
    //TODO: Is IF still used?
  case IF: 
    if(e.arity() == 4) {
      Expr c(parseExpr(e[1]));
      Expr e1(parseExpr(e[2]));
      Expr e2(parseExpr(e[3]));
      return c.iteExpr(e1, e2);
    } else
      throw ParserException("Bad IF-THEN-ELSE expression: "
		      +e.toString());
  case COND: {
    if(e.arity() >= 3)
      return processCond(e, 1);
    else
      throw ParserException("Bad COND expression: "+e.toString());
    break;
  }
  case LET: { // (LET ((v1 [ type1 ] e1) ... ) body)
    Expr e2(e);
    while (true) {
      if(!(e2.arity() == 3 && e2[1].getKind() == RAW_LIST && e2[1].arity() > 0))
        throw ParserException("Bad LET expression: "+e2.toString());

      // Iterate through the bound variables
      for(Expr::iterator i=e2[1].begin(), iend=e2[1].end(); i!=iend; ++i) {
        const Expr& decl = *i;
        if (decl.getKind() != RAW_LIST || decl.arity() != 2)
          throw ParserException("Bad variable declaration block in LET "
                                "expression: "+decl.toString()+
                                "\n e2 = "+e2.toString());
        if (decl[0].getKind() != ID)
          throw ParserException("Variable must be an identifier in LET "
                                "expression: "+decl[0].toString()+
                                "\n e2 = "+e2.toString());
        addBoundVar(decl[0][0].getString(), Type(), parseExpr(decl[1]));
      }
      // Optimization for nested LETs:
      if (e2[2].getKind()==RAW_LIST && e2[2].arity() > 0 &&
          e2[2][0].getKind()==ID && getEM()->getKind(e2[2][0][0].getString()) == LET) {
        e2 = e2[2];
      } else break;
    }
    // Parse the body recursively and return it (nuke the LET)
    return parseExpr(e2[2]);
  }
//     {
//     vector<Expr> letDecls, lvars;
//     Expr letDeclsExpr;
//     for(Expr::iterator i = e[1].begin(), iend=e[1].end(); i!=iend; ++i) {
//       lvars = i->getKids();
//       lvars.insert(lvars.begin(), Expr(e.getEM(), ID, Expr(e.getEM(), STRING_EXPR, "LETDECL")));
//       letDecls.push_back(Expr(e.getEM(), RAW_LIST, lvars));
//       }
//     letDecls.insert(letDecls.begin(), Expr(e.getEM(), ID, Expr(e.getEM(), STRING_EXPR, "LETDECLS")));
//     letDeclsExpr = Expr(e.getEM(), RAW_LIST, letDecls);
//     return Expr(e.getEM(), kind, parseExpr(letDeclsExpr), parseExpr(e[2]));
//   }
  case TRUE_EXPR:	{ return e.getEM()->trueExpr();	}
  case FALSE_EXPR:	{ return e.getEM()->falseExpr();}
  case BOOLEAN: 	{ return e.getEM()->boolExpr();	}
    break;
  default:
    DebugAssert(false,
		"TheoryCore::parseExprOp: invalid command or expression: "
		+ e.toString());
    break;
  }
  return e;
}


ExprStream& TheoryCore::print(ExprStream& os, const Expr& e)
{
  switch(os.lang()) {
    case SIMPLIFY_LANG:    
   switch(e.getKind()) {
    case TRUE_EXPR: os << "TRUE"; break;
    case FALSE_EXPR: os << "FALSE"; break;
    case TYPE:
      break; // no type for Simplify
    case ID:
      if(e.arity() == 1 && e[0].isString()) os << e[0].getString();
      else e.print(os);
      break;
    case CONST:
      //      os << "ERROR:const to be supported\n"; simplify do not need this
      break;
    case SUBTYPE:
      break;
    case TYPEDEF: {
      break;
    }
    case EQ:
      os << "(EQ " << e[0] << " " << e[1] << ")";
      break;
   case NOT: os << "(NOT " << e[0] << ")"; break;
   case AND: {
      int i=0, iend=e.arity();
      os << "(AND ";
      if(i!=iend) { os << e[i]; ++i; }
      for(; i!=iend; ++i) os << " " << e[i];
      os << ")";
    }
      break;
    case OR: {
      int i=0, iend=e.arity();
      os << "(OR ";
      if(i!=iend) { os << e[i]; ++i; }
      for(; i!=iend; ++i) os << " " << e[i];
      os << ")";
    }
      break;
    case ITE:
      os<<"ERROR:ITE:not supported yet\n";
      /* os <<  "(AND (IMPLIES "<< e[0] << " " << e[1]<<")"  
	 <<  "(IMPLIES (NOT " <<e[0] << ")" << e[2] <<"))"; 
      */
      break;
    case IFF:
      if(e.arity() == 2)
	os << "(IFF " << e[0]  << " " << e[1] << ")";
      else
	e.print(os);
      break;
    case IMPLIES:
      os << "(IMPLIES " <<e[0] << " " << e[1]  << ")";
      break;
      // Commands
    case ASSERT:
      os << "(BG_PUSH " << e[0] <<  ")\n";
      break;
    case TRANSFORM:
      os << "ERROR:TRANSFORM:not supported in Simplify " << push << e[0] << push << "\n";
      break;
    case QUERY:
      os << e[0] <<"\n";
      break;
    case WHERE:
      os << "ERROR:WHERE:not supported in Simplify\n";
      break;
    case ASSERTIONS:
      os << "ERROR:ASSERTIONS:not supported in Simplify\n";
      break;
    case ASSUMPTIONS:
      os << "ERROR:ASSUMPTIONS:not supported in Simplify\n";
      break;
    case COUNTEREXAMPLE:
      os << "ERROR:COUNTEREXAMPLE:not supported in Simplify\n";
      break;
    case COUNTERMODEL:
      os << "ERROR:COUNTERMODEL:not supported in Simplify\n";
      break;
    case PUSH:
    case POP:
    case POPTO:
    case PUSH_SCOPE:
    case POP_SCOPE:
    case POPTO_SCOPE:
      os << "ERROR:PUSH and POP:not supported in Simplify\n";
      break;
      //    case CONSTDEF:
    case LETDECL:
      os << "LETDECL not supported in Simplify\n";
      break;
    case LET: {
      // (LET (LETDECLS (LETDECL var [ type ] val) .... ) body)
      /*      bool first(true);
      os << "(" << push << "LET" << space << push;
      for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i) {
	if(!first) os << push << "," << pop << endl;
	else first = false;
	if(i->arity() == 3) {
	  os << (*i)[0] << ":" << space << push << (*i)[1]
	     << space << "= " << push << nodag << (*i)[2] << pop << pop;
	} else {
	  os << (*i)[0];
	  Type tp((*i)[0].lookupType());
	  if(!tp.isNull()) os << ":" << space << push << tp.getExpr();
	  else os << push;
	  os << space << "= " << push << nodag << (*i)[1] << pop << pop;
	}
      }
      os << pop << endl << "IN" << space << push << e[1] << push << ")";
      */
      os << "LET not supported in Simplify\n";
      break;
      
    }
    case BOUND_VAR:
      os << e.getName()+"_"+e.getUid();
      break;
    case SKOLEM_VAR:
      os << "SKOLEM_" + int2string((int)e.getIndex());
      break;
    case PF_APPLY: // FIXME: this will eventually go to the "symsim" theory
      /*      DebugAssert(e.arity() > 0, "TheoryCore::print(): "
		  "Proof rule application must have at "
		  "least one argument (rule name):\n "+e.toString());
      os << e[0];
      if(e.arity() > 1) { // Print the arguments
	os << push << "(" << push;
	bool first(true);
	for(int i=1; i<e.arity(); i++) {
	  if(first) first=false;
	  else os << push << "," << pop << space;
	  os << e[i];
	}
	os << push << ")";
	}*/

      os << "PR_APPLY not supported in Simplify\n";
      break;
    case RAW_LIST: {
      /*      os << "[" << push;
      bool firstTime(true);
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	if(firstTime) firstTime = false;
	else os << push << "," << pop << space;
	os << *i;
      }
      os << push << "]";*/
      os << "RAW_LIST not supported in Simplify\n";
      break;
    }
    case PF_HOLE: // FIXME: implement this (now fall through to default)
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.print(os);
    }
    break; // end of case simplify_LANG


  case PRESENTATION_LANG:
    switch(e.getKind()) {
    case TRUE_EXPR:
    case FALSE_EXPR:
    case UCONST:
    case BOOLEAN:
    case STRING_EXPR:
      e.print(os); break;
    case TYPE:
      if(e.arity() == 0) os << "TYPE";
      else if(e.arity() == 1) {
        for (int i=0; i < e[0].arity(); ++i) {
          if (i != 0) os << endl;
          os << e[0][i] << ": TYPE;";
        }
      }
      else if(e.arity() == 2)
	os << e[0] << ":" << push << " TYPE = " << e[1] << push << ";";
      else e.printAST(os);
      break;
    case ID:
      if(e.arity() == 1 && e[0].isString()) os << e[0].getString();
      else e.printAST(os);
      break;
    case CONST:
      if(e.arity() == 2) {
	if(e[0].getKind() == RAW_LIST) {
	  bool first(true);
	  for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i) {
	    if(first) first = false;
	    else os << push << "," << pop << space;
	    os << (*i);
	  }
	}
	else
	  os << e[0];
	os << ":" << push << space << e[1] << push << ";";
      } else if(e.arity() == 3)
	os << e[0] << ":" << push << space << e[1]
	   << space << "=" << space << push << e[2] << push << ";";
      else
	e.printAST(os);
      break;
    case SUBTYPE:
      os << "SUBTYPE(" << push << e[0] << push << ")";
      break;
    case TYPEDEF: {
      // This is used when dumping declarations to file.  Print just
      // the name of the type, unless it's a messed-up expression.
      if(e.arity() != 2) e.printAST(os);
      else if(e[0].isString()) os << e[0].getString();
      else e[0].print(os);
      break;
    }
    case EQ:
      // When a separator starts with a space (like " = "), add the
      // leading space with 'space' modifier.  If this separator goes
      // to the next line, the leading spaces must be eaten up to get
      // the indentation right; 'space' will tell the indentation
      // engine that it is a space that can be eaten.  A space in a
      // string (like " ") will never be eaten.
      os << "(" << push << e[0] << space << "= " << e[1] << push << ")";
      break;
    case NOT: os << "NOT " << e[0]; break;
    case AND: {
      int i=0, iend=e.arity();
      os << "(" << push;
      if(i!=iend) { os << e[i]; ++i; }
      for(; i!=iend; ++i) os << space << "AND " << e[i];
      os << push << ")";
    }
      break;
    case OR: {
      int i=0, iend=e.arity();
      os << "(" << push;
      if(i!=iend) { os << e[i]; ++i; }
      for(; i!=iend; ++i) os << space << "OR " << e[i];
      os << push << ")";
    }
      break;
    case ITE:
      os << push << "IF " << push << e[0] << popSave
	 << space << "THEN " << pushRestore << e[1] << popSave
	 << space << "ELSE " << pushRestore << e[2] << pop
	 << space << "ENDIF";
      break;
    case IFF:
      if(e.arity() == 2)
	os << "(" << push << e[0] << space << "<=> " << e[1] << push << ")";
      else
	e.printAST(os);
      break;
    case IMPLIES:
      os << "(" << push << e[0] << space << "=> " << e[1] << push << ")";
      break;
      // Commands
    case ASSERT:
      os << "ASSERT " << push << e[0] << push << ";";
      break;
    case TRANSFORM:
      os << "TRANSFORM " << push << e[0] << push << ";";
      break;
    case QUERY:
      os << "QUERY " << push << e[0] << push << ";";
      break;
    case WHERE:
      os << "WHERE;";
      break;
    case ASSERTIONS:
      os << "ASSERTIONS;";
      break;
    case ASSUMPTIONS:
      os << "ASSUMPTIONS;";
      break;
    case COUNTEREXAMPLE:
      os << "COUNTEREXAMPLE;";
      break;
    case COUNTERMODEL:
      os << "COUNTERMODEL;";
      break;
    case PUSH:
      if(e.arity()==0)
	os << "PUSH;";
      else
	os << "PUSH" << space << e[0] << push << ";";
      break;
    case POP:
      if(e.arity()==0)
	os << "POP;";
      else
	os << "POP" << space << e[0] << push << ";";
      break;
    case POPTO:
      os << "POPTO" << space << e[0] << push << ";"; break;
    case PUSH_SCOPE:
      if(e.arity()==0)
	os << "PUSH_SCOPE;";
      else
	os << "PUSH_SCOPE" << space << e[0] << push << ";";
      break;
    case POP_SCOPE:
      if(e.arity()==0)
	os << "POP_SCOPE;";
      else
	os << "POP_SCOPE" << space << e[0] << push << ";";
      break;
    case POPTO_SCOPE:
      os << "POPTO_SCOPE" << space << e[0] << push << ";"; break;
    case LETDECL:
      if(e.arity() == 2) os << e[1];
      else e.printAST(os);
      break;
    case LET: {
      // (LET (LETDECLS (LETDECL var [ type ] val) .... ) body)
      bool first(true);
      os << "(" << push << "LET" << space << push;
      for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i) {
	if(!first) os << push << "," << pop << endl;
	else first = false;
	if(i->arity() == 3) {
	  os << (*i)[0] << ":" << space << push << (*i)[1]
	     << space << "= " << push << nodag << (*i)[2] << pop << pop;
	} else {
	  os << (*i)[0];
	  Type tp((*i)[0].lookupType());
	  if(!tp.isNull()) os << ":" << space << push << tp.getExpr();
	  else os << push;
	  os << space << "= " << push << nodag << (*i)[1] << pop << pop;
	}
      }
      os << pop << endl << "IN" << space << push << e[1] << push << ")";
      break;
    }
    case BOUND_VAR:
      os << e.getName()+"_"+e.getUid();
      break;
    case SKOLEM_VAR:
      os << "SKOLEM_" + int2string((int)e.getIndex());
      break;
    case PF_APPLY: // FIXME: this will eventually go to the "symsim" theory
      DebugAssert(e.arity() > 0, "TheoryCore::print(): "
		  "Proof rule application must have at "
		  "least one argument (rule name):\n "+e.toString());
      os << e[0];
      if(e.arity() > 1) { // Print the arguments
	os << push << "(" << push;
	bool first(true);
	for(int i=1; i<e.arity(); i++) {
	  if(first) first=false;
	  else os << push << "," << pop << space;
	  os << e[i];
	}
	os << push << ")";
      }
      break;
    case RAW_LIST: {
      os << "[" << push;
      bool firstTime(true);
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	if(firstTime) firstTime = false;
	else os << push << "," << pop << space;
	os << *i;
      }
      os << push << "]";
      break;
    }
    case ANY_TYPE:
      os << "ANY_TYPE";
      break;
    case PF_HOLE: // FIXME: implement this (now fall through to default)
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case PRESENTATION_LANG
  case SMTLIB_LANG:
    switch(e.getKind()) {
    case TRUE_EXPR: os << "true"; break;
    case FALSE_EXPR: os << "false"; break;
    case UCONST: os << d_translator->fixConstName(e.getName()); break;
    case BOOLEAN: e.printAST(os); break;
    case STRING_EXPR: e.print(os); break;
    case TYPE:
      if (e.arity() == 1) {
        os << "  :extrasorts (";
        for (int i=0; i < e[0].arity(); ++i) {
          if (i != 0) os << push << space;
          os << push << e[0][i];
        }
        os << push << ")";
      }
      else if (e.arity() == 2) {
        break;
      }
      else {
        throw SmtlibException("TheoryCore::print: SMTLIB: Unexpected TYPE expression");
      }
      break;
    case ID: // FIXME: when lisp becomes case-insensitive, fix printing of IDs
      if(e.arity() == 1 && e[0].isString()) os << e[0].getString();
      else e.printAST(os);
      break;
    case CONST:
      if(e.arity() == 2) {
        if (e[1].getKind() == BOOLEAN) {
          os << "  :extrapreds ((" << push << d_translator->fixConstName(e[0][0].getString())
             << push << "))";
        }
        else if (e[1].getKind() == ARROW && e[1][e[1].arity()-1].getKind() == BOOLEAN) {
          os << "  :extrapreds ((" << push << d_translator->fixConstName(e[0][0].getString())
             << space << nodag << e[1] << push << "))";
        }
        else {
          os << "  :extrafuns ((" << push << d_translator->fixConstName(e[0][0].getString())
             << space << nodag << e[1] << push << "))";
        }
      }
      else if (e.arity() == 0) e.printAST(os);
      else {
        throw SmtlibException("TheoryCore::print: SMTLIB: CONST not implemented");
      }
      break;
    case SUBTYPE:
      throw SmtlibException("TheoryCore::print: SMTLIB: SUBTYPE not implemented");
      break;
    case TYPEDEF: {
      throw SmtlibException("TheoryCore::print: SMTLIB: TYPEDEF not implemented");
      break;
    }
    case EQ:
      os << "(" << push << "=" << space << e[0]
	 << space << e[1] << push << ")";
      break;
    case NOT:
      os << "(" << push << "not" << space << e[0] << push << ")";
      break;
    case AND: {
      int i=0, iend=e.arity();
      os << "(" << push << "and";
      for(; i!=iend; ++i) os << space << e[i];
      os << push << ")";
    }
      break;
    case OR: {
      int i=0, iend=e.arity();
      os << "(" << push << "or";
      for(; i!=iend; ++i) os << space << e[i] << space;
      os << push << ")";
      break;
    }
    case XOR: {
      int i=0, iend=e.arity();
      os << "(" << push << "xor";
      for(; i!=iend; ++i) os << space << e[i] << space;
      os << push << ")";
      break;
    }
    case ITE:
      os << "(" << push;
      if (e.getType().isBool()) os << "if_then_else";
      else os << "ite";
      os << space << e[0]
	 << space << e[1] << space << e[2] << push << ")";
      break;
    case IFF:
      os << "(" << push << "iff" << space
	 << e[0] << space << e[1] << push << ")";
      break;
    case IMPLIES:
      os << "(" << push << "implies" << space
	 << e[0] << space << e[1] << push << ")";
      break;
      // Commands
    case ASSERT:
      os << "  :assumption" << space << push << e[0];
      break;
    case TRANSFORM:
      throw SmtlibException("TheoryCore::print: SMTLIB: TRANSFORM not implemented");
      os << "(" << push << "TRANSFORM" << space << e[0] << push << ")";
      break;
    case QUERY:
      os << "  :formula" << space << push << e[0];
      break;
    case LETDECL:
      //      throw SmtlibException("TheoryCore::print: SMTLIB: LETDECL not implemented");
      if(e.arity() == 2) os << e[1];
      else e.printAST(os);
      break;
    case LET: {
      // (LET ((var [ type ] val) .... ) body)
      for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i) {
	os << "(" << push;
        Type tp(i->arity() == 3 ? (*i)[2].getType() : (*i)[1].getType());
        DebugAssert(!tp.isNull(), "Unexpected Null type");
        if (tp.getExpr().getKind() == BOOLEAN) {
          os << "flet" << space << "(" << push;
        }
        else {
          os << "let" << space << "(" << push;
        }
	if(i->arity() == 3) {
	  os << (*i)[0] << space << nodag << (*i)[2];
	} else {
	  os << (*i)[0] << space << nodag << (*i)[1];
        }
	os << push << ")" << pop << pop << space;
      }
      os << e[1] << push;
      for (int j = 0; j < e[0].arity(); ++j)
        os << ")";
      break;
    }
    case BOUND_VAR:
      os << push << "?" << e.getName()+"_"+e.getUid();
      break;
    case SKOLEM_VAR:
      os << push << "SKOLEM_" + int2string((int)e.getIndex());
      break;
    case PF_APPLY: {// FIXME: this will eventually go to the "symsim" theory
      throw SmtlibException("TheoryCore::print: SMTLIB: PF_APPLY not implemented");
      break;
    }
    case RAW_LIST: {
      os << "(" << push;
      bool firstTime(true);
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	if(firstTime) firstTime = false;
	else os << space;
	os << *i;
      }
      os << push << ")";
      break;
    }
    case ANY_TYPE:
      os << "ANY_TYPE";
      break;
    case WHERE:
      os << "  :cvc_command \"WHERE\"";
      break;
    case ASSERTIONS:
      os << "  :cvc_command \"ASSERTIONS\"";
      break;
    case ASSUMPTIONS:
      os << "  :cvc_command \"ASSUMPTIONS\"";
      break;
    case COUNTEREXAMPLE:
      os << "  :cvc_command \"COUNTEREXAMPLE\"";
      break;
    case COUNTERMODEL:
      os << "  :cvc_command \"COUNTERMODEL\"";
      break;
    case PUSH:
      os << "  :cvc_command" << space;
      if(e.arity()==0)
	os << "\"PUSH\"";
      else
	os << "\"PUSH" << space << e[0] << push << "\"";
      break;
    case POP:
      os << "  :cvc_command" << space;
      if(e.arity()==0)
	os << "\"POP\"";
      else
	os << "\"POP" << space << e[0] << push << "\"";
      break;
    case POPTO:
      os << "  :cvc_command" << space;
      os << "\"POPTO" << space << e[0] << push << "\""; break;
    case PUSH_SCOPE:
      os << "  :cvc_command" << space;
      if(e.arity()==0)
	os << "\"PUSH_SCOPE\"";
      else
	os << "\"PUSH_SCOPE" << space << e[0] << push << "\"";
      break;
    case POP_SCOPE:
      os << "  :cvc_command" << space;
      if(e.arity()==0)
	os << "\"POP_SCOPE\"";
      else
	os << "\"POP_SCOPE" << space << e[0] << push << "\"";
      break;
    case POPTO_SCOPE:
      os << "  :cvc_command" << space;
      os << "\"POPTO_SCOPE" << space << e[0] << push << "\""; break;
      break;
    case PF_HOLE: // FIXME: implement this (now fall through to default)
    default:
      throw SmtlibException("TheoryCore::print: SMTLIB_LANG: Unexpected expression: "
                            +getEM()->getKindName(e.getKind()));
    }
    break; // end of case SMTLIB_LANG
  case LISP_LANG:
    switch(e.getKind()) {
    case TRUE_EXPR:
    case FALSE_EXPR:
    case UCONST:
      e.print(os); break;
    case TYPE:
      if(e.arity() == 0) os << "TYPE";
      else if(e.arity() == 1)
	os << "(" << push << "TYPE" << space << e[0] << push << ")";
      else if(e.arity() == 2)
	os << "(" << push << "TYPE" << space << e[0]
	   << space << e[1] << push << ")";
      else e.printAST(os);
      break;
    case ID: // FIXME: when lisp becomes case-insensitive, fix printing of IDs
      if(e.arity() == 1 && e[0].isString()) os << e[0].getString();
      else e.printAST(os);
      break;
    case CONST:
      if(e.arity() == 2)
	os << "(" << push << "CONST" << space << e[0]
	   << space << e[1] << push << ")";
      else
	e.printAST(os);
      break;
    case SUBTYPE:
      os << "SUBTYPE(" << push << e[0] << push << ")";
      break;
    case TYPEDEF: {
      // This is used when dumping declarations to file.  Print just
      // the name of the type, unless it's a messed-up expression.
      if(e.arity() != 2) e.printAST(os);
      else if(e[0].isString()) os << e[0].getString();
      else e[0].print(os);
      break;
    }
    case EQ:
      // When a separator starts with a space (like " = "), add the
      // leading space with 'space' modifier.  If this separator goes
      // to the next line, the leading spaces must be eaten up to get
      // the indentation right; 'space' will tell the indentation
      // engine that it is a space that can be eaten.  A space in a
      // string (like " ") will never be eaten.
      os << "(" << push << "=" << space << e[0]
	 << space << e[1] << push << ")";
      break;
    case NOT:
      os << "(" << push << "NOT" << space << e[0] << push << ")";
      break;
    case AND: {
      int i=0, iend=e.arity();
      os << "(" << push << "AND";
      for(; i!=iend; ++i) os << space << e[i];
      os << push << ")";
    }
      break;
    case OR: {
      int i=0, iend=e.arity();
      os << "(" << push << "OR";
      for(; i!=iend; ++i) os << space << e[i] << space;
      os << push << ")";
    }
      break;
    case ITE:
      os << "(" << push << "IF" << space << e[0]
	 << space << e[1] << space << e[2] << push << ")";
      break;
    case IFF:
      os << "(" << push << "<=>" << space
	 << e[0] << space << e[1] << push << ")";
      break;
    case IMPLIES:
      os << "(" << push << "=>" << space
	 << e[0] << space << e[1] << push << ")";
      break;
      // Commands
    case ASSERT:
      os << "(" << push << "ASSERT" << space << e[0] << push << ")";
      break;
    case TRANSFORM:
      os << "(" << push << "TRANSFORM" << space << e[0] << push << ")";
      break;
    case QUERY:
      os << "(" << push << "QUERY" << space << e[0] << push << ")";
      break;
    case PUSH:
      os << "(PUSH)"; break;
    case POP:
      os << "(POP)"; break;
    case POPTO:
      os << "(" << push << "POPTO" << space << e[0] << push << ")"; break;
    case LETDECL:
      if(e.arity() == 2) os << e[1];
      else if(e.arity()==3) // It's a declaration of a named Expr
	os << e[0] << push << ":" << space << push << e[1] << push << " ="
	   << pop << pop << space << e[2];
      else e.printAST(os);
      break;
    case LET: {
      // (LET ((var [ type ] val) .... ) body)
      bool first(true);
      os << "(" << push << "LET" << space << "(" << push;
      for(Expr::iterator i=e[0].begin(), iend=e[0].end(); i!=iend; ++i) {
	if(!first) os << space;
	else first = false;
	os << "(" << push;
	if(i->arity() == 3) {
	  os << (*i)[0] << space << (*i)[1]
	     << space << nodag << (*i)[2];
	} else {
	  os << (*i)[0];
	  Type tp((*i)[0].lookupType());
	  if(!tp.isNull()) os << space << tp.getExpr();
	  os << space << nodag << (*i)[1];
	}
	os << push << ")" << pop << pop;
      }
      os << push << ")" << pop << pop << space << e[1] << push << ")";
      break;
    }
    case BOUND_VAR:
      os << e.getName()+"_"+e.getUid();
      break;
    case SKOLEM_VAR:
      os << "SKOLEM_" + int2string((int)e.getIndex());
      break;
    case PF_APPLY: {// FIXME: this will eventually go to the "symsim" theory
      DebugAssert(e.arity() > 0, "TheoryCore::print(): "
		  "Proof rule application must have at "
		  "least one argument (rule name):\n "+e.toString());
      os << push << "(" << push;
      bool first(true);
      for(int i=0; i<e.arity(); i++) {
	if(first) first=false;
	else os << space;
	os << e[i];
      }
      os << push << ")";
      break;
    }
    case RAW_LIST: {
      os << "(" << push;
      bool firstTime(true);
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	if(firstTime) firstTime = false;
	else os << space;
	os << *i;
      }
      os << push << ")";
      break;
    }
    case ANY_TYPE:
      os << "ANY_TYPE";
      break;
    case PF_HOLE: // FIXME: implement this (now fall through to default)
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case LISP_LANGUAGE
  default:
    // Print the top node in the default LISP format, continue with
    // pretty-printing for children.
    e.printAST(os);
  }
  return os;
}


void TheoryCore::refineCounterExample()
{
  // Theory 0 is TheoryCore, skip it
  for(int i = 1; i<getNumTheories(); i++) {
    if(d_theories[i] != this)
      d_theories[i]->refineCounterExample();
    if(inconsistent()) {
      vector<Expr> assump;
      inconsistentThm().getLeafAssumptions(assump);
      Expr a = Expr(RAW_LIST, assump, d_em);
      throw EvalException("Theory["+d_theories[i]->getName()
		      +"]: Model Creation failed due "
		      "to the following assumptions:\n\n"
		      +a.toString()
		      +"\n\nYou might be using an incomplete logical fragment.");
    }
  }
}


void TheoryCore::computeModelBasic(const vector<Expr>& v) {
  for(vector<Expr>::const_iterator i=v.begin(), iend=v.end(); i!=iend; ++i) {
    TRACE("model", "Model var "+i->toString()+" = ", find(*i).getRHS(), "");
    DebugAssert((*i).getType().isBool(), "TheoryCore::computeModel: *i = "
		+(*i).toString());
    Expr val = find(*i).getRHS();
    if(!val.isBoolConst()) val = d_em->trueExpr();
    assignValue(*i, val);
  }
}


/*****************************************************************************/
/*
 * User-level API methods
 */
/*****************************************************************************/


void TheoryCore::addFact(const Theorem& e)
{
  //<<<<<<< theory_core_sat.cpp
  //  cout<<"theory_core_sat.cpp asserted fact:"<<e<<endl;
  //  IF_DEBUG(string indentStr(getCM()->scopeLevel(), ' '));
  //  TRACE("addFact", indentStr, "Assert: ", e.getExpr().toString(PRESENTATION_LANG));
  //=======
  IF_DEBUG(string indentStr(getCM()->scopeLevel(), ' '));
  TRACE("addFact", indentStr, "Assert: ", e.getExpr().toString(PRESENTATION_LANG));
  //>>>>>>> 1.7
  DebugAssert(!d_inAddFact, "Recursive call to addFact() is not allowed");
  DebugAssert(d_queue.empty(), "addFact[start]: Expected empty queue");
  DebugAssert(d_queueSE.empty(), "addFact[start]: Expected empty queue");
  DebugAssert(d_update_thms.empty() && d_update_data.empty(),
              "adFact[start]: Expected empty update list");
  IF_DEBUG(ScopeWatcher sw(&d_inAddFact));

  if(!d_inconsistent) {
    enqueueFact(e);
    processFactQueue();
  }

  DebugAssert(d_queue.empty(), "addFact[end]: Expected empty queue");
  DebugAssert(d_queueSE.empty(), "addFact[end]: Expected empty queue");
}


bool TheoryCore::checkSATCore()
{
  DebugAssert(d_queue.empty(), "checkSATCore[start]: Expected empty queue");
  DebugAssert(d_queueSE.empty(), "checkSATCore[start]: Expected empty queue");
  DebugAssert(!d_inCheckSATCore, "Recursive call to checkSATCore is not allowed!");
  IF_DEBUG(ScopeWatcher sw(&d_inCheckSATCore));
  IF_DEBUG(debugger.counter("DP checkSAT(fullEffort) calls")++);

  bool lemmas = processFactQueue(FULL);

  DebugAssert(d_queue.empty(), "checkSATCore[start]: Expected empty queue");
  DebugAssert(d_queueSE.empty(), "checkSATCore[start]: Expected empty queue");

  return !lemmas;
}


bool TheoryCore::incomplete(vector<string>& reasons)
{
  if(d_incomplete.size() > 0) {
    for(CDMap<string,bool>::iterator i=d_incomplete.begin(),
	  iend=d_incomplete.end(); i!=iend; ++i)
      reasons.push_back((*i).first);
    return true;
  }
  else
    return false;
}


void TheoryCore::registerAtom(const Expr& e, const Theorem& thm)
{
  DebugAssert(!e.isRegisteredAtom(), "atom registered more than once");
  //  if (e.isQuantifier()) return;
  e.setRegisteredAtom();
  d_termTheorems[e] = thm;  
  // TODO: don't change state by calling this function
  DebugAssert(e.isAbsAtomicFormula(), "Expected atomic formula");
  IF_DEBUG(ScopeWatcher sw(&d_inRegisterAtom));
  Theorem thm2 = simplify(e);
  if (thm2.getRHS().isTrue()) {
    setFindLiteral(d_commonRules->iffTrueElim(thm2));
  }
  else if (thm2.getRHS().isFalse()) {
    setFindLiteral(d_commonRules->iffFalseElim(thm2));
  }
  else {
    setupSubFormulas(thm2.getRHS(), e, thm);
  }
  processFactQueue(LOW);
}


Theorem TheoryCore::getImpliedLiteral(void)
{
  Theorem res;
  if (d_impliedLiteralsIdx < d_impliedLiterals.size()) {
    res = d_impliedLiterals[d_impliedLiteralsIdx];
    d_impliedLiteralsIdx = d_impliedLiteralsIdx + 1;
  }
  return res;
}


Theorem TheoryCore::getImpliedLiteralByIndex(unsigned index)
{
  DebugAssert(index < d_impliedLiterals.size(), "index out of bounds");
  return d_impliedLiterals[index];
}


Expr TheoryCore::parseExpr(const Expr& e)
{
  // check cache
  ExprMap<Expr>::iterator iParseCache = d_parseCache.find(e);
  if (iParseCache != d_parseCache.end()) {
    return (*iParseCache).second;
  }

  // Remember the current size of the bound variable stack
  size_t boundVarSize = d_boundVarStack.size();

  // Compute the kind to determine what to do with the expression
  int kind = NULL_KIND;
  Expr res;

  switch(e.getKind()) {
  case ID: {
    const Expr c1 = e[0];
    kind = getEM()->getKind(c1.getString());
    if(kind == NULL_KIND) { // It's an identifier; try to resolve it
      res = resolveID(e[0].getString());
      if(res.isNull())
	throw ParserException("cannot resolve an identifier: "
			      +e[0].toString());
      else {
        DebugAssert(!e.isApply(), "Unexpected apply function");
      }
    }
    // Otherwise exit the switch and use DP-specific parsing
    break;
  }
  case RAW_LIST: {
    if(e.arity() == 0)
      throw ParserException("Empty list is not an expression!");
    const Expr& op = e[0];
    // First, resolve the operator
    switch(op.getKind()) {
    case ID: { // The operator in the list is ID: is it keyword or variable?
      kind = getEM()->getKind(op[0].getString());
      if(kind == NULL_KIND) {
	// It's a named function application.  Resolve the ID.
	res = resolveID(op[0].getString());
	if(res.isNull())
	  throw ParserException("cannot resolve an identifier: "
				+op[0].toString());
        if(e.arity() < 2)
          throw ParserException("Bad function application: "+e.toString());
        Expr::iterator i=e.begin(), iend=e.end();
        ++i;
        vector<Expr> args;
        for(; i!=iend; ++i) args.push_back(parseExpr(*i));
        res = Expr(res.mkOp(), args);
      }
      // Proceed to DP-specific parsing
      break;
    }
    case RAW_LIST: 
      // This can only be a lambda expression application.
      kind = LAMBDA;
      break;
    default:
      throw ParserException("Bad operator in "+e.toString());
    }
    break; // Exit the top-level switch, proceed to DP-specific parsing
  }
  default: // Can only be a string or a number.
    res = e;
  }

  // DP-specific parsing
  if(res.isNull()) {
    if (hasTheory(kind)) {
      res = theoryOf(kind)->parseExprOp(e);
      // Restore the bound variable stack
      if (d_boundVarStack.size() > boundVarSize) {
        d_parseCache.clear();
        while(d_boundVarStack.size() > boundVarSize) {
          pair<string,Expr>& bv = d_boundVarStack.back();
          hash_map<string,Expr>::iterator iBoundVarMap = d_boundVarMap.find(bv.first);
          DebugAssert(iBoundVarMap != d_boundVarMap.end(), "Expected bv in map");
          if ((*iBoundVarMap).second.getKind() == RAW_LIST) {
            (*iBoundVarMap).second = (*iBoundVarMap).second[1];
          }
          else d_boundVarMap.erase(bv.first);
          d_boundVarStack.pop_back();
        }
      }
    }
    else {
      res = e;
    }
  }
  d_parseCache[e] = res;
  if (!getEM()->isTypeKind(res.getOpKind())) res.getType();
  return res;
}


void TheoryCore::assignValue(const Expr& t, const Expr& val)
{
  DebugAssert(d_varAssignments.count(t) == 0
	      || d_varAssignments[t].getRHS() == val,
	      "TheoryCore::assignValue("+t.toString()+" := "+val.toString()
	      +")\n variable already has a different value");
  // Check if the assignment theorem can be derived from the find of t
  Theorem thm(find(t));
  Expr t2 = thm.getRHS();

  if(t2!=val) {
    bool isBool(t2.getType().isBool());
    Expr assump = (isBool)? t2.iffExpr(val) : t2.eqExpr(val);
    Theorem assertThm = d_coreSatAPI->addAssumption(assump);
    addFact(assertThm);
    thm = transitivityRule(thm, assertThm);
  }
  d_varAssignments[t] = thm;
}


void TheoryCore::assignValue(const Theorem& thm)
{
  DebugAssert(thm.isRewrite(), "TheoryCore::assignValue("+thm.toString()+")");
  const Expr& t = thm.getLHS();
  const Expr& val = thm.getRHS();
  DebugAssert(d_varAssignments.count(t) == 0
	      || d_varAssignments[t].getRHS() == val,
	      "TheoryCore::assignValue("+thm.getExpr().toString()
	      +")\n variable already has a different value:\n "
	      +d_varAssignments[t].getExpr().toString());
  d_varAssignments[t] = thm;
  // Check if the assignment theorem can be derived from the find of t
  Theorem findThm(find(t));
  const Expr& t2 = findThm.getRHS();

  if(t2!=val) {
    Theorem thm2 = transitivityRule(symmetryRule(findThm), thm);
    addFact(thm2);
  }
}


void TheoryCore::addToVarDB(const Expr&  e)
{
  TRACE("model", "TheoryCore::addToVarDB(", e, ")");
  d_vars.push_back(e);
}


void TheoryCore::collectBasicVars()
{
  TRACE_MSG("model", "collectBasicVars() {");
  // Clear caches
  d_varModelMap.clear();
  d_varAssignments.clear();
  // Current stack of variables to process
  vector<Expr> stack(d_vars.begin(), d_vars.end());
  size_t lastSize(0);
  while(stack.size() > 0) {
    Expr var(stack.back());
    stack.pop_back();
    if(d_varModelMap.count(var) > 0) continue; // Already processed
    Theorem findThm(find(var));
    if(findThm.getRHS()!=var) { // Replace var with its find
      d_simplifiedModelVars[var] = findThm;
      stack.push_back(findThm.getRHS());
      TRACE("model", "collectBasicVars: simplified var: ", findThm.getExpr(), "");
      continue; // Recycle to the beginning of the loop
    }
    lastSize = stack.size();
    TRACE("model", "getModelTerm(", var, ") {");
    getModelTerm(var, stack);
    TRACE("model", "getModelTerm => ",
	  Expr(RAW_LIST, stack, getEM()), " }");
    if(stack.size() == lastSize) {
      // Add a primitive variable
      TRACE("model", "collectBasicVars: adding primitive var: ", var, "");
      d_basicModelVars.push_back(var);
      if(var.isTerm()) {
	Theory* t1 = theoryOf(var);
	Theory* t2 = theoryOf(getBaseType(var).getExpr().getKind());
	if(t1 != t2) {
	  TRACE("model", "collectBasicVars: adding shared var: ", var, "");
	  d_sharedTerms.insert(var, t1);
	  t1->addSharedTerm(var);
	  t2->addSharedTerm(var);
	}
      }
    } else { // Record the descendants of var
      vector<Expr>& kids = d_varModelMap[var];
      for(size_t i=lastSize; i<stack.size(); ++i) {
	DebugAssert(stack[i] != var, "Primitive var was pushed on "
		    "the stack in computeModelTerm(): "+var.toString());
	kids.push_back(stack[i]);
      }
      TRACE("model", "collectBasicVars: var="+var.toString()
	    +" maps into vars=", Expr(RAW_LIST, kids, getEM()), "");
    }
  }
  TRACE_MSG("model", "collectBasicVars() => }");
}


void TheoryCore::buildModel(ExprMap<Expr>& m)
{
  TRACE_MSG("model", "buildModel() {");

  size_t numTheories = getNumTheories();
  // Use STL set to prune duplicate variables in theories
  vector<set<Expr> > theoryExprs(numTheories+1);
  // Sort out model vars by theories
  for(size_t j = 0 ; j<d_basicModelVars.size() ; j++) {
    const Expr& var = d_basicModelVars[j];
    Theorem findThm(find(var));
    if(findThm.getRHS()!=var) { // Replace var with its find and skip it
      TRACE("model", "buildModel: replace var="+var.toString(),
	    " with find(var)=", findThm.getRHS());
      d_simplifiedModelVars[var] = findThm;
      continue;
    }

    Theory *th = theoryOf(getBaseType(var).getExpr().getKind());
    size_t i=0;
    for(; i<numTheories && d_theories[i] != th; ++i);
    DebugAssert(i<numTheories && d_theories[i] == th,
		"TheoryCore::buildModel: cannot find the theory ["
		+th->getName()+"] for the variable: "
		+var.toString());
    theoryExprs[i].insert(var);
    TRACE("model", "buildModel: adding ", var,
	  " to theory "+d_theories[i]->getName());
  }
  // Build a model for the basic-type variables
  for(int i=0; i<getNumTheories(); i++) {
    if(theoryExprs[i].size() > 0) {
      TRACE("model", "computeModelBasic[", d_theories[i]->getName(), "] {");
      // Copy the corresponding variables into a vector
      vector<Expr> vars;
      vars.insert(vars.end(), theoryExprs[i].begin(), theoryExprs[i].end());
      d_theories[i]->computeModelBasic(vars);
      TRACE("model", "computeModelBasic[", d_theories[i]->getName(), "] => }");
      if(inconsistent()) {
	vector<Expr> assump;
	inconsistentThm().getLeafAssumptions(assump);
	Expr a = Expr(RAW_LIST, assump, d_em);
	throw EvalException
	  ("Model Creation failed in Theory["
	   +d_theories[i]->getName()
	   +"] due to the following assumptions:\n\n"
	   +a.toString()
	   +"\n\nYou might be using an incomplete logical fragment.");
      }
    }
  }
  // Recombine the values for the compound-type variables
  ExprHashMap<Theorem>::iterator k, kend=d_simplifiedModelVars.end();
  for(CDList<Expr>::const_iterator i=d_vars.begin(), iend=d_vars.end(); i!=iend; ++i) {
    Expr var(*i);
    TRACE("model", "buildModel: recombining var=", var, "");
    k=d_simplifiedModelVars.find(var);
    Theorem simp; // Null by default
    if(k!=kend) { // This var is simplified
      simp = k->second;
      TRACE("model", "buildModel: simplified var="+var.toString()+" to ",
	    simp.getRHS(), "");
      var = simp.getRHS();
    }
    collectModelValues(var, m);
    if(d_varAssignments.count(var) > 0) {
      if(!simp.isNull()) {
	Theorem thm(transitivityRule(simp, d_varAssignments[var]));
	assignValue(thm);
	DebugAssert(thm.getLHS() == *i, "");
	m[*i] = thm.getRHS();
      } else
	m[*i] = d_varAssignments[var].getRHS();
    }
//     else if(simp.isNull())
//       m[*i] = *i;
//     else
//       m[*i] = simp.getRHS();
  }
  TRACE_MSG("model", "buildModel => }");
}


// Recursively build a compound-type variable assignment for e
/*! Not all theories may implement aggregation of compound values.  If
 *  a compound variable is not assigned by a theory, add the more
 *  primitive variable assignments to 'm'.
 *
 * Some variables may simplify to something else (simplifiedVars map).
 * INVARIANT: e is always simplified (it's not in simplifiedVars map).
 * Also, if v simplifies to e, and e is assigned, then v must be assigned.
 */
void TheoryCore::collectModelValues(const Expr& e, ExprMap<Expr>& m)
{
  TRACE("model", "collectModelValues(", e, ") {");
  if(d_varAssignments.count(e) > 0) {
    TRACE("model", "collectModelValues[cached] => ",
	  d_varAssignments[e].getRHS(), " }");
    return; // Got it already
  }
  ExprHashMap<Theorem>::iterator k, kend=d_simplifiedModelVars.end();
  k=d_simplifiedModelVars.find(e);
  if(k!=kend) {
    const Theorem& findThm = k->second;
    const Expr& ee = findThm.getRHS();
    collectModelValues(ee, m);
    if(d_varAssignments.count(ee) > 0) {
      Theorem thm = transitivityRule(findThm, d_varAssignments[ee]);
      assignValue(thm);
    }
    TRACE("model", "collectModelValues[simplified] => ",
	  d_varAssignments[e].getRHS(), " }");
    return;
  }
  if(d_varModelMap.count(e) == 0) { // Consider it a value of itself
    assignValue(reflexivityRule(e));
    TRACE("model", "collectModelValues[e=e] => ", e, " }");
    return; // Got it already
  }
  // Get the vector of more primitive vars
  const vector<Expr>& vars = d_varModelMap[e];
  // Recurse
  bool gotAll(true);  // Whether we got all the values
  for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end(); i!=iend; ++i) {
    Expr var(*i);
//     k=d_simplifiedModelVars.find(var);
//     Theorem simp; // Null by default
//     if(k!=kend) { // This var is simplified
//       simp = k->second;
//       var = simp.getRHS();
//     }
    collectModelValues(var, m);
    if(d_varAssignments.count(var) == 0) {
      gotAll = false;
    }
//     else if(!simp.isNull()) {
//       Theorem thm(transitivityRule(simp, d_varAssignments[var]));
//       DebugAssert(thm.getLHS() == *i, "");
//       assignValue(thm);
//     }
  }
  IF_DEBUG(vector<Expr> res);
  if(gotAll) {
    vector<Expr> assigned; // What DP actually assigns
    Theory* th = theoryOf(getBaseType(e).getExpr());
    TRACE("model", "computeModel["+th->getName()+"](", e, ") {");
    th->computeModel(e, assigned);
    TRACE("model", "computeModel["+th->getName()+"] => ",
	  Expr(RAW_LIST, assigned, getEM()), " }");
    // Check if the assigned vars are different from e
    if(!(assigned.size()==1 && assigned[0]==e)) {
      //    if(d_varAssignments.count(e) == 0) {
      for(vector<Expr>::iterator i=assigned.begin(), iend=assigned.end();
	  i!=iend; ++i) {
	if(*i == e) continue; // Skip the original var
	m[*i] = getModelValue(*i).getRHS();
	IF_DEBUG(res.push_back(getModelValue(*i).getExpr()));
      }
    } else {
      IF_DEBUG(res.push_back(getModelValue(e).getExpr()));
    }
  }
  TRACE("model", "collectModelValues => ",
	Expr(RAW_LIST, res, getEM()), " }");
}


Theorem TheoryCore::rewriteLiteral(const Expr& e) {
  DebugAssert(e.isAbsLiteral(), "rewriteLiteral("+e.toString()
	      +")\nExpected a literal.");
  Theorem res;
  //Theory* i = theoryOf(getBaseType(e).getExpr());
  bool neg(e.isNot());
  const Expr a = neg? e[0] : e;
  Theory * i;
  if(a.isEq())
    i = theoryOf(getBaseType(a[0]).getExpr());  
  else if (a.arity() > 1)
    i = theoryOf(getBaseType(a[0]).getExpr());
  else
    i = theoryOf(a);
  res = i->rewriteAtomic(a);
  if(neg) res = d_commonRules->iffContrapositive(res);
  return res;
}


/*****************************************************************************/
/*
 * Methods provided for benefit of theories
 */
/*****************************************************************************/


/*!
 * Invariants: 
 * - The input theorem e is either an equality or a conjunction of
 *   equalities;
 * - In each equality e1=e2, the RHS e2 i-leaf-simplified;
 * - At the time of calling update(), all equalities in the queue are
 *   processed by assertFormula() and the equivalence classes are merged
 *   in the union-find database.
 *
 * In other words, the entire equality queue is processed "in parallel".
 */

void TheoryCore::assertEqualities(const Theorem& e)
{
  IF_DEBUG(
  string indentStr(getCM()->scopeLevel(), ' ');
  TRACE("facts", indentStr, "assertEqualities: ", e);
  d_solver->checkAssertEqInvariant(e);
  )
  // fast case
  if (e.isRewrite()) {
    DebugAssert(e.getLHS().isTerm(), "term expected");
    DebugAssert(findReduced(e.getLHS()) &&
                findReduced(e.getRHS()), "should be find-reduced");
    DebugAssert(e.getLHS() != e.getRHS(), "expected different lhs and rhs");
    assertFormula(e);
    e.getLHS().setFind(e);
    d_em->invalidateSimpCache();
    NotifyList *L;
    L = e.getLHS().getNotify();
    if (L) processNotify(e, L);
  }
  else if (e.getExpr().isFalse()) {
    setInconsistent(e);
  }
  else {
    Expr conj = e.getExpr();
    DebugAssert(conj.isAnd(), "Expected conjunction");
    vector<Theorem> eqs;
    Theorem t;
    int index;

    for (index = 0; index < conj.arity(); ++index) {
      t = d_commonRules->andElim(e, index);
      eqs.push_back(t);
      if (t.getExpr().isFalse()) {
        setInconsistent(t);
        return;
      }
      DebugAssert(t.isRewrite(), "Expected rewrite");
      DebugAssert(t.getLHS().isTerm(), "term expected");
      DebugAssert(findReduced(t.getLHS()) &&
                  findReduced(t.getRHS()), "should be find-reduced");
      assertFormula(t);
      if (d_inconsistent) return;
    }

    // Merge the equivalence classes
    vector<Theorem>::iterator i = eqs.begin(), iend = eqs.end();
    for(; i!=iend; ++i) {
      const Theorem& thm = *i;
      DebugAssert(find(thm.getLHS()).getRHS() == thm.getLHS(),
		  "find error: thm = "+thm.getExpr().toString()
		  +"\n\n  find(thm.getLHS()) = "
		  +find(thm.getLHS()).getRHS().toString());
      DebugAssert(find(thm.getRHS()).getRHS() == thm.getRHS(),
		  "find error: thm = "+thm.getExpr().toString()
		  +"\n\n  find(thm.getRHS()) = "
		  +find(thm.getRHS()).getRHS().toString());
      thm.getLHS().setFind(thm);
    }

    d_em->invalidateSimpCache();
  
    // Call the update() functions (process NotifyLists).  

    for(i=eqs.begin(); i!=iend && !d_inconsistent; ++i) {
      const Theorem& thm = *i;
      NotifyList *L = thm.getLHS().getNotify();
      if (L) processNotify(thm, L);
    }
  }
}


void TheoryCore::setIncomplete(const string& reason)
{
  d_incomplete.insert(reason, true);
}


Theorem TheoryCore::typePred(const Expr& e)
{
  return d_rules->typePred(e);
}


static bool hasBoundVarRec(const Expr& e)
{
  if (e.getFlag()) return false;
  if (e.isQuantifier()) return false;
  if (e.getKind() == BOUND_VAR) return true;
  for (int i = 0, ar = e.arity(); i < ar; ++i) {
    if (hasBoundVarRec(e[i])) return true;
  }
  e.setFlag();
  return false;
}

static bool hasBoundVar(const Expr& e)
{
  e.getEM()->clearFlags();
  return hasBoundVarRec(e);
}


void TheoryCore::enqueueFact(const Theorem& e)
{
  // The theorem scope shouldn't be higher than current
  DebugAssert(e.getScope() <= d_cm->scopeLevel(),
	      "\n e.getScope()="+int2string(e.getScope())
	      +"\n scopeLevel="+int2string(d_cm->scopeLevel())
	      +"\n e = "+e.getExpr().toString());
  DebugAssert(d_inAddFact || d_inCheckSATCore || d_inRegisterAtom,
	      "enqueueFact() is called outside of addFact()"
	      " or checkSATCore() or registerAtom()");
  DebugAssert((e.isRewrite() && !hasBoundVar(e.getLHS())
               && !hasBoundVar(e.getRHS())) ||
              (!e.isRewrite() && !hasBoundVar(e.getExpr())),
              "Bound vars shouldn't be free");

  // No need to enqueue when already inconsistent or out of resources
  if (d_inconsistent || outOfResources()) return;
	     
  if (!e.isRewrite() && e.getExpr().isFalse()) {
    setInconsistent(e);
  } else {
    getResource();
    d_queue.push(e);
    if (outOfResources()) {
      // No more resources: ignore all the remaining facts and fail
      // gracefully
      setIncomplete("Exhausted user-specified resource");
    }
  }
}


void TheoryCore::setInconsistent(const Theorem& e)
{
  d_inconsistent = true; d_incThm = e;
  d_queueSE.clear();
  // Theory 0 is TheoryCore, skip it
  for(int i=1; i<getNumTheories(); ++i) {
    d_theories[i]->notifyInconsistent(e);
  }
}


void TheoryCore::setupTerm(const Expr& t, Theory* i, const Theorem& thm)
{
  // Even if t is already setup, it may become shared with another theory
  Theory* j = theoryOf(t);
  if(i != j && t.isTerm()) {
    j->addSharedTerm(t);
    i->addSharedTerm(t);
    d_sharedTerms.insert(t, j);
  }
  
  int k;

  // Atomic formulas (non-terms) may have find pointers without the
  // subterms being setup.  Recurse down to the terms before checking
  // for find pointers.
  if (!t.isTerm()) {
    if (!t.isStoredPredicate()) {
      DebugAssert(t.isAbsLiteral(), "Expected absliteral");
      //    if(t.isAbsLiteral()) {
      for (k = 0; k < t.arity(); ++k) {
        setupTerm(t[k], i, thm);
      }

      //<<<<<<< theory_core_sat.cpp
      // Save a list of all non-equality predicates
      //    if (t.isAtomicFormula() && !t.isEq() && !t.isStoredPredicate()) {
      //    if (t.isAtomicFormula()  && !t.isStoredPredicate()) {
      //    if (!t.isStoredPredicate()) {
      //=======
      // Save a list of all asserted predicates
      t.setStoredPredicate();
      d_predicates.push_back(t);
      d_termTheorems[t] = thm;
      j->setup(t);
      //      d_termTheorems[t] = thm;
      TRACE("quantlevel","pushed pred ",t,thm);
      TRACE("quantlevel","pushed pred quantlevel",thm.getQuantLevel(),"");
    }
    return;
  }
  
  // If already setup, nothing else to do
  if (t.hasFind()) {
    return;
  }

  // Proceed with the setup

  // Add the term into the set of all terms
  d_terms.push_back(t);

  d_termTheorems[t] = thm;
  TRACE("quantlevel","pushed term ",t,thm);
  TRACE("quantlevel","pushed term quantlevel ",thm.getQuantLevel(),"");


  for (k = 0; k < t.arity(); ++k) {
    setupTerm(t[k], theoryOf(t), thm);
  }
  t.setFind(d_commonRules->reflexivityRule(t));
  j->setup(t);

  // Assert the subtyping predicate AFTER the setup is complete
  Theorem pred = d_rules->typePred(t);
  const Expr& predExpr = pred.getExpr();
  if(predExpr.isFalse()) {
    IF_DEBUG(debugger.counter("conflicts from type preficate")++);
    setInconsistent(pred); 
  }
  else if(!predExpr.isTrue()) {
    Theory* k = theoryOf(t.getType().getExpr());
    k->assertTypePred(t, pred);
  }
}
