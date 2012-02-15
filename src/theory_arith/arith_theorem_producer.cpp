/*****************************************************************************/
/*!
 * \file arith_theorem_producer.cpp
 * 
 * Author: Vijay Ganesh, Sergey Berezin
 * 
 * Created: Dec 13 02:09:04 GMT 2002
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
// CLASS: ArithProofRules
//
// AUTHOR: Sergey Berezin, 12/11/2002
// AUTHOR: Vijay Ganesh,   05/30/2003
//
// Description: TRUSTED implementation of arithmetic proof rules.
//
///////////////////////////////////////////////////////////////////////////////

// This code is trusted
#define _CVC3_TRUSTED_

#include "arith_theorem_producer.h"
#include "theory_core.h"

using namespace std;
using namespace CVC3;

////////////////////////////////////////////////////////////////////
// TheoryArith: trusted method for creating ArithTheoremProducer
////////////////////////////////////////////////////////////////////

ArithProofRules* TheoryArith::createProofRules() {
  return new ArithTheoremProducer(theoryCore()->getTM(), this);
}
  
////////////////////////////////////////////////////////////////////
// Canonization rules
////////////////////////////////////////////////////////////////////


#define CLASS_NAME "ArithTheoremProducer"


// Rule for unary minus: -e == (-1) * e
Theorem ArithTheoremProducer::uMinusToMult(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("uminus_to_mult", e);
  return newRWTheorem((-e), (rat(-1) * e), Assumptions::emptyAssump(), pf);
}


// ==> x - y = x + (-1) * y
Theorem ArithTheoremProducer::minusToPlus(const Expr& x, const Expr& y)
{
  Proof pf;
  if(withProof()) pf = newPf("minus_to_plus", x, y);
  return newRWTheorem((x-y), (x + (rat(-1) * y)), Assumptions::emptyAssump(), pf);  
}


// Rule for unary minus: -e == e/(-1)
// This is to reduce the number of almost identical rules for uminus and div
Theorem ArithTheoremProducer::canonUMinusToDivide(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_uminus", e);
  return newRWTheorem((-e), (e / rat(-1)), Assumptions::emptyAssump(), pf);
}

// Rules for division by constant

// (c)/(d) ==> (c/d).  When d==0, c/0 = 0 (our total extension).
Theorem ArithTheoremProducer::canonDivideConst(const Expr& c,
                                               const Expr& d) {
  // Make sure c and d are a const
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c),
                CLASS_NAME "::canonDivideConst:\n c not a constant: "
                + c.toString());
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonDivideConst:\n d not a constant: "
                + d.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("canon_divide_const", c, d, d_hole);
  const Rational& dr = d.getRational();
  return newRWTheorem((c/d), (rat(dr==0? 0 : (c.getRational()/dr))), Assumptions::emptyAssump(), pf);
}

// (c * x)/d ==> (c/d) * x, takes (c*x) and d
Theorem ArithTheoremProducer::canonDivideMult(const Expr& cx,
                                              const Expr& d) {
  // Check the format of c*x
  if(CHECK_PROOFS) {
    CHECK_SOUND(isMult(cx) && isRational(cx[0]),
                CLASS_NAME "::canonDivideMult:\n  "
                "Not a (c * x) expression: "
                + cx.toString());
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonDivideMult:\n  "
                "d is not a constant: " + d.toString());
  }
  const Rational& dr = d.getRational();
  Rational cdr(dr==0? 0 : (cx[0].getRational()/dr));
  Expr cd(rat(cdr));
  Proof pf;
  if(withProof())
    pf = newPf("canon_divide_mult", cx[0], cx[1], d);
  // (c/d) may be == 1, so we also need to canonize 1*x to x
  if(cdr == 1)
    return newRWTheorem((cx/d), (cx[1]), Assumptions::emptyAssump(), pf);
  else if(cdr == 0) // c/0 == 0 case
    return newRWTheorem((cx/d), cd, Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem((cx/d), (cd*cx[1]), Assumptions::emptyAssump(), pf);
}

// (+ t1 ... tn)/d ==> (+ (t1/d) ... (tn/d))
Theorem ArithTheoremProducer::canonDividePlus(const Expr& sum, const Expr& d) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(isPlus(sum) && sum.arity() >= 2 && isRational(sum[0]),
                CLASS_NAME "::canonUMinusPlus:\n  "
                "Expr is not a canonical sum: "
                + sum.toString());
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonUMinusPlus:\n  "
                "d is not a const: " + d.toString());
  }
  // First, propagate '/d' down to the args
  Proof pf;
  if(withProof())
    pf = newPf("canon_divide_plus", rat(sum.arity()),
               sum.begin(), sum.end());
  vector<Expr> newKids;
  for(Expr::iterator i=sum.begin(), iend=sum.end(); i!=iend; ++i)
    newKids.push_back((*i)/d);
  // (+ t1 ... tn)/d == (+ (t1/d) ... (tn/d))
  return newRWTheorem((sum/d), (plusExpr(newKids)), Assumptions::emptyAssump(), pf);
}

// x/(d) ==> (1/d) * x, unless d == 1
Theorem ArithTheoremProducer::canonDivideVar(const Expr& e, const Expr& d) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(d),
                CLASS_NAME "::canonDivideVar:\n  "
                "d is not a const: " + d.toString());
  }
  Proof pf;

  if(withProof())
    pf = newPf("canon_divide_var", e);

  const Rational& dr = d.getRational();
  if(dr == 1) 
    return newRWTheorem(e/d, e, Assumptions::emptyAssump(), pf);
  if(dr == 0) // e/0 == 0 (total extension of division)
    return newRWTheorem(e/d, d, Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem(e/d, rat(1/dr) * e, Assumptions::emptyAssump(), pf);
}


// Multiplication
// (MULT expr1 expr2 expr3 ...)
// Each expr is in canonical form, i.e. it can be a
// 1) Rational constant
// 2) Arithmetic Leaf (var or term from another theory)
// 3) (POW rational leaf)
// where rational cannot be 0 or 1
// 4) (MULT rational mterm'_1 ...) where each mterm' is of type (2) or (3)
// If rational == 1 then there should be at least two mterms
// 5) (PLUS rational sterm_1 ...) where each sterm is of 
//     type (2) or (3) or (4) 
//    if rational == 0 then there should be at least two sterms


Expr ArithTheoremProducer::simplifiedMultExpr(std::vector<Expr> & mulKids)
{
  DebugAssert(mulKids.size() >= 1 && mulKids[0].isRational(), "");
  if (mulKids.size() == 1) {
    return mulKids[0];
  }
  if ((mulKids[0] == rat(1)) && mulKids.size() == 2) {
    return mulKids[1];
  }
  else
    return multExpr(mulKids);
}

Expr ArithTheoremProducer::canonMultConstMult(const Expr & c,
                                              const Expr & e)
{
  // c is a rational
  // e is (MULT rat mterm'_1 ....)
  // assume that e2 is already in canonic form
  DebugAssert(c.isRational() && e.getKind() == MULT, "");
  std::vector<Expr> mulKids;
  DebugAssert ((e.arity() > 1) && (e[0].isRational()),
               "arith_theorem_producer::canonMultConstMult: "
               "a canonized MULT expression must have arity "
               "greater than 1: and first child must be "
               "rational " + e.toString());
  Expr::iterator i = e.begin();
  mulKids.push_back(rat(c.getRational() * (*i).getRational()));
  ++i;
  for(; i != e.end(); ++i) {
    mulKids.push_back(*i);
  }
  return simplifiedMultExpr(mulKids);
}

Expr ArithTheoremProducer::canonMultConstPlus(const Expr & e1,
                                              const Expr & e2)
{
  DebugAssert(e1.isRational() && e2.getKind() == PLUS &&
              e2.arity() > 0, "");
  // e1 is a rational
  // e2 is of the form (PLUS rational sterm1 sterm2 ...)
  // assume that e2 is already in canonic form
  std::vector<Theorem> thmPlusVector;
  Expr::iterator i = e2.begin();
  for(; i!= e2.end(); ++i) {
    thmPlusVector.push_back(canonMultMtermMterm(e1*(*i)));
  }
    
  Theorem thmPlus1 = 
    d_theoryArith->substitutivityRule(e2.getOp(), thmPlusVector);
  return thmPlus1.getRHS();
}

Expr ArithTheoremProducer::canonMultPowPow(const Expr & e1,
                                           const Expr & e2)
{
  DebugAssert(e1.getKind() == POW && e2.getKind() == POW, "");
  // (POW r1 leaf1) * (POW r2 leaf2)
  Expr leaf1 = e1[1];
  Expr leaf2 = e2[1];
  Expr can_expr;
  if (leaf1 == leaf2) {
    Rational rsum = e1[0].getRational() + e2[0].getRational();
    if (rsum == 0) {
      return rat(1);
    }
    else if (rsum == 1) {
      return leaf1;
    }
    else
      {
        return powExpr(rat(rsum), leaf1);
      }
  }
  else
    {
      std::vector<Expr> mulKids;
      mulKids.push_back(rat(1));
      // the leafs should be put in decreasing order
      if (leaf1 < leaf2) {
        mulKids.push_back(e2);
        mulKids.push_back(e1);
      }
      else 
        {
          mulKids.push_back(e1);
          mulKids.push_back(e2);
        }
      // FIXME: don't really need to simplify, just wrap up a MULT?
      return simplifiedMultExpr(mulKids);
    }
}

Expr ArithTheoremProducer::canonMultPowLeaf(const Expr & e1,
                                            const Expr & e2)
{
  DebugAssert(e1.getKind() == POW, "");
  // (POW r1 leaf1) * leaf2
  Expr leaf1 = e1[1];
  Expr leaf2 = e2;
  Expr can_expr;
  if (leaf1 == leaf2) {
    Rational rsum = e1[0].getRational() + 1;
    if (rsum == 0) {
      return rat(1);
    }
    else if (rsum == 1) {
      return leaf1;
    }
    else
      {
        return powExpr(rat(rsum), leaf1);
      }
  }
  else
    {
      std::vector<Expr> mulKids;
      mulKids.push_back(rat(1));
      // the leafs should be put in decreasing order
      if (leaf1 < leaf2) {
        mulKids.push_back(e2);
        mulKids.push_back(e1);
      }
      else 
        {
          mulKids.push_back(e1);
          mulKids.push_back(e2);
        }
      return simplifiedMultExpr(mulKids);
    }
}

Expr ArithTheoremProducer::canonMultLeafLeaf(const Expr & e1,
                                             const Expr & e2)
{
  // leaf1 * leaf2
  Expr leaf1 = e1;
  Expr leaf2 = e2;
  Expr can_expr;
  if (leaf1 == leaf2) {
    return powExpr(rat(2), leaf1);
  }
  else
    {
      std::vector<Expr> mulKids;
      mulKids.push_back(rat(1));
      // the leafs should be put in decreasing order
      if (leaf1 < leaf2) {
        mulKids.push_back(e2);
        mulKids.push_back(e1);
      }
      else 
        {
          mulKids.push_back(e1);
          mulKids.push_back(e2);
        }
      return simplifiedMultExpr(mulKids);
    }
}

Expr ArithTheoremProducer::canonMultLeafOrPowMult(const Expr & e1,
                                                  const Expr & e2)
{
  DebugAssert(e2.getKind() == MULT, "");
  // Leaf * (MULT rat1 mterm1 ...)
  // (POW r1 leaf1) * (MULT rat1 mterm1 ...) where
  // each mterm is a leaf or (POW r leaf).  Furthermore the leafs
  // in the mterms are in descending order
  Expr leaf1 = e1.getKind() == POW ? e1[1] : e1;
  std::vector<Expr> mulKids;
  DebugAssert(e2.arity() > 1, "MULT expr must have arity 2 or more");
  Expr::iterator i = e2.begin();
  // push the rational
  mulKids.push_back(*i);
  ++i;
  // Now i points to the first mterm
  for(; i != e2.end(); ++i) {
    Expr leaf2 = ((*i).getKind() == POW) ? (*i)[1] : (*i);
    if (leaf1 == leaf2) {
      Rational r1 = e1.getKind() == POW ? e1[0].getRational() : 1;
      Rational r2 = 
        ((*i).getKind() == POW ? (*i)[0].getRational() : 1);
      // if r1 + r2 == 0 then it is the case of x^n * x^{-n}
      // So, nothing needs to be added
      if (r1 + r2 != 0) {
        if (r1 + r2 == 1) {
          mulKids.push_back(leaf1);
        }
        else
          {
            mulKids.push_back(powExpr(rat(r1 + r2), leaf1));
          }
      }
      break;
    }
    // This ensures that the leaves in the mterms are also arranged
    // in decreasing order
    // Note that this will need to be changed if we want the order to
    // be increasing order.
    else if (leaf2 < leaf1) {
      mulKids.push_back(e1);
      mulKids.push_back(*i);
      break;
    }
    else // leaf1 < leaf2
      mulKids.push_back(*i);
  }
  if (i == e2.end()) {
    mulKids.push_back(e1);
  }
  else
    {
      // e1 and *i have already been added
      for (++i; i != e2.end(); ++i) {
        mulKids.push_back(*i);
      }
    }
  return simplifiedMultExpr(mulKids);
}

// Local class for ordering monomials; note, that it flips the
// ordering given by greaterthan(), to sort in ascending order.
class MonomialLess {
public:
  bool operator()(const Expr& e1, const Expr& e2) const {
    return ArithTheoremProducer::greaterthan(e1,e2);
  }
};

typedef map<Expr,Rational,MonomialLess> MonomMap;

Expr 
ArithTheoremProducer::canonCombineLikeTerms(const std::vector<Expr> & sumExprs)
{
  Rational constant = 0;
  MonomMap sumHashMap;
  vector<Expr> sumKids;
 
  // Add each distinct mterm (not including the rational) into 
  // an appropriate hash map entry 
  std::vector<Expr>::const_iterator i = sumExprs.begin();
  for (; i != sumExprs.end(); ++i) {
    Expr mul = *i;
    if (mul.isRational()) {
      constant = constant + mul.getRational();
    }
    else {
      switch (mul.getKind()) {
      case MULT: {
        std::vector<Expr> mulKids;
        DebugAssert(mul.arity() > 1 && mul[0].isRational(),"");
        mulKids.push_back(rat(1));
        Expr::iterator j = mul.begin();
        ++j;
        for (; j!= mul.end(); ++j) {
          mulKids.push_back(*j);
        }
                
        // make sure that tempExpr is also in canonic form
        Expr tempExpr = mulKids.size() > 2 ? multExpr(mulKids): mulKids[1];
	MonomMap::iterator i=sumHashMap.find(tempExpr);
        if (i == sumHashMap.end()) {
          sumHashMap[tempExpr] = mul[0].getRational();
        }
        else {
          (*i).second += mul[0].getRational();
        }
      }
        break;
      default: {
	MonomMap::iterator i=sumHashMap.find(mul);
        // covers the case of POW, leaf
        if (i == sumHashMap.end()) {
          sumHashMap[mul] = 1;
        }
        else {
          (*i).second += 1;
        }
        break;
      }
      }
    }
  }
  // Now transfer to sumKids
  sumKids.push_back(rat(constant));
  MonomMap::iterator j = sumHashMap.begin(), jend=sumHashMap.end();
  for(; j != jend; ++j) {
    if ((*j).second != 0)
      sumKids.push_back
	(canonMultMtermMterm(rat((*j).second) * (*j).first).getRHS());
  }
    
  /*
    for (unsigned k = 0; k < sumKids.size(); ++k)
    {
    cout << "sumKids[" << k << "] = " << sumKids[k].toString() << endl;
    }
  */    

  // The ordering in map guarantees the correct order; no need to sort

  // std::sort(sumKids.begin(), sumKids.end(), greaterthan);
    
  if ((constant == 0) && (sumKids.size() == 2)) {
    return sumKids[1];
  }
  else if (sumKids.size() == 1) {
    return sumKids[0];
  }
  else
    return plusExpr(sumKids);
}

Expr ArithTheoremProducer::canonMultLeafOrPowOrMultPlus(const Expr & e1,
                                                        const Expr & e2)
{
  DebugAssert(e2.getKind() == PLUS, "");
  // Leaf *  (PLUS rational sterm1 ...) 
  // or 
  // (POW n1 x1) * (PLUS rational sterm1 ...)
  // or
  // (MULT r1 m1 m2 ...) * (PLUS rational sterm1 ...)
  // assume that e1 and e2 are themselves canonized
  std::vector<Expr> sumExprs;
  // Multiply each term in turn. 
  Expr::iterator i = e2.begin();
  for (; i != e2.end(); ++i) {
    sumExprs.push_back(canonMultMtermMterm(e1 * (*i)).getRHS());
  }
  return canonCombineLikeTerms(sumExprs);
}

Expr ArithTheoremProducer::canonMultPlusPlus(const Expr & e1,
                                             const Expr & e2)
{
  DebugAssert(e1.getKind() == PLUS && e2.getKind() == PLUS, "");
  // (PLUS r1 .... ) * (PLUS r1' ...)
  // assume that e1 and e2 are themselves canonized

  std::vector<Expr> sumExprs;
  // Multiply each term in turn. 
  Expr::iterator i = e1.begin();
  for (;  i != e1.end(); ++i) {
    Expr::iterator j = e2.begin();
    for (;  j != e2.end(); ++j) {
      sumExprs.push_back(canonMultMtermMterm((*i) * (*j)).getRHS());
    }
  }
  return canonCombineLikeTerms(sumExprs);
}



// The following produces a Theorem which is the result of multiplication
// of two canonized mterms.  e = e1*e2
Theorem
ArithTheoremProducer::canonMultMtermMterm(const Expr& e)
{
  if(CHECK_PROOFS) {
    CHECK_SOUND(isMult(e) && e.arity() == 2, 
		"canonMultMtermMterm: e = "+e.toString());
  }
  Proof pf;
  Expr rhs;
  const Expr& e1 = e[0];
  const Expr& e2 = e[1];
  string cmmm = "canon_mult_mterm_mterm";

  if (e1.isRational()) {
    // e1 is a Rational
    const Rational& c = e1.getRational();
    if (c == 0)
      return canonMultZero(e2);
    else if (c == 1)
      return canonMultOne(e2);
    else {
      switch (e2.getKind()) {
      case RATIONAL_EXPR :
        // rat * rat
        return canonMultConstConst(e1,e2);
        break;
        // TODO case of leaf
      case POW:
        // rat * (POW rat leaf)
        // nothing to simplify
        return d_theoryArith->reflexivityRule (e);
                
        break;
      case MULT:
        rhs = canonMultConstMult(e1,e2);
        if(withProof()) pf = newPf(cmmm,e,rhs);
        return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
        break;
      case PLUS:
        rhs = canonMultConstPlus(e1,e2);
        if(withProof()) pf = newPf(cmmm,e,rhs);
        return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
        break;
      default:
        // TODO: I am going to assume that this is just a leaf
        // i.e., a variable or term from another theory
        return d_theoryArith->reflexivityRule(e);
        break;
      }
    }
  }
  else if (e1.getKind() == POW) {
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case POW:
      rhs = canonMultPowPow(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e,rhs, Assumptions::emptyAssump(), pf);
      break;
    case MULT:
      rhs = canonMultLeafOrPowMult(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    case PLUS:
      rhs = canonMultLeafOrPowOrMultPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);                          
      break;
    default:
      rhs = canonMultPowLeaf(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e,rhs, Assumptions::emptyAssump(), pf);
      break;
    }
  }
  else if (e1.getKind() == MULT) {
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
    case POW:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case MULT:
      {
        // (Mult r m1 m2 ...) (Mult r' m1' m2' ...)
        Expr result = e2;
        Expr::iterator i = e1.begin();
        for (; i != e1.end(); ++i) {
          result = canonMultMtermMterm((*i) * result).getRHS();
        }
        if(withProof()) pf = newPf(cmmm,e,result);
        return newRWTheorem(e, result, Assumptions::emptyAssump(), pf);
      }
      break;
    case PLUS:
      rhs = canonMultLeafOrPowOrMultPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e,rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      // leaf
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    }
  }
  else if (e1.getKind() == PLUS) {
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
    case POW:
    case MULT:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case PLUS:
      rhs = canonMultPlusPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      // leaf
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    }
  }
  else {
    // leaf
    switch (e2.getKind()) {
    case RATIONAL_EXPR:
      // switch the order of the two arguments
      return canonMultMtermMterm(e2 * e1);
      break;
    case POW:
      rhs = canonMultPowLeaf(e2,e1);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    case MULT:
      rhs = canonMultLeafOrPowMult(e1,e2);;
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    case PLUS:
      rhs = canonMultLeafOrPowOrMultPlus(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    default:
      // leaf * leaf
      rhs = canonMultLeafLeaf(e1,e2);
      if(withProof()) pf = newPf(cmmm,e,rhs);
      return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
      break;
    }
  }
  FatalAssert(false, "Unreachable");
  return newRWTheorem(e, rhs, Assumptions::emptyAssump(), pf);
}

// (PLUS expr1 expr2 ...) where each expr is itself in canonic form
Theorem
ArithTheoremProducer::canonPlus(const Expr& e) 
{
  Proof pf;
    
  if (withProof()) {
    pf = newPf("canon_plus", e);
  }
  DebugAssert(e.getKind() == PLUS, "");

  // First flatten the PLUS

  std::vector<Expr> sumKids;
  Expr::iterator i = e.begin();
  for(; i != e.end(); ++i) {
    if ((*i).getKind() != PLUS) {
      sumKids.push_back(*i);
    }
    else
      {
        Expr::iterator j = (*i).begin();
        for(; j != (*i).end(); ++j)
          sumKids.push_back(*j);
      }
  }
  Expr val = canonCombineLikeTerms(sumKids);
  if (withProof()) {
    pf = newPf("canon_plus", e, val);
  }    
  return newRWTheorem(e, val, Assumptions::emptyAssump(), pf);
}

// (MULT expr1 expr2 ...) where each expr is itself in canonic form
Theorem
ArithTheoremProducer::canonMult(const Expr& e) 
{
  Proof pf;
  DebugAssert(e.getKind() == MULT && e.arity() > 1, "");
  Expr::iterator i = e.begin();
  Expr result = *i;
  ++i;
  for (; i != e.end(); ++i) {
    result = canonMultMtermMterm(result * (*i)).getRHS();
  }
  if (withProof()) {
    pf = newPf("canon_mult", e,result);
  }
  return newRWTheorem(e, result, Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::canonInvertConst(const Expr& e) 
{
  if(CHECK_PROOFS)
    CHECK_SOUND(isRational(e), "expecting a rational: e = "+e.toString());
    
  Proof pf;
    
  if (withProof()) {
    pf = newPf("canon_invert_const", e);
  }
  const Rational& er = e.getRational();
  return newRWTheorem((rat(1)/e), rat(er==0? 0 : (1/er)), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::canonInvertLeaf(const Expr& e) 
{
  Proof pf;
    
  if (withProof()) {
    pf = newPf("canon_invert_leaf", e);
  }
  return newRWTheorem((rat(1)/e), powExpr(rat(-1), e), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::canonInvertPow(const Expr& e) 
{
  DebugAssert(e.getKind() == POW, "expecting a rational"+e[0].toString());
    
  Proof pf;
    
  if (withProof()) {
    pf = newPf("canon_invert_pow", e);
  }
  if (e[0].getRational() == -1)
    return newRWTheorem((rat(1)/e), e[1], Assumptions::emptyAssump(), pf);
  else
    return newRWTheorem((rat(1)/e), 
                        powExpr(rat(-e[0].getRational()), e), 
                        Assumptions::emptyAssump(), 
                        pf);
}

Theorem
ArithTheoremProducer::canonInvertMult(const Expr& e) 
{
  DebugAssert(e.getKind() == MULT, "expecting a rational"+e[0].toString());

  Proof pf;
    
  if (withProof()) {
    pf = newPf("canon_invert_mult", e);
  }

  DebugAssert(e.arity() > 1, "MULT should have arity > 1"+e.toString());
  Expr result = canonInvert(e[0]).getRHS();
  for (int i = 1; i < e.arity(); ++i) {
    result = 
      canonMultMtermMterm(result * canonInvert(e[i]).getRHS()).getRHS();
  }
  return newRWTheorem((rat(1)/e), result, Assumptions::emptyAssump(), pf);
}


// Given an expression e in Canonic form generate 1/e in canonic form
// This function assumes that e is not a PLUS expression
Theorem
ArithTheoremProducer::canonInvert(const Expr& e) 
{
  DebugAssert(e.getKind() != PLUS, 
              "Cannot do inverse on a PLUS"+e.toString());
  switch (e.getKind()) {
  case RATIONAL_EXPR:
    return canonInvertConst(e);
    break;
  case POW:
    return canonInvertPow(e);
    break;
  case MULT:
    return canonInvertMult(e);
    break;
  default:
    // leaf
    return canonInvertLeaf(e);
    break;
  }
}


Theorem
ArithTheoremProducer::canonDivide(const Expr& e) 
{
  DebugAssert(e.getKind() == DIVIDE, "Expecting Divide"+e.toString());
  Proof pf;
    
  if (withProof()) {
    pf = newPf("canon_invert_divide", e);
  }

  Theorem thm = newRWTheorem(e, e[0]*(canonInvert(e[1]).getRHS()), Assumptions::emptyAssump(), pf);
    
  return d_theoryArith->transitivityRule(thm, canonMult(thm.getRHS()));
}


// Rules for multiplication
// t*c ==> c*t, takes constant c and term t
Theorem 
ArithTheoremProducer::canonMultTermConst(const Expr& c, const Expr& t) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c),
                CLASS_NAME "::canonMultTermConst:\n  "
                "c is not a constant: " + c.toString());
  }
  if(withProof()) pf = newPf("canon_mult_term_const", c, t);
  return newRWTheorem((t*c), (c*t), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// t1*t2 ==> Error, takes t1 and t2 where both are non-constants
Theorem 
ArithTheoremProducer::canonMultTerm1Term2(const Expr& t1, const Expr& t2) {
  // Proof pf;
  // if(withProof()) pf = newPf("canon_mult_term1_term2", t1, t2);
  if(CHECK_PROOFS) {
    CHECK_SOUND(false, "Fatal Error: We don' support multiplication"
                "of two non constant terms at this time " 
                + t1.toString() + " and " + t2.toString());
  }
  return Theorem();
}

// Rules for multiplication
// 0*x = 0, takes x
Theorem ArithTheoremProducer::canonMultZero(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_mult_zero", e);
  return newRWTheorem((rat(0)*e), rat(0), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// 1*x ==> x, takes x
Theorem ArithTheoremProducer::canonMultOne(const Expr& e) {
  Proof pf;
  if(withProof()) pf = newPf("canon_mult_one", e);
  return newRWTheorem((rat(1)*e), e, Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*c2 ==> c', takes constant c1*c2 
Theorem 
ArithTheoremProducer::canonMultConstConst(const Expr& c1, const Expr& c2) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c1),
                CLASS_NAME "::canonMultConstConst:\n  "
                "c1 is not a constant: " + c1.toString());
    CHECK_SOUND(isRational(c2),
                CLASS_NAME "::canonMultConstConst:\n  "
                "c2 is not a constant: " + c2.toString());
  }
  if(withProof()) pf = newPf("canon_mult_const_const", c1, c2);
  return 
    newRWTheorem((c1*c2), rat(c1.getRational()*c2.getRational()), Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*(c2*t) ==> c'*t, takes c1 and c2 and t
Theorem 
ArithTheoremProducer::canonMultConstTerm(const Expr& c1,
                                         const Expr& c2,const Expr& t) {
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c1),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "c1 is not a constant: " + c1.toString());
    CHECK_SOUND(isRational(c2),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "c2 is not a constant: " + c2.toString());
  }
  
  if(withProof()) pf = newPf("canon_mult_const_term", c1, c2, t);
  return 
    newRWTheorem(c1*(c2*t), rat(c1.getRational()*c2.getRational())*t, Assumptions::emptyAssump(), pf);
}

// Rules for multiplication
// c1*(+ c2 v1 ...) ==> (+ c1c2 c1v1 ...), takes c1 and the sum
Theorem 
ArithTheoremProducer::canonMultConstSum(const Expr& c1, const Expr& sum) {
  Proof pf;
  std::vector<Expr> sumKids;
  
  if(CHECK_PROOFS) {
    CHECK_SOUND(isRational(c1),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "c1 is not a constant: " + c1.toString());
    CHECK_SOUND(PLUS == sum.getKind(),
                CLASS_NAME "::canonMultConstTerm:\n  "
                "the kind must be a PLUS: " + sum.toString());
  }
  Expr::iterator i = sum.begin();
  for(; i != sum.end(); ++i)
    sumKids.push_back(c1*(*i));
  Expr ret = plusExpr(sumKids);
  if(withProof()) pf = newPf("canon_mult_const_sum", c1, sum, ret);
  return newRWTheorem((c1*sum),ret , Assumptions::emptyAssump(), pf);
}


// c^n = c' (compute the constant power expression)
Theorem
ArithTheoremProducer::canonPowConst(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == POW && e.arity() == 2
		&& e[0].isRational() && e[1].isRational(),
		"ArithTheoremProducer::canonPowConst("+e.toString()+")");
  }
  const Rational& p = e[0].getRational();
  const Rational& base = e[1].getRational();
  if(CHECK_PROOFS) {
    CHECK_SOUND(p.isInteger(),
		"ArithTheoremProducer::canonPowConst("+e.toString()+")");
  }
  Expr res;
  if (base == 0 && p < 0) {
    res = rat(0);
  }
  else res = rat(pow(p, base));
  Proof pf;
  if(withProof())
    pf = newPf("canon_pow_const", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


// Rules for addition
// flattens the input. accepts a PLUS expr
Theorem 
ArithTheoremProducer::canonFlattenSum(const Expr& e) {
  Proof pf;
  std::vector<Expr> sumKids;
  if(CHECK_PROOFS) {
    CHECK_SOUND(PLUS == e.getKind(),
                CLASS_NAME "::canonFlattenSum:\n"
                "input must be a PLUS:" + e.toString());
  }

  Expr::iterator i = e.begin();
  for(; i != e.end(); ++i){
    if (PLUS != (*i).getKind())
      sumKids.push_back(*i);
    else {
      Expr::iterator j = (*i).begin();
      for(; j != (*i).end(); ++j)
        sumKids.push_back(*j);
    }
  }
  Expr ret =  plusExpr(sumKids);
  if(withProof()) pf = newPf("canon_flatten_sum", e,ret);
  return newRWTheorem(e,ret, Assumptions::emptyAssump(), pf);
}

// Rules for addition
// combine like terms. accepts a flattened PLUS expr
Theorem 
ArithTheoremProducer::canonComboLikeTerms(const Expr& e) {
  Proof pf;
  std::vector<Expr> sumKids;
  ExprMap<Rational> sumHashMap;
  Rational constant = 0;

  if(CHECK_PROOFS) {
    Expr::iterator k = e.begin();
    for(; k != e.end(); ++k)
      CHECK_SOUND(!isPlus(*k),
                  CLASS_NAME "::canonComboLikeTerms:\n"
                  "input must be a flattened PLUS:" + k->toString());
  }
  Expr::iterator i = e.begin();
  for(; i != e.end(); ++i){
    if(i->isRational())
      constant = constant + i->getRational();
    else {
      if (!isMult(*i)) {
        if(0 == sumHashMap.count((*i)))
          sumHashMap[*i] = 1;
        else
          sumHashMap[*i] += 1;
      }
      else {
        if(0 == sumHashMap.count((*i)[1]))
          sumHashMap[(*i)[1]] = (*i)[0].getRational();
        else
          sumHashMap[(*i)[1]] = sumHashMap[(*i)[1]] + (*i)[0].getRational();
      }
    }
  }

  sumKids.push_back(rat(constant));
  ExprMap<Rational>::iterator j = sumHashMap.begin();
  for(; j != sumHashMap.end(); ++j) {
    if(0 == (*j).second)
      ;//do nothing
    else if (1 == (*j).second)
      sumKids.push_back((*j).first);
    else
      sumKids.push_back(rat((*j).second) * (*j).first);
  }
  
  //constant is same as sumKids[0].
  //corner cases: "0 + monomial" and "constant"(no monomials)

  Expr ret;
  if(2 == sumKids.size() && 0 == constant) ret = sumKids[1];
  else if (1 == sumKids.size()) ret = sumKids[0];
  else ret = plusExpr(sumKids);

  if(withProof()) pf = newPf("canon_combo_like_terms",e,ret);  
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}





// e[0] kind e[1] <==> true when e[0] kind e[1],
// false when e[0] !kind e[1], for constants only
Theorem ArithTheoremProducer::constPredicate(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity() == 2 && isRational(e[0]) && isRational(e[1]),
                CLASS_NAME "::constPredicate:\n  "
                "non-const parameters: " + e.toString());
  }
  Proof pf;
  bool result(false);
  int kind = e.getKind();
  Rational r1 = e[0].getRational(), r2 = e[1].getRational();
  switch(kind) {
  case EQ:
    result = (r1 == r2)?true : false; 
    break;
  case LT:
    result = (r1 < r2)?true : false; 
    break;
  case LE:
    result = (r1 <= r2)?true : false; 
    break;
  case GT:
    result = (r1 > r2)?true : false; 
    break;
  case GE:
    result = (r1 >= r2)?true : false; 
    break;
  default:
    if(CHECK_PROOFS) {
      CHECK_SOUND(false,
                  "ArithTheoremProducer::constPredicate: wrong kind");
    }
    break;
  }
  Expr ret = (result) ? d_em->trueExpr() : d_em->falseExpr();
  if(withProof()) pf = newPf("const_predicate", e,ret);
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}

// e[0] kind e[1] <==> 0 kind e[1] - e[0]
Theorem ArithTheoremProducer::rightMinusLeft(const Expr& e)
{
  Proof pf;
  int kind = e.getKind();
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) || 
                (LT==kind) || 
                (LE==kind) || 
                (GE==kind) || 
                (GT==kind),
                "ArithTheoremProduder::rightMinusLeft: wrong kind");
  }
  if(withProof()) pf = newPf("right_minus_left",e);
  return newRWTheorem(e, Expr(e.getOp(), rat(0), e[1] - e[0]), Assumptions::emptyAssump(), pf);
}


// x kind y <==> x + z kind y + z
Theorem ArithTheoremProducer::plusPredicate(const Expr& x, 
                                      const Expr& y,
                                      const Expr& z, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((EQ==kind) || 
                (LT==kind) || 
                (LE==kind) || 
                (GE==kind) || 
                (GT==kind),
                "ArithTheoremProduder::plusPredicate: wrong kind");
  }
  Proof pf;
  Expr left = Expr(kind, x, y);
  Expr right = Expr(kind, x + z, y + z);
  if(withProof()) pf = newPf("plus_predicate",left,right);
  return newRWTheorem(left, right, Assumptions::emptyAssump(), pf);
}

// x = y <==> x * z = y * z
Theorem ArithTheoremProducer::multEqn(const Expr& x, 
                                      const Expr& y,
                                      const Expr& z) {
  Proof pf;
  if(CHECK_PROOFS)
    CHECK_SOUND(z.isRational() && z.getRational() != 0,
		"ArithTheoremProducer::multEqn(): multiplying equation by 0");
  if(withProof()) pf = newPf("mult_eqn", x, y, z);
  return newRWTheorem(x.eqExpr(y), (x * z).eqExpr(y * z), Assumptions::emptyAssump(), pf);
}


// if z is +ve, return e[0] LT|LE|GT|GE e[1] <==> e[0]*z LT|LE|GT|GE e[1]*z
// if z is -ve, return e[0] LT|LE|GT|GE e[1] <==> e[1]*z LT|LE|GT|GE e[0]*z
Theorem ArithTheoremProducer::multIneqn(const Expr& e, const Expr& z)
{
  int kind = e.getKind();

  if(CHECK_PROOFS) {
    CHECK_SOUND((LT==kind) || 
                (LE==kind) || 
                (GE==kind) || 
                (GT==kind),
                "ArithTheoremProduder::multIneqn: wrong kind");    
    CHECK_SOUND(z.isRational() && z.getRational() != 0,
                "ArithTheoremProduder::multIneqn: "
		"z must be non-zero rational: " + z.toString());
  }
  Op op(e.getOp());
  Proof pf;

  Expr ret;
  if(0 < z.getRational())
    ret = Expr(op, e[0]*z, e[1]*z);
  else
    ret = Expr(op, e[1]*z, e[0]*z);
  if(withProof()) pf = newPf("mult_ineqn", e, ret);  
  return newRWTheorem(e, ret, Assumptions::emptyAssump(), pf);
}


// "op1 GE|GT op2" <==> op2 LE|LT op1
Theorem ArithTheoremProducer::flipInequality(const Expr& e)
{
  Proof pf;
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGT(e) || isGE(e),
                "ArithTheoremProducer::flipInequality: wrong kind: " + 
                e.toString());
  }
  
  int kind = isGE(e) ? LE : LT; 
  Expr ret =  Expr(kind, e[1], e[0]);
  if(withProof()) pf = newPf("flip_inequality", e,ret);
  return newRWTheorem(e,ret, Assumptions::emptyAssump(), pf);
}


// NOT (op1 LT op2)  <==> (op1 GE op2)
// NOT (op1 LE op2)  <==> (op1 GT op2)
// NOT (op1 GT op2)  <==> (op1 LE op2)
// NOT (op1 GE op2)  <==> (op1 LT op2)
Theorem ArithTheoremProducer::negatedInequality(const Expr& e)
{
  const Expr& ineq = e[0];
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot(),
                "ArithTheoremProducer::negatedInequality: wrong kind: " +
                e.toString());
    CHECK_SOUND(isIneq(ineq),
                "ArithTheoremProducer::negatedInequality: wrong kind: " +
                (ineq).toString());
  }
  Proof pf;
  if(withProof()) pf = newPf("negated_inequality", e);

  int kind;
  // NOT (op1 LT op2)  <==> (op1 GE op2)
  // NOT (op1 LE op2)  <==> (op1 GT op2)
  // NOT (op1 GT op2)  <==> (op1 LE op2)
  // NOT (op1 GE op2)  <==> (op1 LT op2)
  kind = 
    isLT(ineq) ? GE : 
    isLE(ineq) ? GT : 
    isGT(ineq) ? LE : 
    LT;
  return newRWTheorem(e, Expr(kind, ineq[0], ineq[1]), Assumptions::emptyAssump(), pf);
}

//takes two ineqs "|- alpha LT|LE t" and "|- t LT|LE beta"
//and returns "|- alpha LT|LE beta"
Theorem ArithTheoremProducer::realShadow(const Theorem& alphaLTt, 
                                         const Theorem& tLTbeta)
{
  const Expr& expr1 = alphaLTt.getExpr();
  const Expr& expr2 = tLTbeta.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND((isLE(expr1) || isLT(expr1)) &&
                (isLE(expr2) || isLT(expr2)),
                "ArithTheoremProducer::realShadow: Wrong Kind: " + 
                alphaLTt.toString() +  tLTbeta.toString());
    
    CHECK_SOUND(expr1[1] == expr2[0], 
                "ArithTheoremProducer::realShadow:" 
                " t must be same for both inputs: " +
                expr1[1].toString() + " , " + expr2[0].toString());
  }
  Assumptions a(alphaLTt, tLTbeta);
  int firstKind = expr1.getKind();
  int secondKind = expr2.getKind();
  int kind = (firstKind == secondKind) ? firstKind : LT;
  Proof pf; 
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(alphaLTt.getProof());
    pfs.push_back(tLTbeta.getProof());
    pf = newPf("real_shadow",expr1, expr2, pfs);
  }
  return newTheorem(Expr(kind, expr1[0], expr2[1]), a, pf); 
}

//! alpha <= t <= alpha ==> t = alpha

/*! takes two ineqs "|- alpha LE t" and "|- t LE alpha"
  and returns "|- t = alpha"
*/
Theorem ArithTheoremProducer::realShadowEq(const Theorem& alphaLEt, 
                                           const Theorem& tLEalpha)
{
  const Expr& expr1 = alphaLEt.getExpr();
  const Expr& expr2 = tLEalpha.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducer::realShadowLTLE: Wrong Kind: " + 
                alphaLEt.toString() +  tLEalpha.toString());
    
    CHECK_SOUND(expr1[1] == expr2[0], 
                "ArithTheoremProducer::realShadowLTLE:" 
                " t must be same for both inputs: " +
                alphaLEt.toString() + " , " + tLEalpha.toString());

    CHECK_SOUND(expr1[0] == expr2[1], 
                "ArithTheoremProducer::realShadowLTLE:" 
                " alpha must be same for both inputs: " +
                alphaLEt.toString() + " , " + tLEalpha.toString());
  }
  Assumptions a(alphaLEt, tLEalpha);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(alphaLEt.getProof());
    pfs.push_back(tLEalpha.getProof());
    pf = newPf("real_shadow_eq", alphaLEt.getExpr(), tLEalpha.getExpr(), pfs);
  }
  return newRWTheorem(expr1[0], expr1[1], a, pf);
}

Theorem 
ArithTheoremProducer::finiteInterval(const Theorem& aLEt,
				     const Theorem& tLEac,
				     const Theorem& isInta,
				     const Theorem& isIntt) {
  const Expr& e1 = aLEt.getExpr();
  const Expr& e2 = tLEac.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(e1) && isLE(e2),
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // term 't' is the same in both inequalities
    CHECK_SOUND(e1[1] == e2[0],
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // RHS in e2 is (a+c)
    CHECK_SOUND(isPlus(e2[1]) && e2[1].arity() == 2,
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // term 'a' in LHS of e1 and RHS of e2 is the same
    CHECK_SOUND(e1[0] == e2[1][0],
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // 'c' in the RHS of e2 is a positive integer constant
    CHECK_SOUND(e2[1][1].isRational() && e2[1][1].getRational().isInteger()
		&& e2[1][1].getRational() >= 1,
		"ArithTheoremProducer::finiteInterval:\n e1 = "
		+e1.toString()+"\n e2 = "+e2.toString());
    // Integrality constraints
    const Expr& isIntaExpr = isInta.getExpr();
    const Expr& isInttExpr = isIntt.getExpr();
    CHECK_SOUND(isIntPred(isIntaExpr) && isIntaExpr[0] == e1[0],
		"Wrong integrality constraint:\n e1 = "
		+e1.toString()+"\n isInta = "+isIntaExpr.toString());
    CHECK_SOUND(isIntPred(isInttExpr) && isInttExpr[0] == e1[1],
		"Wrong integrality constraint:\n e1 = "
		+e1.toString()+"\n isIntt = "+isInttExpr.toString());
  }
  vector<Theorem> thms;
  thms.push_back(aLEt);
  thms.push_back(tLEac);
  thms.push_back(isInta);
  thms.push_back(isIntt);
  Assumptions a(thms);
  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e1);
    es.push_back(e2);
    es.push_back(isInta.getExpr());
    es.push_back(isIntt.getExpr());
    pfs.push_back(aLEt.getProof());
    pfs.push_back(tLEac.getProof());
    pfs.push_back(isInta.getProof());
    pfs.push_back(isIntt.getProof());
    pf = newPf("finite_interval", es, pfs);
  }
  // Construct GRAY_SHADOW(t, a, 0, c)
  Expr g(grayShadow(e1[1], e1[0], 0, e2[1][1].getRational()));
  return newTheorem(g, a, pf);
}


// Dark & Gray shadows when a <= b
Theorem ArithTheoremProducer::darkGrayShadow2ab(const Theorem& betaLEbx, 
						const Theorem& axLEalpha,
						const Theorem& isIntAlpha,
						const Theorem& isIntBeta,
						const Theorem& isIntx) {
  const Expr& expr1 = betaLEbx.getExpr();
  const Expr& expr2 = axLEalpha.getExpr();
  const Expr& isIntAlphaExpr = isIntAlpha.getExpr();
  const Expr& isIntBetaExpr = isIntBeta.getExpr();
  const Expr& isIntxExpr = isIntx.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducer::darkGrayShadow2ab: Wrong Kind: " + 
                betaLEbx.toString() +  axLEalpha.toString());
  }

  const Expr& beta = expr1[0];
  const Expr& bx = expr1[1];
  const Expr& ax = expr2[0];
  const Expr& alpha = expr2[1];
  Rational a = isMult(ax)? ax[0].getRational() : 1;
  Rational b = isMult(bx)? bx[0].getRational() : 1;
  const Expr& x = isMult(ax)? ax[1] : ax;

  if(CHECK_PROOFS) {
    // Integrality constraints
    CHECK_SOUND(isIntPred(isIntAlphaExpr) && isIntAlphaExpr[0] == alpha,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n alpha = "
		+alpha.toString()+"\n isIntAlpha = "
		+isIntAlphaExpr.toString());
    CHECK_SOUND(isIntPred(isIntBetaExpr) && isIntBetaExpr[0] == beta,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n beta = "
		+beta.toString()+"\n isIntBeta = "
		+isIntBetaExpr.toString());
    CHECK_SOUND(isIntPred(isIntxExpr) && isIntxExpr[0] == x,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n x = "
		+x.toString()+"\n isIntx = "
		+isIntxExpr.toString());
    // Expressions ax and bx should match on x
    CHECK_SOUND(!isMult(ax) || ax.arity() == 2,
		"ArithTheoremProducer::darkGrayShadow2ab:\n ax<=alpha: " +
                axLEalpha.toString());
    CHECK_SOUND(!isMult(bx) || (bx.arity() == 2 && bx[1] == x),
		"ArithTheoremProducer::darkGrayShadow2ab:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
    CHECK_SOUND(1 <= a && a <= b && 2 <= b,
		"ArithTheoremProducer::darkGrayShadow2ab:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
  }
  vector<Theorem> thms;
  thms.push_back(betaLEbx);
  thms.push_back(axLEalpha);
  thms.push_back(isIntAlpha);
  thms.push_back(isIntBeta);
  thms.push_back(isIntx);
  Assumptions A(thms);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(betaLEbx.getProof());
    pfs.push_back(axLEalpha.getProof());
    pfs.push_back(isIntAlpha.getProof());
    pfs.push_back(isIntBeta.getProof());
    pfs.push_back(isIntx.getProof());
    
    pf = newPf("dark_grayshadow_2ab", expr1, expr2, pfs);
  }
  
  Expr bAlpha = multExpr(rat(b), alpha);
  Expr aBeta = multExpr(rat(a), beta);
  Expr t = minusExpr(bAlpha, aBeta);
  Expr d = darkShadow(rat(a*b-1), t);
  Expr g = grayShadow(ax, alpha, -a+1, 0);
  return newTheorem((d || g) && (!d || !g), A, pf);
}

// Dark & Gray shadows when b <= a
Theorem ArithTheoremProducer::darkGrayShadow2ba(const Theorem& betaLEbx, 
						const Theorem& axLEalpha,
						const Theorem& isIntAlpha,
						const Theorem& isIntBeta,
						const Theorem& isIntx) {
  const Expr& expr1 = betaLEbx.getExpr();
  const Expr& expr2 = axLEalpha.getExpr();
  const Expr& isIntAlphaExpr = isIntAlpha.getExpr();
  const Expr& isIntBetaExpr = isIntBeta.getExpr();
  const Expr& isIntxExpr = isIntx.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(isLE(expr1) && isLE(expr2),
                "ArithTheoremProducer::darkGrayShadow2ba: Wrong Kind: " + 
                betaLEbx.toString() +  axLEalpha.toString());
  }

  const Expr& beta = expr1[0];
  const Expr& bx = expr1[1];
  const Expr& ax = expr2[0];
  const Expr& alpha = expr2[1];
  Rational a = isMult(ax)? ax[0].getRational() : 1;
  Rational b = isMult(bx)? bx[0].getRational() : 1;
  const Expr& x = isMult(ax)? ax[1] : ax;

  if(CHECK_PROOFS) {
    // Integrality constraints
    CHECK_SOUND(isIntPred(isIntAlphaExpr) && isIntAlphaExpr[0] == alpha,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n alpha = "
		+alpha.toString()+"\n isIntAlpha = "
		+isIntAlphaExpr.toString());
    CHECK_SOUND(isIntPred(isIntBetaExpr) && isIntBetaExpr[0] == beta,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n beta = "
		+beta.toString()+"\n isIntBeta = "
		+isIntBetaExpr.toString());
    CHECK_SOUND(isIntPred(isIntxExpr) && isIntxExpr[0] == x,
		"ArithTheoremProducer::darkGrayShadow2ab:\n "
		"wrong integrality constraint:\n x = "
		+x.toString()+"\n isIntx = "
		+isIntxExpr.toString());
    // Expressions ax and bx should match on x
    CHECK_SOUND(!isMult(ax) || ax.arity() == 2,
		"ArithTheoremProducer::darkGrayShadow2ba:\n ax<=alpha: " +
                axLEalpha.toString());
    CHECK_SOUND(!isMult(bx) || (bx.arity() == 2 && bx[1] == x),
		"ArithTheoremProducer::darkGrayShadow2ba:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
    CHECK_SOUND(1 <= b && b <= a && 2 <= a,
		"ArithTheoremProducer::darkGrayShadow2ba:\n beta<=bx: "
		+betaLEbx.toString()
		+"\n ax<=alpha: "+ axLEalpha.toString());
  }
  vector<Theorem> thms;
  thms.push_back(betaLEbx);
  thms.push_back(axLEalpha);
  thms.push_back(isIntAlpha);
  thms.push_back(isIntBeta);
  thms.push_back(isIntx);
  Assumptions A(thms);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(betaLEbx.getProof());
    pfs.push_back(axLEalpha.getProof());
    pfs.push_back(isIntAlpha.getProof());
    pfs.push_back(isIntBeta.getProof());
    pfs.push_back(isIntx.getProof());
    
    pf = newPf("dark_grayshadow_2ba", betaLEbx.getExpr(),
	       axLEalpha.getExpr(), pfs);
  }
  
  Expr bAlpha = multExpr(rat(b), alpha);
  Expr aBeta = multExpr(rat(a), beta);
  Expr t = minusExpr(bAlpha, aBeta);
  Expr d = darkShadow(rat(a*b-1), t);
  Expr g = grayShadow(bx, beta, 0, b-1);
  return newTheorem((d || g) && (!d || !g), A, pf);
}

/*! takes a dark shadow and expands it into an inequality.
*/
Theorem ArithTheoremProducer::expandDarkShadow(const Theorem& darkShadow) {
  const Expr& theShadow = darkShadow.getExpr();
  if(CHECK_PROOFS){
    CHECK_SOUND(isDarkShadow(theShadow),
		"ArithTheoremProducer::expandDarkShadow: not DARK_SHADOW: " +
		theShadow.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("expand_dark_shadow", theShadow, darkShadow.getProof());
  return newTheorem(leExpr(theShadow[0], theShadow[1]), darkShadow.getAssumptionsRef(), pf);
}


// takes a grayShadow (c1==c2) and expands it into an equality
Theorem ArithTheoremProducer::expandGrayShadow0(const Theorem& grayShadow) {
  const Expr& theShadow = grayShadow.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst0:"
		" not GRAY_SHADOW: " +
		theShadow.toString());
    CHECK_SOUND(theShadow[2] == theShadow[3],
		"ArithTheoremProducer::expandGrayShadow0: c1!=c2: " +
		theShadow.toString());
  }
  Proof pf;
  if(withProof()) pf = newPf("expand_gray_shadowconst0", theShadow,
			     grayShadow.getProof());
  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];
  return newRWTheorem(v, e + theShadow[2], grayShadow.getAssumptionsRef(), pf);
}


// G ==> (G1 or G2) and (!G1 or !G2),
// where G  = G(x, e, c1, c2),
//       G1 = G(x,e,c1,c)
//       G2 = G(x,e,c+1,c2),
// and    c = floor((c1+c2)/2)
Theorem ArithTheoremProducer::splitGrayShadow(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducer::expandGrayShadow: " +
		theShadow.toString());
  }

  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];

  Proof pf;
  if(withProof())
    pf = newPf("expand_gray_shadow", theShadow, gThm.getProof());
  Rational c(floor((c1+c2) / 2));
  Expr g1(grayShadow(v, e, c1, c));
  Expr g2(grayShadow(v, e, c+1, c2));
  return newTheorem((g1 || g2) && (!g1 || !g2), gThm.getAssumptionsRef(), pf);
}


Theorem ArithTheoremProducer::expandGrayShadow(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst: not a shadow" +
		theShadow.toString());
  }

  const Rational& c1 = theShadow[2].getRational();
  const Rational& c2 = theShadow[3].getRational();

  if(CHECK_PROOFS) {
    CHECK_SOUND(c1.isInteger() && c2.isInteger() && c1 < c2,
		"ArithTheoremProducer::expandGrayShadow: " +
		theShadow.toString());
  }

  const Expr& v = theShadow[0];
  const Expr& e = theShadow[1];

  Proof pf;
  if(withProof())
    pf = newPf("expand_gray_shadow", theShadow, gThm.getProof());
  Expr ineq1(leExpr(e+rat(c1), v));
  Expr ineq2(leExpr(v, e+rat(c2)));
  return newTheorem(ineq1 && ineq2, gThm.getAssumptionsRef(), pf);
}


// Expanding GRAY_SHADOW(a*x, c, b), where c is a constant
Theorem
ArithTheoremProducer::expandGrayShadowConst(const Theorem& gThm) {
  const Expr& theShadow = gThm.getExpr();
  const Expr& ax = theShadow[0];
  const Expr& cExpr = theShadow[1];
  const Expr& bExpr = theShadow[2];

  if(CHECK_PROOFS) {
    CHECK_SOUND(!isMult(ax) || ax[0].isRational(),
		"ArithTheoremProducer::expandGrayShadowConst: "
		"'a' in a*x is not a const: " +theShadow.toString());
  }

  Rational a = isMult(ax)? ax[0].getRational() : 1;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isGrayShadow(theShadow),
		"ArithTheoremProducer::expandGrayShadowConst: "
		"not a GRAY_SHADOW: " +theShadow.toString());
    CHECK_SOUND(a.isInteger() && a >= 1,
		"ArithTheoremProducer::expandGrayShadowConst: "
		"'a' is not integer: " +theShadow.toString());
    CHECK_SOUND(cExpr.isRational(),
		"ArithTheoremProducer::expandGrayShadowConst: "
		"'c' is not rational" +theShadow.toString());
    CHECK_SOUND(bExpr.isRational() && bExpr.getRational().isInteger(),
		"ArithTheoremProducer::expandGrayShadowConst: b not integer: "
		+theShadow.toString());
  }

  const Rational& b = bExpr.getRational();
  const Rational& c = cExpr.getRational();
  Rational j = constRHSGrayShadow(c,b,a);
  // Compute sign(b)*j(c,b,a)
  Rational signB = (b>0)? 1 : -1;
  // |b| (absolute value of b)
  Rational bAbs = abs(b);

  const Assumptions& assump(gThm.getAssumptionsRef());
  Proof pf;
  Theorem conc;  // Conclusion of the rule

  if(bAbs < j) {
    if(withProof())
      pf = newPf("expand_gray_shadow_const_0", theShadow,
		 gThm.getProof());
    conc = newTheorem(d_em->falseExpr(), assump, pf);
  } else if(bAbs < a+j) {
    if(withProof())
      pf = newPf("expand_gray_shadow_const_1", theShadow,
		 gThm.getProof());
    conc = newRWTheorem(ax, rat(c+b-signB*j), assump, pf);
  } else {
    if(withProof())
      pf = newPf("expand_gray_shadow_const", theShadow,
		 gThm.getProof());
    Expr newGrayShadow(Expr(GRAY_SHADOW, ax, cExpr, rat(b-signB*(a+j))));
    conc = newTheorem(ax.eqExpr(rat(c+b-signB*j)).orExpr(newGrayShadow),
		      assump, pf);
  }

  return conc;
}


Theorem
ArithTheoremProducer::grayShadowConst(const Theorem& gThm) {
  const Expr& g = gThm.getExpr();
  bool checkProofs(CHECK_PROOFS);
  if(checkProofs) {
    CHECK_SOUND(isGrayShadow(g), "ArithTheoremProducer::grayShadowConst("
		+g.toString()+")");
  }

  const Expr& ax = g[0];
  const Expr& e = g[1];
  const Rational& c1 = g[2].getRational();
  const Rational& c2 = g[3].getRational();
  Expr aExpr, x;
  d_theoryArith->separateMonomial(ax, aExpr, x);

  if(checkProofs) {
    CHECK_SOUND(e.isRational() && e.getRational().isInteger(),
		"ArithTheoremProducer::grayShadowConst("+g.toString()+")");
    CHECK_SOUND(aExpr.isRational(),
		"ArithTheoremProducer::grayShadowConst("+g.toString()+")");
  }

  const Rational& a = aExpr.getRational();
  const Rational& c = e.getRational();

  if(checkProofs) {
    CHECK_SOUND(a.isInteger() && a >= 2,
		"ArithTheoremProducer::grayShadowConst("+g.toString()+")");
  }

  Rational newC1 = ceil((c1+c)/a), newC2 = floor((c2+c)/a);
  Expr newG((newC1 > newC2)? d_em->falseExpr()
	    : grayShadow(x, rat(0), newC1, newC2));
  Proof pf;
  if(withProof())
    pf = newPf("gray_shadow_const", g, gThm.getProof());
  return newTheorem(newG, gThm.getAssumptionsRef(), pf);
}


Rational ArithTheoremProducer::constRHSGrayShadow(const Rational& c,
						  const Rational& b,
						  const Rational& a) {
  DebugAssert(c.isInteger() &&
	      b.isInteger() &&
	      a.isInteger() &&
	      b != 0,
	      "ArithTheoremProducer::constRHSGrayShadow: a, b, c must be ints");
  if (b > 0)
    return mod(c+b, a);
  else
    return mod(a-(c+b), a);
}

/*! Takes a Theorem(\\alpha < \\beta) and returns 
 *  Theorem(\\alpha < \\beta <==> \\alpha <= \\beta -1)
 * where \\alpha and \\beta are integer expressions
 */
Theorem ArithTheoremProducer::lessThanToLE(const Theorem& less,
					   const Theorem& isIntLHS,
					   const Theorem& isIntRHS,
					   bool changeRight) {
  const Expr& ineq = less.getExpr();
  const Expr& isIntLHSexpr = isIntLHS.getExpr();
  const Expr& isIntRHSexpr = isIntRHS.getExpr();
  
  if(CHECK_PROOFS) {
    CHECK_SOUND(isLT(ineq),
		"ArithTheoremProducer::LTtoLE: ineq must be <");
    // Integrality check
    CHECK_SOUND(isIntPred(isIntLHSexpr)	&& isIntLHSexpr[0] == ineq[0],
		"ArithTheoremProducer::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntLHS = "
		+isIntLHSexpr.toString());
    CHECK_SOUND(isIntPred(isIntRHSexpr) && isIntRHSexpr[0] == ineq[1],
		"ArithTheoremProducer::lessThanToLE: bad integrality check:\n"
		" ineq = "+ineq.toString()+"\n isIntRHS = "
		+isIntRHSexpr.toString());
  }
  vector<Theorem> thms;
  thms.push_back(less);
  thms.push_back(isIntLHS);
  thms.push_back(isIntRHS);
  Assumptions a(thms);
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(less.getProof());
    pfs.push_back(isIntLHS.getProof());
    pfs.push_back(isIntRHS.getProof());
    pf = newPf(changeRight? "lessThan_To_LE_rhs" : "lessThan_To_LE_lhs",
	       ineq, pfs);
  }
  Expr le = changeRight?
    leExpr(ineq[0], ineq[1] + rat(-1))
    : leExpr(ineq[0] + rat(1), ineq[1]);
  return newRWTheorem(ineq, le, a, pf);
}


/*! \param eqn is an equation 0 = a.x or 0 = c + a.x
 *  \param isIntx is a proof of IS_INTEGER(x)
 *
 * \return the theorem 0 = c + a.x <==> x=-c/a if -c/a is int else
 *  return the theorem 0 = c + a.x <==> false.
 *
 * It also handles the special case of 0 = a.x <==> x = 0
 */
Theorem 
ArithTheoremProducer::intVarEqnConst(const Expr& eqn,
				     const Theorem& isIntx) {
  const Expr& left(eqn[0]);
  const Expr& right(eqn[1]);
  const Expr& isIntxexpr(isIntx.getExpr());

  if(CHECK_PROOFS) {
    CHECK_SOUND((isMult(right) && right[0].isRational())
                || (right.arity() == 2 && isPlus(right)
                    && right[0].isRational()
                    && ((!isMult(right[1]) || right[1][0].isRational()))),
                "ArithTheoremProducer::intVarEqnConst: "
		"rhs has a wrong format: " + right.toString());
    CHECK_SOUND(left.isRational() && 0 == left.getRational(),
                "ArithTheoremProducer:intVarEqnConst:left is not a zero: " +
                left.toString());
  }
  // Integrality constraint
  Expr x(right);
  Rational a(1), c(0);
  if(isMult(right)) {
    Expr aExpr;
    d_theoryArith->separateMonomial(right, aExpr, x);
    a = aExpr.getRational();
  } else { // right is a PLUS
    c = right[0].getRational();
    Expr aExpr;
    d_theoryArith->separateMonomial(right[1], aExpr, x);
    a = aExpr.getRational();
  }
  if(CHECK_PROOFS) {
    CHECK_SOUND(isIntPred(isIntxexpr) && isIntxexpr[0] == x,
                "ArithTheoremProducer:intVarEqnConst: "
		"bad integrality constraint:\n right = " +
                right.toString()+"\n isIntx = "+isIntxexpr.toString());
    CHECK_SOUND(a!=0, "ArithTheoremProducer:intVarEqnConst: eqn = "
		+eqn.toString());
  }
  const Assumptions& assump(isIntx.getAssumptionsRef());
  Proof pf;
  if(withProof())
    pf = newPf("int_const_eq", eqn, isIntx.getProof());

  // Solve for x:   x = r = -c/a
  Rational r(-c/a);

  if(r.isInteger())
    return newRWTheorem(eqn, x.eqExpr(rat(r)), assump, pf);
  else
    return newRWTheorem(eqn, d_em->falseExpr(), assump, pf);
}


Expr
ArithTheoremProducer::create_t(const Expr& eqn) {
  const Expr& lhs = eqn[0];
  DebugAssert(isMult(lhs),
              CLASS_NAME "create_t : lhs must be a MULT"
              + lhs.toString());
  const Expr& x = lhs[1];
  Rational m = lhs[0].getRational()+1;
  DebugAssert(m > 0, "ArithTheoremProducer::create_t: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(eqn[1]))
    sumModM(kids, eqn[1], m, m);
  else
    kids.push_back(monomialModM(eqn[1], m, m));
  
  kids.push_back(multExpr(rat(1/m), x));
  return plusExpr(kids);
}

Expr
ArithTheoremProducer::create_t2(const Expr& lhs, const Expr& rhs,
				const Expr& sigma) {
  Rational m = lhs[0].getRational()+1;
  DebugAssert(m > 0, "ArithTheoremProducer::create_t2: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(rhs))
    sumModM(kids, rhs, m, -1);
  else {
    kids.push_back(rat(0)); // For canonical form
    Expr monom = monomialModM(rhs, m, -1);
    if(!monom.isRational())
      kids.push_back(monom);
    else 
      DebugAssert(monom.getRational() == 0, "");
  }
  kids.push_back(rat(m)*sigma);
  return plusExpr(kids);
}

Expr
ArithTheoremProducer::create_t3(const Expr& lhs, const Expr& rhs,
				const Expr& sigma) {
  const Rational& a = lhs[0].getRational();
  Rational m = a+1;
  DebugAssert(m > 0, "ArithTheoremProducer::create_t3: m = "+m.toString());
  vector<Expr> kids;
  if(isPlus(rhs))
    sumMulF(kids, rhs, m, 1);
  else {
    kids.push_back(rat(0)); // For canonical form
    Expr monom = monomialMulF(rhs, m, 1);
    if(!monom.isRational())
      kids.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
  kids.push_back(rat(-a)*sigma);
  return plusExpr(kids);
}

Rational
ArithTheoremProducer::modEq(const Rational& i, const Rational& m) {
  DebugAssert(m > 0, "ArithTheoremProducer::modEq: m = "+m.toString());
  Rational half(1,2);
  Rational res((i - m*(floor((i/m) + half))));
  TRACE("arith eq", "modEq("+i.toString()+", "+m.toString()+") = ", res, "");
  return res;
}

Rational
ArithTheoremProducer::f(const Rational& i, const Rational& m) {
  DebugAssert(m > 0, "ArithTheoremProducer::f: m = "+m.toString());
  Rational half(1,2);
  return (floor(i/m + half)+modEq(i,m));
}

void
ArithTheoremProducer::sumModM(vector<Expr>& summands, const Expr& sum,
                              const Rational& m, const Rational& divisor) {
  DebugAssert(divisor != 0, "ArithTheoremProducer::sumModM: divisor = "
	      +divisor.toString());
  Expr::iterator i = sum.begin();
  DebugAssert(i != sum.end(), CLASS_NAME "::sumModM");
  Rational C = i->getRational();
  C = modEq(C,m)/divisor;
  summands.push_back(rat(C));
  i++;
  for(Expr::iterator iend=sum.end(); i!=iend; ++i) {
    Expr monom = monomialModM(*i, m, divisor);
    if(!monom.isRational())
      summands.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
}

Expr
ArithTheoremProducer::monomialModM(const Expr& i,
                                   const Rational& m, const Rational& divisor)
{
  DebugAssert(divisor != 0, "ArithTheoremProducer::monomialModM: divisor = "
	      +divisor.toString());
  Expr res;
  if(isMult(i)) {
    Rational ai = i[0].getRational();
    ai = modEq(ai,m)/divisor;
    if(0 == ai) res = rat(0);
    else if(1 == ai && i.arity() == 2) res = i[1];
    else {
      vector<Expr> kids = i.getKids();
      kids[0] = rat(ai);
      res = multExpr(kids);
    }
  } else { // It's a single variable
    Rational ai = modEq(1,m)/divisor;
    if(1 == ai) res = i;
    else res = rat(ai)*i;
  }
  DebugAssert(!res.isNull(), "ArithTheoremProducer::monomialModM()");
  TRACE("arith eq", "monomialModM(i="+i.toString()+", m="+m.toString()
	+", div="+divisor.toString()+") = ", res, "");
  return res;
}

void
ArithTheoremProducer::sumMulF(vector<Expr>& summands, const Expr& sum,
                              const Rational& m, const Rational& divisor) {
  DebugAssert(divisor != 0, "ArithTheoremProducer::sumMulF: divisor = "
	      +divisor.toString());
  Expr::iterator i = sum.begin();
  DebugAssert(i != sum.end(), CLASS_NAME "::sumModM");
  Rational C = i->getRational();
  C = f(C,m)/divisor;
  summands.push_back(rat(C));
  i++;
  for(Expr::iterator iend=sum.end(); i!=iend; ++i) {
    Expr monom = monomialMulF(*i, m, divisor);
    if(!monom.isRational())
      summands.push_back(monom);
    else
      DebugAssert(monom.getRational() == 0, "");
  }
}

Expr
ArithTheoremProducer::monomialMulF(const Expr& i,
                                   const Rational& m, const Rational& divisor)
{
  DebugAssert(divisor != 0, "ArithTheoremProducer::monomialMulF: divisor = "
	      +divisor.toString());
  Rational ai = isMult(i) ? (i)[0].getRational() : 1;
  Expr xi = isMult(i) ? (i)[1] : (i);
  ai = f(ai,m)/divisor;
  if(0 == ai) return rat(0);
  if(1 == ai) return xi;
  return multExpr(rat(ai), xi);
}

// This recursive function accepts a term, t, and a 'map' of
// substitutions [x1/t1, x2/t2,...,xn/tn].  it returns a t' which is
// basically t[x1/t1,x2/t2...xn/tn]
Expr
ArithTheoremProducer::substitute(const Expr& term, ExprMap<Expr>& eMap)
{
  ExprMap<Expr>::iterator i, iend = eMap.end();

  i = eMap.find(term);
  if(iend != i)
    return (*i).second;

  if (isMult(term)) {
    //in this case term is of the form c.x
    i = eMap.find(term[1]);
    if(iend != i)
      return term[0]*(*i).second;
    else
      return term;
  }

  if(isPlus(term)) {
    vector<Expr> output;
    for(Expr::iterator j = term.begin(), jend = term.end(); j != jend; ++j)
      output.push_back(substitute(*j, eMap));
    return plusExpr(output);
  }
  return term;    
}

bool ArithTheoremProducer::greaterthan(const Expr & l, const Expr & r)
{
  //    DebugAssert(l != r, "");
  if (l==r) return false;
    
  switch(l.getKind()) {
  case RATIONAL_EXPR:
    DebugAssert(!r.isRational(), "");
    return true;
    break;
  case POW:
    switch (r.getKind()) {
    case RATIONAL_EXPR:
      // TODO:
      // alternately I could return (not greaterthan(r,l))
      return false;
      break;
    case POW:
      // x^n > y^n if x > y
      // x^n1 > x^n2 if n1 > n2
      return 
        ((r[1] < l[1]) || 
         ((r[1]==l[1]) && (r[0].getRational() < l[0].getRational())));
      break;
            
    case MULT:
      DebugAssert(r.arity() > 1, "");
      DebugAssert((r.arity() > 2) || (r[1] != l), "");
      if (r[1] == l) return false;
      return greaterthan(l, r[1]);
      break;
    case PLUS:
      DebugAssert(false, "");
      return true;
      break;
    default:
      // leaf
      return ((r < l[1]) || ((r == l[1]) && l[0].getRational() > 1));
      break;
    }
    break;
  case MULT:
    DebugAssert(l.arity() > 1, "");
    switch (r.getKind()) {
    case RATIONAL_EXPR:
      return false;
      break;
    case POW:
      DebugAssert(l.arity() > 1, "");
      DebugAssert((l.arity() > 2) || (l[1] != r), "");
      // TODO:
      // alternately return (not greaterthan(r,l)
      return ((l[1] == r) || greaterthan(l[1], r));
      break;
    case MULT:
      {
            
        DebugAssert(r.arity() > 1, "");
        Expr::iterator i = l.begin();
        Expr::iterator j = r.begin();
        ++i;
        ++j;
        for (; i != l.end() && j != r.end(); ++i, ++j) {
          if (*i == *j)
            continue;
          return greaterthan(*i,*j);
        }
        DebugAssert(i != l.end() || j != r.end(), "");
        if (i == l.end()) {
          // r is bigger
          return false;
        }
        else
          {
            // l is bigger
            return true;
          }
      }
      break;
    case PLUS:
      DebugAssert(false, "");
      return true;
      break;
    default:
      // leaf
      DebugAssert((l.arity() > 2) || (l[1] != r), "");
      return ((l[1] == r) || greaterthan(l[1], r));
      break;
    }
    break;
  case PLUS:
    DebugAssert(false, "");
    return true;
    break;
  default:
    // leaf
    switch (r.getKind()) {
    case RATIONAL_EXPR:
      return false;
      break;
    case POW:
      return ((r[1] < l) || ((r[1] == l) && (r[0].getRational() < 1)));
      break;
    case MULT:
      DebugAssert(r.arity() > 1, "");
      DebugAssert((r.arity() > 2) || (r[1] != l), "");
      if (l == r[1]) return false;
      return greaterthan(l,r[1]);
      break;
    case PLUS:
      DebugAssert(false, "");
      return true;
      break;
    default:
      // leaf
      return (r < l);
      break;
    }
    break;
  }
}


Theorem
ArithTheoremProducer::eqElimIntRule(const Theorem& eqn, const Theorem& isIntx,
				    const vector<Theorem>& isIntVars) {
  TRACE("arith eq", "eqElimIntRule(", eqn.getExpr(), ") {");
  Proof pf;

  if(CHECK_PROOFS)
    CHECK_SOUND(eqn.isRewrite(),
                "ArithTheoremProducer::eqElimInt: input must be an equation" +
                eqn.toString());

  const Expr& lhs = eqn.getLHS();
  const Expr& rhs = eqn.getRHS();
  Expr a, x;
  d_theoryArith->separateMonomial(lhs, a, x);

  if(CHECK_PROOFS) {
    // Checking LHS
    const Expr& isIntxe = isIntx.getExpr();
    CHECK_SOUND(isIntPred(isIntxe) && isIntxe[0] == x,
		"ArithTheoremProducer::eqElimInt\n eqn = "
		+eqn.getExpr().toString()
		+"\n isIntx = "+isIntxe.toString());
    CHECK_SOUND(isRational(a) && a.getRational().isInteger()
		&& a.getRational() >= 2,
		"ArithTheoremProducer::eqElimInt:\n lhs = "+lhs.toString());
    // Checking RHS
    // It cannot be a division (we don't handle it)
    CHECK_SOUND(!isDivide(rhs),
		"ArithTheoremProducer::eqElimInt:\n rhs = "+rhs.toString());
    // If it's a single monomial, then it's the only "variable"
    if(!isPlus(rhs)) {
      Expr c, v;
      d_theoryArith->separateMonomial(rhs, c, v);
      CHECK_SOUND(isIntVars.size() == 1
		  && isIntPred(isIntVars[0].getExpr())
		  && isIntVars[0].getExpr()[0] == v
		  && isRational(c) && c.getRational().isInteger(),
		  "ArithTheoremProducer::eqElimInt:\n rhs = "+rhs.toString()
		  +"isIntVars.size = "+int2string(isIntVars.size()));
    } else { // RHS is a plus
      CHECK_SOUND(isIntVars.size() + 1 == (size_t)rhs.arity(),
		  "ArithTheoremProducer::eqElimInt: rhs = "+rhs.toString());
      // Check the free constant
      CHECK_SOUND(isRational(rhs[0]) && rhs[0].getRational().isInteger(),
		  "ArithTheoremProducer::eqElimInt: rhs = "+rhs.toString());
      // Check the vars
      for(size_t i=0, iend=isIntVars.size(); i<iend; ++i) {
	Expr c, v;
	d_theoryArith->separateMonomial(rhs[i+1], c, v);
	const Expr& isInt(isIntVars[i].getExpr());
	CHECK_SOUND(isIntPred(isInt) && isInt[0] == v
		    && isRational(c) && c.getRational().isInteger(),
		    "ArithTheoremProducer::eqElimInt:\n rhs["+int2string(i+1)
		    +"] = "+rhs[i+1].toString()
		    +"\n isInt = "+isInt.toString());
      }
    }
  }

  // Creating a fresh bound variable
  static int varCount(0);
  Expr newVar = d_em->newBoundVarExpr("_int_var", int2string(varCount++));
  newVar.setType(intType());
  Expr t2 = create_t2(lhs, rhs, newVar);
  Expr t3 = create_t3(lhs, rhs, newVar);
  vector<Expr> vars;
  vars.push_back(newVar);
  Expr res = d_em->newClosureExpr(EXISTS, vars,
                                  x.eqExpr(t2) && rat(0).eqExpr(t3));
  
  vector<Theorem> thms(isIntVars);
  thms.push_back(isIntx);
  thms.push_back(eqn);
  Assumptions assump(thms);

  if(withProof()) {
    vector<Proof> pfs;
    pfs.push_back(eqn.getProof());
    pfs.push_back(isIntx.getProof());
    vector<Theorem>::const_iterator i=isIntVars.begin(), iend=isIntVars.end();
    for(; i!=iend; ++i) 
      pfs.push_back(i->getProof());
    pf = newPf("eq_elim_int", eqn.getExpr(), pfs);
  }

  Theorem thm(newTheorem(res, assump, pf));
  TRACE("arith eq", "eqElimIntRule => ", thm.getExpr(), " }");
  return thm;
}


Theorem
ArithTheoremProducer::isIntConst(const Expr& e) {
  Proof pf;

  if(CHECK_PROOFS) {
    CHECK_SOUND(isIntPred(e) && e[0].isRational(),
		"ArithTheoremProducer::isIntConst(e = "
		+e.toString()+")");
  }
  if(withProof())
    pf = newPf("is_int_const", e);
  bool isInt = e[0].getRational().isInteger();
  return newRWTheorem(e, isInt? d_em->trueExpr() : d_em->falseExpr(), Assumptions::emptyAssump(), pf);
}


Theorem
ArithTheoremProducer::equalLeaves1(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[1].getKind() == RATIONAL_EXPR &&
		e[1].getRational() == Rational(0) &&
		e[0].getKind() == PLUS &&
		e[0].arity() == 3 &&
		e[0][0].getKind() == RATIONAL_EXPR &&
		e[0][0].getRational() == Rational(0) &&
		e[0][1].getKind() == MULT &&
		e[0][1].arity() == 2 &&
		e[0][1][0].getKind() == RATIONAL_EXPR &&
		e[0][1][0].getRational() == Rational(-1),
		"equalLeaves1");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves1", e, pfs);
  }
  return newRWTheorem(e, e[0][1][1].eqExpr(e[0][2]), thm.getAssumptionsRef(), pf);
}


Theorem
ArithTheoremProducer::equalLeaves2(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == RATIONAL_EXPR &&
		e[0].getRational() == Rational(0) &&
		e[1].getKind() == PLUS &&
		e[1].arity() == 3 &&
		e[1][0].getKind() == RATIONAL_EXPR &&
		e[1][0].getRational() == Rational(0) &&
		e[1][1].getKind() == MULT &&
		e[1][1].arity() == 2 &&
		e[1][1][0].getKind() == RATIONAL_EXPR &&
		e[1][1][0].getRational() == Rational(-1),
		"equalLeaves2");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves2", e, pfs);
  }
  return newRWTheorem(e, e[1][1][1].eqExpr(e[1][2]), thm.getAssumptionsRef(), pf);
}


Theorem
ArithTheoremProducer::equalLeaves3(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[1].getKind() == RATIONAL_EXPR &&
		e[1].getRational() == Rational(0) &&
		e[0].getKind() == PLUS &&
		e[0].arity() == 3 &&
		e[0][0].getKind() == RATIONAL_EXPR &&
		e[0][0].getRational() == Rational(0) &&
		e[0][2].getKind() == MULT &&
		e[0][2].arity() == 2 &&
		e[0][2][0].getKind() == RATIONAL_EXPR &&
		e[0][2][0].getRational() == Rational(-1),
		"equalLeaves3");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves3", e, pfs);
  }
  return newRWTheorem(e, e[0][2][1].eqExpr(e[0][1]), thm.getAssumptionsRef(), pf);
}


Theorem
ArithTheoremProducer::equalLeaves4(const Theorem& thm)
{
  Proof pf;
  const Expr& e = thm.getRHS();

  if (CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == RATIONAL_EXPR &&
		e[0].getRational() == Rational(0) &&
		e[1].getKind() == PLUS &&
		e[1].arity() == 3 &&
		e[1][0].getKind() == RATIONAL_EXPR &&
		e[1][0].getRational() == Rational(0) &&
		e[1][2].getKind() == MULT &&
		e[1][2].arity() == 2 &&
		e[1][2][0].getKind() == RATIONAL_EXPR &&
		e[1][2][0].getRational() == Rational(-1),
		"equalLeaves4");
  }
  if (withProof())
  {
    vector<Proof> pfs;
    pfs.push_back(thm.getProof());
    pf = newPf("equalLeaves4", e, pfs);
  }
  return newRWTheorem(e, e[1][2][1].eqExpr(e[1][1]), thm.getAssumptionsRef(), pf);
}

Theorem
ArithTheoremProducer::diseqToIneq(const Theorem& diseq) {
  Proof pf;

  const Expr& e = diseq.getExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isEq(),
		"ArithTheoremProducer::diseqToIneq: expected disequality:\n"
		" e = "+e.toString());
  }

  const Expr& x = e[0][0];
  const Expr& y = e[0][1];

  if(withProof())
    pf = newPf(e, diseq.getProof());
  return newTheorem(ltExpr(x,y).orExpr(gtExpr(x,y)), diseq.getAssumptionsRef(), pf);
}
