/*****************************************************************************/
/*!
 * \file theory_bitvector.cpp
 * 
 * Author: Vijay Ganesh.
 * 
 * Created: Wed May  5 16:16:59 PST 2004
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


#include "theory_bitvector.h"
#include "bitvector_proof_rules.h"
#include "bitvector_exception.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "bitvector_expr_value.h"
#include "command_line_flags.h"


#define HASH_VALUE_ZERO 380
#define HASH_VALUE_ONE  450


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryBitvector Private Methods                                           //
///////////////////////////////////////////////////////////////////////////////

int
TheoryBitvector::BVSize(const Expr& e) {
  Type tp(getBaseType(e));
  DebugAssert(tp.getExpr().getOpKind() == BITVECTOR,
	      "BVSize: e = "+e.toString());
  return getBitvectorTypeParam(tp);
}

// Bit-blasting methods

//! accepts a bitvector equation t1 = t2. 
/*! \return a rewrite theorem which is a conjunction of equivalences
 * over the bits of t1,t2 respectively.
 */
Theorem TheoryBitvector::bitBlastEqn(const Expr& e)
{
  TRACE("bitvector", "bitBlastEqn(", e.toString(), ") {"); 
  IF_DEBUG(debugger.counter("bit-blasted eq")++);
  //stat counter
  d_bvBitBlastEq++;

  DebugAssert(e.isEq(),
	      "TheoryBitvector::bitBlastEqn:"
	      "expecting an equation" + e.toString());
  const Expr& leftBV = e[0];
  const Expr& rightBV = e[1];

  Theorem result = reflexivityRule(e);
  IF_DEBUG(const Type& leftType = getBaseType(leftBV));
  IF_DEBUG(const Type& rightType = getBaseType(rightBV));
  DebugAssert(BITVECTOR == leftType.getExpr().getOpKind() &&
	      BITVECTOR == rightType.getExpr().getOpKind(),
	      "TheoryBitvector::bitBlastEqn:"
	      "lhs & rhs must be bitvectors");
  DebugAssert(BVSize(leftBV) == BVSize(rightBV),
	      "TheoryBitvector::bitBlastEqn:\n e = "
	      +e.toString());
  Theorem bitBlastLeftThm;
  Theorem bitBlastRightThm;
  std::vector<Theorem> substThms;
  std::vector<Theorem> leftBVrightBVThms;
  int bvLength = BVSize(leftBV);
  int bitPosition = 0;
  Theorem thm0;

  for(; bitPosition < bvLength; bitPosition = bitPosition+1) {
    //bitBlastLeftThm is the theorem 'leftBV[bitPosition] <==> phi'
    bitBlastLeftThm = bitBlastTerm(leftBV, bitPosition);
    //bitBlastRightThm is the theorem 'rightBV[bitPosition] <==> theta'
    bitBlastRightThm = bitBlastTerm(rightBV, bitPosition);
    //collect the two theorems created above in the vector
    //leftBVrightBVthms.
    leftBVrightBVThms.push_back(bitBlastLeftThm); 
    leftBVrightBVThms.push_back(bitBlastRightThm);
    //construct (leftBV[bitPosition] <==> rightBV[bitPosition]) 
    //<====> phi <==> theta
    //and store in the vector substThms.
    Theorem thm = substitutivityRule(IFF, leftBVrightBVThms);
    thm = transitivityRule(thm, rewriteBoolean(thm.getRHS()));    
    leftBVrightBVThms.clear();
    substThms.push_back(thm); 
    //if phi <==> theta is false, then stop bitblasting. immediately
    //exit and return false.
    if(thm.getRHS().isFalse())
      return transitivityRule(result,
			      d_rules->bitvectorFalseRule(thm));
  }
  // AND_0^bvLength(leftBV[bitPosition] <==> rightBV[bitPosition]) <====>
  // AND_0^bvLength(phi <==> theta)
  Theorem thm = substitutivityRule(AND, substThms);
  // AND_0^bvLength(leftBV[bitPosition] <==> rightBV[bitPosition]) <====>
  // rewriteBoolean(AND_0^bvLength(phi <==> theta))
  thm = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
  //call trusted rule for bitblasting equations.
  result = d_rules->bitBlastEqnRule(e, thm.getLHS());
  result = transitivityRule(result, thm);
  TRACE("bitvector", "bitBlastEqn => ", result.toString(), " }"); 
  return result;
}

//! accepts a bitvector equation t1 != t2. 
/*! \return a rewrite theorem which is a conjunction of
 * (dis)-equivalences over the bits of t1,t2 respectively.
 * 
 * A separate rule for disequations for efficiency sake. Obvious
 * implementation using rule for equations and rule for NOT, is not
 * efficient.
 */
Theorem TheoryBitvector::bitBlastDisEqn(const Theorem& notE)
{
  TRACE("bitvector", "bitBlastDisEqn(", notE, ") {"); 
  IF_DEBUG(debugger.counter("bit-blasted diseq")++);
  //stat counter
  d_bvBitBlastDiseq++;

  DebugAssert(notE.getExpr().isNot() && (notE.getExpr())[0].isEq(),
	      "TheoryBitvector::bitBlastDisEqn:"
	      "expecting an equation" + notE.getExpr().toString());
  //e is the equation
  const Expr& e = (notE.getExpr())[0];
  const Expr& leftBV = e[0];
  const Expr& rightBV = e[1];
  IF_DEBUG(Type leftType = leftBV.getType());
  IF_DEBUG(debugger.counter("bit-blasted diseq bits")+=
	   BVSize(leftBV));
  IF_DEBUG(Type rightType = rightBV.getType());
  DebugAssert(BITVECTOR == leftType.getExpr().getOpKind() &&
	      BITVECTOR == rightType.getExpr().getOpKind(),
	      "TheoryBitvector::bitBlastDisEqn:"
	      "lhs & rhs must be bitvectors");
  DebugAssert(BVSize(leftBV) == BVSize(rightBV),
	      "TheoryBitvector::bitBlastDisEqn: e = "
	      +e.toString());
  Theorem bitBlastLeftThm;
  Theorem bitBlastRightThm;
  std::vector<Theorem> substThms;
  std::vector<Theorem> leftBVrightBVThms;
  int bvLength = BVSize(leftBV);
  int bitPosition = 0;
  for(; bitPosition < bvLength; bitPosition = bitPosition+1) {
    //bitBlastLeftThm is the theorem '~leftBV[bitPosition] <==> ~phi'
    bitBlastLeftThm =
      getCommonRules()->iffContrapositive(bitBlastTerm(leftBV, bitPosition));
    //bitBlastRightThm is the theorem 'rightBV[bitPosition] <==> theta'
    bitBlastRightThm = bitBlastTerm(rightBV, bitPosition);
    //collect the two theorems created above in the vector leftBVrightBVthms.
    leftBVrightBVThms.push_back(bitBlastLeftThm); 
    leftBVrightBVThms.push_back(bitBlastRightThm);
    //construct (~leftBV[bitPosition] <==> rightBV[bitPosition]) 
    //<====> ~phi <==> theta
    //and store in the vector substThms.
    //recall that (p <=/=> q) is same as (~p <==> q)
    Theorem thm = substitutivityRule(IFF, leftBVrightBVThms);
    thm = transitivityRule(thm, rewriteBoolean(thm.getRHS()));
    leftBVrightBVThms.clear();
    substThms.push_back(thm); 
    
    //if phi <==> theta is the True theorem, then stop bitblasting. immediately
    //exit and return t1!=t2 <=> true.
    if(thm.getRHS().isTrue())
      return d_rules->bitvectorTrueRule(thm);
  }

  // OR_0^bvLength(~leftBV[bitPosition] <==> rightBV[bitPosition]) <====>
  // OR_0^bvLength(~phi <==> theta)
  Theorem thm1 = substitutivityRule(OR, substThms);
  // Call trusted rule for bitblasting disequations.
  Theorem result = d_rules->bitBlastDisEqnRule(notE, thm1.getLHS());
  Theorem thm2 = transitivityRule(thm1, rewriteBoolean(thm1.getRHS()));
  result = iffMP(result, thm2);
  TRACE("bitvector", "bitBlastDisEqn => ", result.toString(), " }"); 
  return result;
}

/*! \param e1 pred e2, where pred is < or <=.  
 *
 *  if e1,e2 are constants, determine bv2int(e1) pred bv2int(e2). 
 *
 *  most significant bit of ei is denoted by msb(ei) 
 * 
 *  \return (msb(e1) pred msb(e2)) \vee 
 *          (msb(e1)=msb(e2) \wedge e1[n-2:0] pred e2[n-2:0])
 */
Theorem TheoryBitvector::bitBlastIneqn(const Expr& e) {
  TRACE("bitvector", "bitBlastIneqn(", e.toString(), ") {"); 

  if(e.isBoolConst()) {
    Theorem res(reflexivityRule(e));
    TRACE("bitvector", "bitBlastIneqn => ", res.getExpr(), " }");
    return res;
  }

  DebugAssert(BVLT == e.getOpKind() ||
	      BVLE == e.getOpKind(),
	      "TheoryBitvector::bitBlastIneqn: "
	      "input e must be BVLT/BVLE: e = " + e.toString());
  DebugAssert(e.arity() == 2,
	      "TheoryBitvector::bitBlastIneqn: "
	      "arity of e must be 2: e = " + e.toString());
  int e0len = BVSize(e[0]);
  int e1len = BVSize(e[1]);
  int bvLength = e0len >= e1len ? e0len : e1len;
  
  Expr newE=e;
  Expr lhs = e[0];
  Expr rhs = e[1];
  Theorem thm1 = reflexivityRule(e);
  if(e0len != e1len) {
    Theorem thm0 = d_rules->padBVLTRule(e, bvLength);
    thm1 = rewriteBV(thm0, 3, false);
    newE = thm1.getRHS();
    lhs = newE[0];
    rhs = newE[1];
  }

  int kind = e.getOpKind();
  Theorem res;
  if(lhs == rhs)
    res = 
      transitivityRule(thm1,d_rules->lhsEqRhsIneqn(newE, kind));
  else {
    if(BVCONST == lhs.getKind() && BVCONST == rhs.getKind())
      res = transitivityRule(thm1,d_rules->bvConstIneqn(newE, kind));
    else {
      Theorem lhs_i = bitBlastTerm(lhs, bvLength-1);
      Theorem rhs_i = bitBlastTerm(rhs, bvLength-1);
      Theorem thm2 = d_rules->generalIneqn(newE, lhs_i, rhs_i, kind);
      res = transitivityRule(thm1, thm2);      
      //check if output is TRUE or FALSE theorem, and then simply return
      Theorem output = rewriteBoolean(res.getRHS());
      if(output.getRHS().isBoolConst()) {
	res = transitivityRule(res, output);
	TRACE("bitvector", "bitBlastIneqn => ", res.getExpr(), " }"); 
	return res;
      }

      if(bvLength-1 > 0) {
	// Copy by value, since 'res' will be changing
	Expr resRHS = res.getRHS();
	//resRHS can be of the form (\alpha or (\beta and \gamma)) or
	//resRHS can be of the form (\beta and \gamma) or
	//resRHS can be of the form (\alpha or \gamma) or
	//resRHS can be of the form (\gamma)
	// Our mission is to bitblast \gamma and insert it back to the formula
	vector<unsigned> changed;
	vector<Theorem> thms;
	Expr gamma;
	Theorem gammaThm;
	switch(resRHS.getOpKind()) {
	case OR:
	  if(resRHS[1].isAnd()) { // (\alpha or (\beta and \gamma))
	    changed.push_back(1);
	    gamma = resRHS[1][1];
	    // \gamma <=> \gamma'
	    gammaThm = rewriteBV(gamma,2,false);
	    //\gamma' <=> \gamma"
	    Theorem thm3 = bitBlastIneqn(gammaThm.getRHS());
	    //Theorem thm3 = bitBlastIneqn(gamma);
	    //\gamma <=> \gamma' <=> \gamma"
	    thm3 = transitivityRule(gammaThm, thm3);
	    thms.push_back(thm3);
	    // (\beta and \gamma) <=> (\beta and \gamma")
	    thm3 = substitutivityRule(resRHS[1],changed,thms);
	    // Now substitute this into the OR.
	    // 'changed' is the same, only update thms[0]
	    thms[0] = thm3;
	    // (a or (b and g)) <=> (a or (b and g"))
	    thm3 = substitutivityRule(resRHS,changed,thms);
	    res = transitivityRule(res, thm3);
	    break;
	  }
	  // (\alpha or \gamma) - fall through (same as the AND case)
	case AND: { // (\beta and \gamma)
	  changed.push_back(1);
	  gamma = resRHS[1];
	  // \gamma <=> \gamma'
	  gammaThm = rewriteBV(gamma,2,false);
	  //\gamma' <=> \gamma"
	  Theorem thm3 = bitBlastIneqn(gammaThm.getRHS());
	  //Theorem thm3 = bitBlastIneqn(gamma);
	  //\gamma <=> \gamma' <=> \gamma"
	  thm3 = transitivityRule(gammaThm, thm3);
	  thms.push_back(thm3);
	  // (\beta and \gamma) <=> (\beta and \gamma")
	  thm3 = substitutivityRule(resRHS,changed,thms);
	  res = transitivityRule(res, thm3);
	  break;
	}
	default: // (\gamma)
	  IF_DEBUG(gamma = resRHS);
	  // \gamma <=> \gamma'
	  gammaThm = rewriteBV(resRHS,2,false);
	  //\gamma' <=> \gamma"
	  Theorem thm3 = bitBlastIneqn(gammaThm.getRHS());
	  //Theorem thm3 = bitBlastIneqn(gamma);
	  //\gamma <=> \gamma' <=> \gamma"
	  thm3 = transitivityRule(gammaThm, thm3);
	  res = transitivityRule(res, thm3);
	  break;
	}
	
	DebugAssert(kind == gamma.getOpKind(),
		    "TheoryBitvector::bitBlastIneqn: "
		    "gamma must be a BVLT/BVLE. gamma = " +
		    gamma.toString());
      }
    }
  }
  TRACE("bitvector", "bitBlastIneqn => ", res.toString(), " }"); 
  return res;
}


/*! The invariant maintained by this function is: accepts a bitvector
 * term, t,and a bitPosition, i. returns a formula over the set of
 * propositional variables defined using BOOLEXTRACT of bitvector
 * variables in t at the position i.
 *
 * \return Theorem(BOOLEXTRACT(t, bitPosition) <=> phi), where phi is
 * a Boolean formula over the individual bits of bit-vector variables.
 */
Theorem TheoryBitvector::bitBlastTerm(const Expr& t, int bitPosition)
{
  TRACE("bitvector", 
	"bitBlastTerm(", t, ", " + int2string(bitPosition) + ") {"); 
  Theorem result;
  
  //check in cache for the theorem t[bitPosition] <=> \theta_i.
  //if yes return the theorem, else produce it.
  Expr t_i = newBoolExtractExpr(t, bitPosition);
  CDMap<Expr,Theorem>::iterator it = d_bitvecCache.find(t_i);
  if(it != d_bitvecCache.end()) {
    result = (*it).second;
    TRACE("bitvector", "bitBlastTerm[cached] => ", result, " }"); 
    DebugAssert(t_i == result.getLHS(),
		"TheoryBitvector::bitBlastTerm:"
		"created wrong theorem" + result.toString() + t_i.toString());
    return result;
  } else {
    //else construct the theorem t[bitPosition] <=> \theta_i. and put it into
    //d_bitvecCache
    IF_DEBUG(Type type = t.getType());
    DebugAssert(BITVECTOR == type.getExpr().getOpKind(),
		"TheoryBitvector::bitBlastTerm: "
		"The type of input to bitBlastTerm must be BITVECTOR.\n t = "
		+t.toString());
    DebugAssert(bitPosition >= 0,
		"TheoryBitvector::bitBlastTerm: "
		"illegal bitExtraction attempted.\n bitPosition = "+
		int2string(bitPosition));
    // First, rewrite t[i] into t[i:i][0], normalize t[i:i], and
    // bitblast the result.
    if(*d_rwBitBlastFlag)
      result = rewriteBV(t_i, false);
    else
      result = reflexivityRule(t_i);

    Expr t2_i = result.getRHS();
    if(t2_i.isBoolConst()) {
      // Record the original expression into the cache
      d_bitvecCache[t_i] = result;
      TRACE("bitvector", "bitBlastTerm[rewrite to const] => ", result, " }"); 
      return result;
    }
      
    DebugAssert(t2_i.getOpKind()==BOOLEXTRACT,
		"bitBlastTerm: t2_i = "+t2_i.toString());
    // Check the cache again
    it = d_bitvecCache.find(t2_i);
    if(it != d_bitvecCache.end()) {
      result = transitivityRule(result, (*it).second);
      // Record the original expression into the cache
      d_bitvecCache[t_i] = result;
      TRACE("bitvector", "bitBlastTerm[cached2] => ", result, " }"); 
      return result;
    }
    // Bit-blast the rewritten version of the term.  We'll merge the
    // two at the end.
    Theorem resTmp(reflexivityRule(t2_i));
    const Expr& t2 = t2_i[0];

    int bitPos2 = getBoolExtractIndex(t2_i);
    switch(t2.getOpKind()) {
    case BVCONST:
      //we have a bitvector constant
      resTmp = transitivityRule(resTmp, 
				d_rules->bitExtractConstant(t2, bitPos2));
      break;
    case BVMULT: {
      Theorem thm;
      if(BVCONST == t2[0].getKind())
	thm = d_rules->bitExtractConstBVMult(t2, bitPos2);
      else
	thm = d_rules->bitExtractBVMult(t2, bitPos2);
      const Expr& boolExtractTerm = thm.getRHS();
      const Expr& term = boolExtractTerm[0];
      resTmp = transitivityRule(thm, bitBlastTerm(term, bitPos2)); 
    }
      break;
    case BVOR:
    case BVAND: {
      int resKind = (t2.getOpKind()==BVOR)? OR : AND;
      Theorem thm = (resKind==AND)?
	d_rules->bitExtractAnd(t2, bitPos2)
	: d_rules->bitExtractOr(t2, bitPos2);
      const Expr& phi = thm.getRHS();
      DebugAssert(phi.getOpKind() == resKind && phi.arity() == t2.arity(),
		  "TheoryBitvector::bitBlastTerm: recursion:"
		  "\n phi = "+phi.toString()
		  +"\n t2 = "+t2.toString());
      vector<Theorem> substThms;
      for(Expr::iterator i=phi.begin(), iend=phi.end(); i!=iend; ++i) {
	if(i->getOpKind() == BOOLEXTRACT)
	  substThms.push_back(bitBlastTerm((*i)[0], getBoolExtractIndex(*i)));
	else
	  substThms.push_back(reflexivityRule(*i));
      }
      resTmp = transitivityRule(resTmp, thm);
      resTmp = transitivityRule(resTmp, substitutivityRule(resKind,
							   substThms));
      break;
    }
    case BVNEG: {
      Theorem thm = d_rules->bitExtractNot(t2, bitPos2);
      const Expr& extractTerm = thm.getRHS();
      DebugAssert(NOT == extractTerm.getKind(),
		  "TheoryBitvector::bitBlastTerm:" 
		  "recursion: term must be NOT");
      const Expr& term0 = extractTerm[0];
      DebugAssert(BOOLEXTRACT == term0.getOpKind(), 
		  "TheoryBitvector::bitBlastTerm: recursion:("
		  "terms must be BOOL-EXTRACT");
      int bitPos0 = getBoolExtractIndex(term0);
      std::vector<Theorem> res;
      res.push_back(bitBlastTerm(term0[0], bitPos0));
      resTmp = transitivityRule(resTmp, thm);
      resTmp = transitivityRule(resTmp,
				substitutivityRule(NOT, res));
      break; 
    }
    case BVPLUS: {
      Expr bvPlusTerm = t2;
      Theorem thm1;
      if(2 < t2.arity()) {
	//this rule makes t2 a binary add. binary add is more suitable
	//for bitblasting.
	const Theorem& thm = d_rules->bvPlusAssociativityRule(bvPlusTerm);
	std::vector<Theorem> thms;
	thms.push_back(thm);
	thm1 = substitutivityRule
	  (newBoolExtractExpr(bvPlusTerm, bitPos2).getOp(), thms);
	bvPlusTerm = thm.getRHS();
	TRACE("bitvector", 
	      "TheoryBitvector::bitBlastTerm:thm1(", thm1.getExpr(), ")");
      } else
	thm1 = reflexivityRule(newBoolExtractExpr(bvPlusTerm, bitPos2));
      //bitblast each bit of t[0] and t[1] from 0-bit to bitPos2 
      //and store in two separate vectors.
      const Expr& bvplust1 = bvPlusTerm[0];
      const Expr& bvplust2 = bvPlusTerm[1];
      int t1Length = BVSize(bvplust1);
      int t2Length = BVSize(bvplust2);
      std::vector<Theorem> t1BitExtractThms;
      std::vector<Theorem> t2BitExtractThms;
      for(int i = 0; i <= bitPos2; i=i+1) {
        if(i < t1Length)
          t1BitExtractThms.push_back(bitBlastTerm(bvplust1, i));
        else
          t1BitExtractThms.push_back(d_rules->zeroPaddingRule(bvplust1,i));
        if(i < t2Length)
          t2BitExtractThms.push_back(bitBlastTerm(bvplust2, i));
        else
          t2BitExtractThms.push_back(d_rules->zeroPaddingRule(bvplust2,i));
      }
      Theorem thm2 = 
        d_rules->bitExtractBVPlus(t1BitExtractThms, 
                                  t2BitExtractThms, bvPlusTerm, bitPos2);
      resTmp = transitivityRule(resTmp, thm1);
      resTmp = transitivityRule(resTmp, thm2);
      break;
    }
    case CONCAT: {
      //we have a bitvector concatenation term
      Theorem thm = d_rules->bitExtractConcatenation(t2, bitPos2);
      const Expr& boolExtractTerm = thm.getRHS();
      DebugAssert(BOOLEXTRACT == boolExtractTerm.getOpKind(),
		  "TheoryBitvector::bitBlastTerm: recursion: term must be"
		  "bool_extract");
      const Expr& term = boolExtractTerm[0];
      int bitPos = getBoolExtractIndex(boolExtractTerm);
      TRACE("bitvector", 
	    "term for bitblastTerm recursion:(", term.toString(), ")");
      resTmp = transitivityRule(thm, bitBlastTerm(term, bitPos));
    }
      break;
    case EXTRACT:{
      // EXTRACT collapses under BOOLEXTRACT, no more of this case      
      //we have a bitvector extraction term
      Theorem thm = d_rules->bitExtractExtraction(t2, bitPos2);
      const Expr& boolExtractTerm = thm.getRHS();
      DebugAssert(BOOLEXTRACT == boolExtractTerm.getOpKind(),
		  "TheoryBitvector::bitBlastTerm: recursion: term must be"
		  "bool_extract");
      const Expr& term = boolExtractTerm[0];
      int bitPos = getBoolExtractIndex(boolExtractTerm);
      TRACE("bitvector", "term for bitblastTerm recursion:(", term, ")");
      resTmp = transitivityRule(thm, bitBlastTerm(term, bitPos));
      break;
    }
    case CONST_WIDTH_LEFTSHIFT: {
      resTmp = d_rules->bitExtractFixedLeftShift(t2, bitPos2);
      const Expr& extractTerm = resTmp.getRHS();
      if(BOOLEXTRACT == extractTerm.getOpKind())
	resTmp = 
	  transitivityRule(resTmp, 
			   bitBlastTerm(extractTerm[0],
					getBoolExtractIndex(extractTerm)));
      break;
    }
    case LEFTSHIFT:
    case RIGHTSHIFT:
    case SX:
    case BVSUB:
    case BVUMINUS:
      DebugAssert(false, "control should not reach here.");
      break;
    default:
      //we have bitvector variable.
      //check if the expr is indeed a BITVECTOR.   
      IF_DEBUG(Type type = t2.getType());
      DebugAssert(BITVECTOR == (type.getExpr()).getOpKind(),
		  "BitvectorTheoremProducer::bitBlastTerm: "
		  "the type must be BITVECTOR");
      //check if 0<= i < length of BITVECTOR
      IF_DEBUG(int bvLength=BVSize(t2));
      DebugAssert(0 <= bitPos2 && bitPos2 < bvLength,
		  "BitvectorTheoremProducer::bitBlastTerm: "
		  "the bitextract position must be legal");
      TRACE("bitvector",
	    "bitBlastTerm: blasting variables(", t2, ")");
      const Expr bitExtract = newBoolExtractExpr(t2, bitPos2);
      resTmp = transitivityRule(resTmp, reflexivityRule(bitExtract));
      TRACE("bitvector",
	    "bitBlastTerm: blasting variables(", t, ")");
      break;
    }
    DebugAssert(!resTmp.isNull(), "TheoryBitvector::bitBlastTerm()");
    Theorem simpThm = rewriteBoolean(resTmp.getRHS());

    resTmp = transitivityRule(resTmp, simpThm);
    result = transitivityRule(result, resTmp);
    d_bitvecCache[t_i] = result;
    d_bitvecCache[t2_i] = resTmp;
    DebugAssert(t_i == result.getLHS(),
		"TheoryBitvector::bitBlastTerm: "
		"created wrong theorem.\n result = "
		+result.toString()
		+"\n t_i = "+t_i.toString());
    TRACE("bitvector", "bitBlastTerm => ", result, " }"); 
    return result;
  }
}
  
// Rewriting methods

//! Check that all the kids of e are BVCONST
static bool constantKids(const Expr& e) {
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
    if(!i->isRational() && i->getKind() != BVCONST) return false;
  return true;
}


//! Search for all the BVCONST kids of e, and return their indices in idxs
static void constantKids(const Expr& e, vector<int>& idxs) {
  for(int i=0, iend=e.arity(); i<iend; ++i)
    if(e[i].getKind() == BVCONST) idxs.push_back(i);
}

Theorem
TheoryBitvector::normalizeConcat(const Expr& e, bool useFind) {
  TRACE("bitvector rewrite", "normalizeConcat(", e, ") {");
  Theorem res;
  if(*d_concatRewriteFlag) {
    switch(e.getOpKind()) {
    case EXTRACT: {
      DebugAssert(e.arity() == 1, "TheoryBitvector::normalizeConcat: e = "
		  +e.toString());
      if(getExtractLow(e) == 0 && getExtractHi(e) == BVSize(e[0])-1)
	res = d_rules->extractWhole(e);
      else {
	switch(e[0].getOpKind()) {
	case BVCONST:
	  res = d_rules->extractConst(e);
	  break;
	case EXTRACT:
	  res = d_rules->extractExtract(e);
	  break;
	case CONCAT:
	  // Push extraction through concat, and rewrite the kids
	  res = rewriteBV(d_rules->extractConcat(e), 2, useFind);
	  break;
	case BVNEG:
	  res = rewriteBV(d_rules->extractNeg(e), 2, useFind);
	  break;
	case BVAND:
	  res = rewriteBV(d_rules->extractAnd(e), 2, useFind);
	  break;
	case BVOR:
	  res = rewriteBV(d_rules->extractOr(e), 2, useFind);	  
	  break;
	case BVXOR:
	  res = 
	    rewriteBV(d_rules->extractBitwise(e, BVXOR,"extract_bvxor"), 
		      2, useFind);
	  break;
	case BVMULT: {
	  const Expr& bvmult = e[0];
	  int hiBit = getExtractHi(e);
	  int bvmultLen = BVSize(bvmult);
	  // Applicable if it changes anything
	  if(hiBit+1 < bvmultLen) {
	    res = d_rules->extractBVMult(e);
	    // The extraction may be stripped off
	    if(res.getRHS().getOpKind() == EXTRACT)
	      res = rewriteBV(res, 2, useFind);
	    else
	      res = rewriteBV(res, 1, useFind);
	  } else
	    res = reflexivityRule(e);
	  break;
	}
	case BVPLUS: {
	  const Expr& bvplus = e[0];
	  int hiBit = getExtractHi(e);
	  int bvplusLen = BVSize(bvplus);
	  if(hiBit+1 < bvplusLen) {
	    res = d_rules->extractBVPlus(e);
	    // The extraction may be stripped off
	    if(res.getRHS().getOpKind() == EXTRACT)
	      res = rewriteBV(res, 2, useFind);
	    else
	      res = rewriteBV(res, 1, useFind);
	  } else
	    res = reflexivityRule(e);
	  break;
	}
	  
	  /*
	case ITE: {
	  //ite(c,t1,t2)[i:j] <=> ite(c,t1[i:j],t2[i:j])
	  res = simplify(e);
	  vector<Theorem> thms;
	  vector<unsigned> changed;
	  const Expr& e1 = res.getRHS()[1];
	  const Expr& e2 = res.getRHS()[2];
	  Theorem t = rewriteBV(e1, useFind);
	  if(e1 != t.getRHS()) {
	    thms.push_back(t);
	    changed.push_back(1);
	  }
	  t = rewriteBV(e2, useFind);
	  if(e2 != t.getRHS()) {
	    thms.push_back(t);
	    changed.push_back(2);
	  }
	  if(changed.size()>0) {
	    t = substitutivityRule(res.getRHS(), changed, thms);
	    res = transitivityRule(res, t);
	  }
	  break;
	}
	  */
	default:
	  res = reflexivityRule(e);
	  break;
	}
      }
      break;
    }
    case BVNEG: {
      switch(e[0].getOpKind()) {
      case BVCONST:
	res = d_rules->negConst(e);
	break;
      case CONCAT:
	// May need to propagate negation in the kids, rewrite 2 levels
	res = rewriteBV(d_rules->negConcat(e), 2, useFind);
      break;
      case BVNEG:
	res = d_rules->negNeg(e);
	break;
      default:
	res = reflexivityRule(e);
	break;
      }
      break;
    }
    case BVAND: {
      // Flatten the bit-wise AND, eliminate duplicates, reorder terms
      res = d_rules->andFlatten(e);
      Expr ee = res.getRHS();
      // Search for constant bitvectors
      vector<int> idxs;
      constantKids(ee, idxs);
      if(idxs.size() >= 2) {
      res = transitivityRule(res, d_rules->andConst(ee, idxs));
      }
      ee = res.getRHS();
      if(ee.getOpKind() == BVAND) {
	// Search for constants again
	idxs.clear();
	constantKids(ee, idxs);
	DebugAssert(idxs.size() <= 1, "TheoryBitvector::normalizeConcat(ee="
		    +ee.toString()+")");
	if(idxs.size() >= 1) {
	  int idx(idxs[0]);
	  // Check if ee[idx] is a bitvector of 0's or 1's
          bool isZero(true);
          bool isOne(true);
          const Expr& c = ee[idx];
          for(int i=0, iend=getBVConstSize(c);
              (isZero || isOne) && (i<iend); ++i) {
            isZero = (isZero && !getBVConstValue(c, i));
            isOne  = (isOne && getBVConstValue(c, i));
          }
          if(isZero)
            res = transitivityRule(res, d_rules->andZero(ee, idx));
          else if(isOne)
            res = transitivityRule(res, d_rules->andOne(ee, idxs));
	}
      }
      // Lift concatenation over bit-wise AND and rewrite again
      ee = res.getRHS();
      if(ee.getOpKind() == BVAND) {
	int i=0, iend=ee.arity();
	// Search for the first CONCAT child
	for(; (i<iend) && ee[i].getOpKind() != CONCAT; ++i);
	// If found, lift CONCAT over BVAND, and rewrite 3 levels
	// deep.  Reason: the result of andConcat is of the form:
	// (@ (& ... t_k[i:j] ...) ... ), and only t_k is known to be 
	// completely rewritten.  Hence the 3 levels of rewrites.
	if(i<iend)
	  res = transitivityRule(res, rewriteBV(d_rules->andConcat(ee, i),
						3, useFind));
      }
      break;
    }
    case BVOR: {
      // Flatten the bit-wise OR, eliminate duplicates, reorder terms
      res = d_rules->orFlatten(e);
      Expr ee = res.getRHS();
      // Search for constant bitvectors
      vector<int> idxs;
      constantKids(ee, idxs);
      if(idxs.size() >= 2) {
	res = transitivityRule(res, d_rules->orConst(ee, idxs));
      }
      ee = res.getRHS();
      if(ee.getOpKind() == BVOR) {
	// Search for constants again
	idxs.clear();
	constantKids(ee, idxs);
	DebugAssert(idxs.size() <= 1, "TheoryBitvector::normalizeConcat(ee="
		    +ee.toString()+")");
	if(idxs.size() >= 1) {
	  int idx(idxs[0]);
	  // Check if ee[idx] is a bitvector of 0's or 1's
	  bool isZero(true);
	  bool isOne(true);
	  const Expr& c = ee[idx];
	  for(int i=0, iend=getBVConstSize(c);
	      (isZero || isOne) && (i<iend); ++i) {
	    isZero = (isZero && !getBVConstValue(c, i));
	    isOne  &= (isOne && getBVConstValue(c, i));
	  }
	  if(isOne)
	    res = transitivityRule(res, d_rules->orOne(ee, idx));
	  else if(isZero)
	    res = transitivityRule(res, d_rules->orZero(ee, idxs));
	  
	}
      }
      // Lift concatenation over bit-wise OR and rewrite again
      ee = res.getRHS();
      if(ee.getOpKind() == BVOR) {
	int i=0, iend=ee.arity();
	// Search for the first CONCAT child
	for(; (i<iend) && ee[i].getOpKind() != CONCAT; ++i);
	// If found, lift CONCAT over BVOR, and rewrite 3 levels
	// deep.  Reason: the result of orConcat is of the form:
	// (@ (| ... t_k[i:j] ...) ... ), and only t_k is known to be 
	// completely rewritten.  Hence the 3 levels of rewrites.
	if(i<iend)
	  res = transitivityRule(res, rewriteBV(d_rules->orConcat(ee, i),
						3, useFind));
      }
      break;
    }
    case CONCAT: {
      // First, flatten concatenation
      res = d_rules->concatFlatten(e);
      TRACE("bitvector rewrite", "normalizeConcat: flattened = ",
	    res.getRHS(), "");
      // Search for adjacent constants and accumulate the vector of
      // nested concatenations (@ t1 ... (@ c1 ... ck) ... tn), and the
      // indices of constant concatenations in this new expression.
      // We'll connect this term to 'e' by inverse of flattenning, and
      // rewrite concatenations of constants into bitvector constants.
      vector<unsigned> idxs;
      vector<Expr> kids; // Kids of the new concatenation
      vector<Theorem> thms; // Rewrites of constant concatenations
      vector<Expr> nestedKids; // Kids of the current concatenation of constants
      // res will be overwritten, using const Expr& may be dangerous
      Expr e1 = res.getRHS();
      for(int i=0, iend=e1.arity(); i<iend; ++i) {
	TRACE("bitvector rewrite", "normalizeConcat: e["+int2string(i)+"]=",
	      e1[i], "");
	if(e1[i].getKind() == BVCONST) {
	  // INVARIANT: if it is the first constant in a batch,
	  // then nestedKids must be empty.
	  nestedKids.push_back(e1[i]);
	  TRACE("bitvector rewrite", "normalizeConcat: queued up BVCONST: ",
		e1[i], "");
	} else { // e1[i] is not a BVCONST
	  if(nestedKids.size() > 0) { // This is the end of a batch
	    if(nestedKids.size() >= 2) { // Create a nested const concat
	      Expr cc = newConcatExpr(nestedKids);
	      idxs.push_back(kids.size());
	      kids.push_back(cc);
	      thms.push_back(d_rules->concatConst(cc));
	      TRACE("bitvector rewrite", "normalizeConcat: wrapping ", cc, "");
	    } else { // A single constant, add it as it is
	      TRACE("bitvector rewrite", "normalizeConcat: single const ",
		    nestedKids[0], "");
	      kids.push_back(nestedKids[0]);
	    }
	    nestedKids.clear();
	  }
	  // Add the current non-constant BV
	  kids.push_back(e1[i]);
	}
      }
      // Handle the last BVCONST
      if(nestedKids.size() > 0) {
	if(nestedKids.size() >= 2) { // Create a nested const concat
	  Expr cc = newConcatExpr(nestedKids);
	  idxs.push_back(kids.size());
	  kids.push_back(cc);
	  thms.push_back(d_rules->concatConst(cc));
	  TRACE("bitvector rewrite", "normalizeConcat: wrapping ", cc, "");
	} else { // A single constant, add it as it is
	  kids.push_back(nestedKids[0]);
	  TRACE("bitvector rewrite", "normalizeConcat: single const ",
		nestedKids[0], "");
	}
	nestedKids.clear();
      }
      // If there are any constants to merge, do the merging
      if(idxs.size() > 0) {
	// CONCAT with constants groupped
	if(kids.size() == 1) { // Special case: all elements are constants
	  DebugAssert(thms.size() == 1, "TheoryBitvector::normalizeConcat:\n"
		      "case CONCAT: all constants.  thms.size() == "
		      +int2string(thms.size()));
	  res = transitivityRule(res, thms[0]);
	} else {
	  Expr ee = newConcatExpr(kids);
	  
	  Theorem constMerge = substitutivityRule(ee, idxs, thms);
	  // The inverse flattening of ee
	  Theorem unFlatten = symmetryRule(d_rules->concatFlatten(ee));
	  // Putting it together: Theorem(e==e'), where e' has constants merged
	  res = transitivityRule(res, unFlatten);
	  res = transitivityRule(res, constMerge);
	}
      }
      
      // Now do a similar search for mergeable extractions
      idxs.clear();
      thms.clear();
      kids.clear();
      // nestedKids must already be empty
      DebugAssert(nestedKids.size() == 0,
		  "normalizeConcat() case CONCAT, end of const merge");
      Expr prevExpr; // Previous base of extraction (initially Null)
      // The first and the last bit in the batch of mergeable extractions
      int hi(-1), low(-1);
      // Refresh e1
      e1 = res.getRHS();
      for(int i=0, iend=e1.arity(); i<iend; ++i) {
	const Expr& ei = e1[i];
	if(ei.getOpKind() == EXTRACT) {
	  if(nestedKids.size() > 0 && ei[0] == prevExpr
	     && (low-1) == getExtractHi(ei)) {
	    // Continue to accumulate the current batch
	    nestedKids.push_back(ei);
	    low = getExtractLow(ei);
	  } else { // Start a new batch
	    // First, check if there was a batch before that
	    if(nestedKids.size() >= 2) { // Create a nested const concat
	      Expr cc = newConcatExpr(nestedKids);
	      idxs.push_back(kids.size());
	      kids.push_back(cc);
	      thms.push_back(d_rules->concatMergeExtract(cc));
	      nestedKids.clear();
	    } else if(nestedKids.size() == 1) {
	      // A single extraction, add it as it is
	      kids.push_back(nestedKids[0]);
	      nestedKids.clear();
	    }
	    // Now, actually start a new batch
	    nestedKids.push_back(ei);
	    hi = getExtractHi(ei);
	    low = getExtractLow(ei);
	    prevExpr = ei[0];
	  }
	} else { // e1[i] is not an EXTRACT
	  if(nestedKids.size() >= 2) { // Create a nested const concat
	    Expr cc = newConcatExpr(nestedKids);
	    idxs.push_back(kids.size());
	    kids.push_back(cc);
	    thms.push_back(d_rules->concatMergeExtract(cc));
	  } else if(nestedKids.size() == 1) {
	    // A single extraction, add it as it is
	    kids.push_back(nestedKids[0]);
	  }
	  nestedKids.clear();
	  // Add the current non-EXTRACT BV
	  kids.push_back(ei);
	}
      }
      // Handle the last batch of extractions
      if(nestedKids.size() >= 2) { // Create a nested const concat
	Expr cc = newConcatExpr(nestedKids);
	idxs.push_back(kids.size());
	kids.push_back(cc);
	// The extraction may include all the bits, we need to rewrite again
	thms.push_back(rewriteBV(d_rules->concatMergeExtract(cc), 1, useFind));
      } else if(nestedKids.size() == 1) {
	// A single extraction, add it as it is
	kids.push_back(nestedKids[0]);
      }
      // If there are any extractions to merge, do the merging
      if(idxs.size() > 0) {
	// CONCAT with extractions groupped
	if(kids.size() == 1) { // Special case: all elements merge together
	  DebugAssert(thms.size() == 1, "TheoryBitvector::normalizeConcat:\n"
		      "case CONCAT: all extracts merge.  thms.size() == "
		      +int2string(thms.size()));
	  res = thms[0];
	} else {
	  Expr ee = newConcatExpr(kids);
	  Theorem extractMerge = substitutivityRule(ee, idxs, thms);
	  // The inverse flattening of ee
	  Theorem unFlatten = symmetryRule(d_rules->concatFlatten(ee));
	  // Putting it together: Theorem(e==e'), where e' has extractions merged
	  res = transitivityRule(res, unFlatten);
	  res = transitivityRule(res, extractMerge);
	}
      }
      // Check for 0bin00 @ BVPLUS(n, ...).  Most of the time, this
      // case will be handled during the top-down phase
      // (simplifyOp()), but not always.
      Expr ee = res.getRHS();
      if(ee.getOpKind()==CONCAT && ee[0].getKind()==BVCONST
	 && ee[1].getOpKind()==BVPLUS && computeBVConst(ee[0]) == 0) {
	// Push the concat down through BVPLUS
	Theorem thm = d_rules->bvplusZeroConcatRule(ee);
	if(thm.getLHS()!=thm.getRHS()) {
	  thm = transitivityRule(thm, d_rules->padBVPlus(thm.getRHS()));
	  // Kids may need to be rewritten again
	  res = rewriteBV(transitivityRule(res, thm), 2, useFind);
	}
      }
      // Since we may have pulled subexpressions from more than one
      // level deep, we cannot guarantee that all the new kids are
      // fully simplified, and have to call simplify explicitly again.
      // Since this is potentially an expensive operation, we try to
      // minimize the need for it: 

      // * check if the result has a find pointer (then kids don't
      //   need to be simplified),
      // * check if any of the kids simplify (if not, don't bother).
      // If kids are already simplified, we'll hit the simplifier
      // cache.  It's only expensive when kids do indeed simplify.
      if(useFind && !res.getRHS().hasFind()) {
	ee = res.getRHS();
	vector<Theorem> thms;
	vector<unsigned> changed;
	for(int i=0, iend=ee.arity(); i<iend; ++i) {
	  Theorem thm = simplify(ee[i]);
	  if(thm.getLHS()!=thm.getRHS()) {
	    thms.push_back(thm);
	    changed.push_back(i);
	  }
	}
	if(changed.size()>0) {
	  Theorem subst = substitutivityRule(ee, changed, thms);
	  res = transitivityRule(res, rewriteBV(subst, 1, useFind));
	}
      }
      break;
    }
    default:
      DebugAssert(false, "normalizeConcat: bad expr: "+e.toString());
      res = reflexivityRule(e);
      break;
    }
    DebugAssert(e == res.getLHS(), "normalizeConcat:\n e = "+e.toString()
		+"\n res.getLHS() = "+res.getLHS().toString());
  }
  else
    res = reflexivityRule(e);
  TRACE("bitvector rewrite", "normalizeConcat => ", res.getExpr(), " }");
  return res;
}


/*! accepts an expression e, and returns a theorem e <==>
 *  BVPLUS_NORMAL_FORM(e) we always assume that kids of e are in
 *  bvplus normal form, and only the top-level needs normalization
 */
Theorem
TheoryBitvector::normalizeBVArith(const Expr& e, bool useFind) {
  TRACE("bitvector rewrite", "normalizeBVArith(", e, ") {");
  Theorem res;
  switch(e.getOpKind()) {
    case BVPLUS: {
      DebugAssert(e.arity()>=2,
		  "BVPLUS must have atleast 2 kids:\n e = " + e.toString());
      res = d_rules->padBVPlus(e);
      Expr rhs = res.getRHS();
      if(e != rhs)
	return rewriteBV(res, 4, useFind);
      switch(rhs.getOpKind()) {
      case BVPLUS: {
	const Theorem thm0 = flattenBVPlus(rhs);
	res = transitivityRule(res, thm0);
	//res = transitivityRule(res, padBVPlus(res.getRHS()));
	res = transitivityRule(res, d_rules->combineLikeTermsRule(res.getRHS()));
	break;
      }
      default:
	return res;
	break;
      }
    }
      break;
    case BVMULT: {
      DebugAssert(e.arity()==2,
		  "BVMULT must have exactly 2 kids: " + e.toString());
      DebugAssert(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		  BITVECTOR==e[1].getType().getExpr().getOpKind(),
		  "For BVMULT terms e[0], e[1] must be a BV:\n e = "
		  +e.toString());
      if(BVCONST == e[0].getKind() || BVCONST == e[1].getKind()) {
	if(constantKids(e)) {
	  res = d_rules->bvmultConst(e);
	  TRACE("bitvector rewrite", "normalizeBVArith[const] => ",
		res.getExpr(), " }");
	  return res;
	}
	
	if(BVCONST == e[1].getKind()) {
	  Theorem thm = d_rules->flipBVMult(e);
	  Theorem thm1 = normalizeBVArith(thm.getRHS(), useFind);
	  res = transitivityRule(thm, thm1);      
	  TRACE("bitvector rewrite", "normalizeBVArith[flip] => ",
		res.getExpr(), " }");
	  return res;
	}
	const Rational coeff = computeBVConst(e[0]);
	if(0 == coeff) {
	  res = d_rules->zeroCoeffBVMult(e);
	  TRACE("bitvector rewrite", "normalizeBVArith[c=0] => ",
		res.getExpr(), " }");
	  return res;
	}
	else if(1 == coeff) {
	  res = d_rules->oneCoeffBVMult(e); 
	  TRACE("bitvector rewrite", "normalizeBVArith[c=1] => ",
		res.getExpr(), " }");
	  return res;
	}
	
	DebugAssert(coeff > 1,
		    "in BVMULT e[0] must be a rational: " + e.toString());
	const Theorem thm = d_rules->padBVMult(e);
	if(thm.getLHS() != thm.getRHS()) {
	  const Theorem thm1 = rewriteBV(thm.getRHS(), 2, useFind);
	  res = transitivityRule(thm, thm1);
	  TRACE("bitvector rewrite", "normalizeBVArith[pad] => ",
		res.getExpr(), " }");
	  return res;
	}
	
	switch(e[1].getOpKind()) {
	case BVMULT: {
	  if (BVCONST == e[1][0].getKind()) {
            //e is of the form a*(b*t); e cannot be of the form a*(t*b)
            //or a*(b*c) since the kids are always in normal form
            //e <==> (a*b)*t
            const Theorem thm2 = 
              d_rules->bvConstMultAssocRule(e);
            res = thm2;
          }
          else res = reflexivityRule(e);
	  break;
	}
	case BVPLUS: {
	  DebugAssert(BVCONST == e[0].getKind(),
		      "e[0] must be a BVCONST" + e.toString());
	  //a*(t1+...+tn) <==> a*t1 + ... + a*tn
	  const Theorem thm0 = d_rules->bvMultDistRule(e);
	  res = rewriteBV(thm0, 2, useFind);
	  break;
	}
	default:
	  res = reflexivityRule(e);
	  break;
	}
      }
      //nonlinear multiplication
      else
      	if(e[1] < e[0])
     	  res = d_rules->flipBVMult(e);
	else
	  res = reflexivityRule(e);
      // 	//FIXME: fix this rule later
      // 	rhs = res.getRHS();
      // 	if(BVMULT == rhs[0].getOpKind() || BVMULT == rhs[1].getOpKind())
      // 	  res = d_rules->bvMultAssocRule(rhs);
      //       }
      break;
    }
    case BVUMINUS: {
      DebugAssert(e.arity() == 1,
		  "e can atmost have one kid" + e.toString());
      DebugAssert(e[0].getOpKind() != BVUMINUS,
		  "e[0] may not be BVUMINUS, it must be normalized:"+
		  e.toString());
      Theorem thm0 = d_rules->bvuminusToBVPlus(e);
      Theorem temp = pushNegation(thm0.getRHS()[0]);
      if (temp.getLHS() != temp.getRHS()) {
	vector<Theorem> thms;
	vector<unsigned> changed;
	thms.push_back(temp);
	changed.push_back(0);
	Theorem thm1 = substitutivityRule(thm0.getRHS(),changed,thms);
	thm0 = transitivityRule(thm0,thm1);
      }
      Theorem thm2 = rewriteBV(thm0.getRHS(), 2, useFind);
      res= transitivityRule(thm0,thm2);
    }
      break;
    default:
      res = reflexivityRule(e);
      break;
  }

  TRACE("bitvector rewrite", "normalizeBVArith => ", res.getExpr(), " }");
  return res;
}


Theorem TheoryBitvector::flattenBVPlus(const Expr& e) {
  DebugAssert(BVPLUS == e.getOpKind(),
	      "TheoryBitvector::flattenBVPlus:"
	      "input must be a BVPLUS: " + e.toString());

  bool needFlattening = false;  
  //loop thru' the subterms to check if they need flatten
  for(Expr::iterator  i=e.begin(), iend=e.end();i!=iend;++i) {
    if(BVPLUS == (*i).getOpKind()) {
      needFlattening = true;
      break;
    }
  }
  
  Theorem res;
  if(needFlattening)
    res = d_rules->flattenBVPlus(e);
  else
    res = reflexivityRule(e);

  return res;
}

//! signextend e0 <=(s) e1 appropriately, then normalize and return
Theorem TheoryBitvector::signExtendBVLT(const Expr& e, int len, bool useFind) {
  DebugAssert(e.getOpKind()==SBVLT || e.getOpKind()==SBVLE,
	      "TheoryBitvector::signExtendBVLT: input must be BVLT/BVLE"
	      + e.toString());
  std::vector<Theorem> thms;
  std::vector<unsigned> changed;

  //e0 <= e1 <==> pad(e0) <= pad(e1)
  Theorem thm = d_rules->padSBVLTRule(e, len);
  Expr paddedE = thm.getRHS();

  //the rest of the code simply normalizes pad(e0) and pad(e1)
  Theorem thm0 = d_rules->signExtendRule(paddedE[0]);
  Expr rhs0 = thm0.getRHS();
  thm0 = transitivityRule(thm0, rewriteBV(rhs0, useFind));
  if(thm0.getLHS() != thm0.getRHS()) {
    thms.push_back(thm0);
    changed.push_back(0);
  }
  
  Theorem thm1 = d_rules->signExtendRule(paddedE[1]);
  Expr rhs1 = thm1.getRHS();
  thm1 = transitivityRule(thm1, rewriteBV(rhs1, useFind));
  if(thm1.getLHS() != thm1.getRHS()) {
    thms.push_back(thm1);
    changed.push_back(1);
  }

  Theorem result;
  if(changed.size() > 0) {
    result = substitutivityRule(paddedE,changed,thms);
    result = transitivityRule(thm, result);
  }
  else
    result = reflexivityRule(e);
  return result;
}

Theorem TheoryBitvector::rewriteConst(const Expr& e)
{
  // Rewrite bitvector operators which have constant arguments
  switch(e.getOpKind()) {
  case EQ:
    if(constantKids(e))
      return d_rules->eqConst(e);
    break;
  case CONCAT:
    if(constantKids(e))
      return d_rules->concatConst(e);
    break;
  case BVAND: {
    vector<int> idxs;
    constantKids(e, idxs);
    if(idxs.size() >= 2)
      return d_rules->andConst(e, idxs);
    break;
  }
  case BVOR: {
    vector<int> idxs;
    constantKids(e, idxs);
    if(idxs.size() >= 2)
      return d_rules->orConst(e, idxs);
    break;
  }
  case BVNEG:
    if(constantKids(e))
      return d_rules->negConst(e);
    break;
  case BOOLEXTRACT:
    if(constantKids(e))
      return d_rules->bitExtractConstant(e[0], getBoolExtractIndex(e));
    break;
  case EXTRACT:
    if(constantKids(e))
      return d_rules->extractConst(e);
    break;
  case BVPLUS:
    if(constantKids(e))
      return d_rules->bvplusConst(e);
    break;
  case BVMULT:
    if(constantKids(e))
      return d_rules->bvmultConst(e);
    break;
  default:
    break;
  }
  return reflexivityRule(e);
}

Theorem TheoryBitvector::rewriteBV(const Expr& e, bool useFind) {
  ExprMap<Theorem> cache;
  return rewriteBV(e, cache, useFind);
}


Theorem TheoryBitvector::rewriteBV(const Expr& e, ExprMap<Theorem>& cache,
				   bool useFind) {
  TRACE("bitvector rewrite", "TheoryBitvector::rewriteBV(", e, ") {");

  ExprMap<Theorem>::iterator it = cache.find(e);
  if(it!=cache.end()) {
    Theorem res = (*it).second;
    TRACE("bitvector rewrite", "TheoryBitvector::rewriteBV[cached] => ",
	  res.getExpr(), " }");
    IF_DEBUG(debugger.counter("bv rewriteBV cache hits")++);
    return res;
  }
    
  Theorem res;
  switch(e.getOpKind()) {
  case EQ: {
    // Rewrite bitvector operators which have constant arguments
    if(constantKids(e)) {
      res = d_rules->eqConst(e);
      IF_DEBUG(debugger.counter("bv rewrite const eq")++);
    } 
    //if both e[0],e[1] are BVPLUS. I disregard other cases like
    //BVPLUS(x,y)=x
    else if (BVPLUS == e[0].getOpKind() && 
	     BVPLUS == e[1].getOpKind() &&
	     *d_lhsMinusRhsFlag) {
      // e[0]=e[1] <==> e[0]+(-e[1])=0
      res = d_rules->lhsMinusRhsRule(e);
      Theorem  thm0 = rewriteBV(res.getRHS(),2,useFind);
      res = transitivityRule(res,thm0);
    }	
    else
      res = reflexivityRule(e);
    break;
  }
  case BOOLEXTRACT: {
    Expr t(e);
    // Normal form: t[0] for 1-bit t, collapse t[i:i][0] into t[i]
    if(BVSize(e[0]) > 1) { // transform t[i] to t[i:i][0] and rewrite
      res = rewriteBV(d_rules->bitExtractRewrite(e), cache, 2, useFind);
      t = res.getRHS();
    }
    if(t.getOpKind() == BOOLEXTRACT && t[0].getOpKind() == EXTRACT) {
      // Collapse t[i:i][0] to t[i]
      int low = getExtractLow(t[0]);
      if(getExtractHi(t[0]) == low) {
	Theorem thm(d_rules->bitExtractRewrite
		    (newBoolExtractExpr(t[0][0], low)));
	thm = symmetryRule(thm);
	res = (res.isNull())? thm : transitivityRule(res, thm);
	t = res.getRHS()[0];
	// Make sure t in the resulting t[i] is its own find pointer
	// (global invariant)
	if(useFind && t.hasFind()) {
	  Theorem findThm = find(t);
	  if(t != findThm.getRHS()) {
	    vector<Theorem> thms;
	    thms.push_back(findThm);
	    thm = substitutivityRule(res.getRHS().getOp(), thms);
	    res = transitivityRule(res, thm);
	  }
	}
      }
    }
    if(!res.isNull()) t = res.getRHS();
    // Rewrite a constant extraction to TRUE or FALSE
    if(t.getOpKind() == BOOLEXTRACT && constantKids(t)) {
      Theorem thm = d_rules->bitExtractConstant(t[0], getBoolExtractIndex(t));
      res = (res.isNull())? thm : transitivityRule(res, thm);
    }
    break;
  }
  case SBVLT:
  case SBVLE:{
    /*! input: e0 <=(s) e1. output depends on whether the topbits(MSB) of
     *  e0 and e1 are constants. If they are constants then optimizations
     *  are done. In general, the following rule is implemented.
     * Step1:
     *                    e0 <=(s) e1 
     *                       <==> 
     *                 pad(e0) <=(s) pad(e1)
     * Step2:
     *                 pad(e0) <=(s) pad(e1) 
     *                       <==> 
     *             (e0[n-1] AND NOT e1[n-1]) OR 
     *             (e0[n-1] = e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
     */
    int e0len = BVSize(e[0]);
    int e1len = BVSize(e[1]);
    int bvlength = e0len>=e1len ? e0len : e1len;
    //e0 <=(s) e1 <=> signpad(e0) <=(s) signpad(e1)
    Theorem thm0 = signExtendBVLT(e, bvlength, useFind);
    //signpad(e0) <= signpad(e1)
    Expr thm0RHS = thm0.getRHS();
    DebugAssert(thm0RHS.getOpKind() == SBVLT || 
		thm0RHS.getOpKind() == SBVLE,
		"TheoryBitvector::RewriteBV");
    //signpad(e0)[bvlength-1:bvlength-1]
    const Expr MSB0 = newBVExtractExpr(thm0RHS[0],bvlength-1,bvlength-1);
    //signpad(e1)[bvlength-1:bvlength-1]
    const Expr MSB1 = newBVExtractExpr(thm0RHS[1],bvlength-1,bvlength-1);
    //rewritten MSB0
    const Theorem topBit0 = rewriteBV(MSB0, 2, useFind);
    //rewritten MSB1
    const Theorem topBit1 = rewriteBV(MSB1, 2, useFind);
    //compute e0 <=(s) e1 <==> signpad(e0) <=(s) signpad(e1) <==>
    //output as given above
    Theorem thm1 = d_rules->signBVLTRule(thm0RHS, topBit0, topBit1);
    thm1 = transitivityRule(thm1,simplify(thm1.getRHS()));
    res = transitivityRule(thm0,thm1);
    break;
  }
  case BVLT:
  case BVLE: {
    Expr lhs = e[0];
    Expr rhs = e[1];
    int e0len = BVSize(lhs);
    int e1len = BVSize(rhs);
    Theorem thm1;
    if (e0len != e1len) {
      int bvlength = e0len>=e1len ? e0len : e1len;
      //e0 <= e1 <=> pad(e0) <= pad(e1)
      Theorem thm0 = d_rules->padBVLTRule(e, bvlength);
      //pad(e0) <= pad(e1)
      Expr thm0RHS = thm0.getRHS();
      DebugAssert(thm0RHS.getOpKind() == BVLT || 
                  thm0RHS.getOpKind() == BVLE,
                  "TheoryBitvector::RewriteBV");
      //pad(e0)
      Expr thm0RHS0 = thm0RHS[0];
      //pad(e1)
      Expr thm0RHS1 = thm0RHS[1];    
      //pad(e0) <=> pad(e0)'
      Theorem rhsThm0 = rewriteBV(thm0RHS0, 2, false);
      //pad(e1) <=> pad(e1)'
      Theorem rhsThm1 = rewriteBV(thm0RHS1, 2, false);

      std::vector<Theorem> thms;
      std::vector<unsigned> changed;
      if(rhsThm0.getLHS() != rhsThm0.getRHS()) {
        thms.push_back(rhsThm0);
        changed.push_back(0);
      }    
      if(rhsThm1.getLHS() != rhsThm1.getRHS()) {
        thms.push_back(rhsThm1);
        changed.push_back(1);
      }

      DebugAssert(changed.size() > 0, "expected change");
      //pad(e0)<pad(e1) <=> pad(e0)' < pad(e1)'
      thm1 = substitutivityRule(thm0RHS, changed, thms);
      thm1 = transitivityRule(thm0,thm1);
      lhs = thm1.getRHS()[0];
      rhs = thm1.getRHS()[1];
    }
    else
      thm1 = reflexivityRule(e);

    Expr newE = thm1.getRHS();

    int kind = newE.getOpKind();
    if(lhs == rhs)
      res = transitivityRule(thm1, d_rules->lhsEqRhsIneqn(newE, kind));
    else if (BVCONST == lhs.getKind() && BVCONST == rhs.getKind())
      res = transitivityRule(thm1, d_rules->bvConstIneqn(newE, kind));
    else if (kind == BVLE && BVCONST == lhs.getKind() && computeBVConst(lhs) == 0)
      res = transitivityRule(thm1, d_rules->zeroLeq(newE));
    else
      res = thm1;
    break;
  }
  case SX: {  
    res = d_rules->signExtendRule(e);
    Expr rhs = res.getRHS();
    res = transitivityRule(res, rewriteBV(rhs, useFind));
    break;
  }
  case RIGHTSHIFT:
    res = rewriteBV(d_rules->rightShiftToConcat(e), 1, useFind);
    break;
  case LEFTSHIFT:
    res = rewriteBV(d_rules->leftShiftToConcat(e), 1, useFind);
    break;
  case CONST_WIDTH_LEFTSHIFT:
    res = rewriteBV(d_rules->constWidthLeftShiftToConcat(e), 1, useFind);
    break;
  case CONCAT:  
  case BVAND:
  case BVOR:
  case BVNEG:
  case EXTRACT:
    res = normalizeConcat(e, useFind);
    break;
  case BVPLUS:
  case BVUMINUS:
  case BVMULT:
    res = normalizeBVArith(e, useFind);
    break;
  default:
    break;
  }
  if(res.isNull()) res = reflexivityRule(e);
  // Ensure that the result is a find pointer of itself (if it has any)
  Expr rhs = res.getRHS();
  if(useFind && rhs.hasFind())
    res = transitivityRule(res, find(rhs));
  cache[e] = res;
  TRACE("bitvector rewrite", "TheoryBitvector::rewriteBV => ",
	res.getExpr(), " }");
  return res;
}


Theorem
TheoryBitvector::rewriteBV(const Expr& e, int n, bool useFind) {
  ExprMap<Theorem> cache;
  return rewriteBV(e, cache, n, useFind);
}

Theorem
TheoryBitvector::rewriteBV(const Expr& e, ExprMap<Theorem>& cache, int n,
			   bool useFind) {
  TRACE("bitvector rewrite",
	"TheoryBitvector::rewriteBV["+int2string(n)+"](", e, ") {");
  Theorem res;

  if(n > 0) {
    // First, check the cache
    ExprMap<Theorem>::iterator it = cache.find(e);
    if(it!=cache.end()) {
      res = (*it).second;
      TRACE("bitvector rewrite", "TheoryBitvector::rewrite["+int2string(n)
	    +"][cached] => ", res.getExpr(), " }");
      IF_DEBUG(debugger.counter("bv rewriteBV[n] cache hits")++);
      return res;
    }
    
    if(n >= 2) {
      // rewrite children recursively
      vector<Theorem> thms;
      vector<unsigned> changed;
      for(int i=0, iend=e.arity(); i<iend; ++i) {
	Theorem thm = rewriteBV(e[i], cache, n-1, useFind);
	if(thm.getLHS() != thm.getRHS()) {
	  thms.push_back(thm);
	  changed.push_back(i);
	}
      }
      if(changed.size() > 0)
	res = substitutivityRule(e, changed, thms);
    }
    // Rewrite the top node
    if(res.isNull())
      res = rewriteBV(e, cache, useFind);
    else
      res = transitivityRule(res, rewriteBV(res.getRHS(), cache, useFind));
  } else
    res = reflexivityRule(e);

  DebugAssert(!res.isNull(), "TheoryBitvector::rewriteBV(e, cache, n)");
  TRACE("bitvector rewrite",
	"TheoryBitvector::rewriteBV["+int2string(n)+"] => ",
	res.getExpr(), " }");
  // The cache is not updated here, since it's used in rewriteBV(e, cache)
  return res;
}

// Recursively descend into the expression e, keeping track of whether
// we are under even or odd number of negations ('neg' == true means
// odd, the context is "negative").
// Produce a proof of e <==> e' or !e <==> e', depending on whether
// neg is false or true, respectively.
// This function must be called only from the pushNegation function
Theorem TheoryBitvector::pushNegationRec(const Expr& e, bool neg) {
  TRACE("pushNegation", "pushNegationRec(", e,
	", neg=" + string(neg? "true":"false") + ") {");
  //DebugAssert(isTerm(e), 
  //      "TheoryBitvector::pushNegationRec: input must be a term. e = " + 
  //      e.toString());
  Expr NegExpr = newBVNegExpr(e);
  ExprMap<Theorem>::iterator i = d_pushNegCache.find(neg ? NegExpr : e);
  if(i != d_pushNegCache.end()) { // Found cached result
    TRACE("TheoryBitvector::pushNegation", 
	  "pushNegationRec [cached] => ", (*i).second, "}");
    return (*i).second;
  }
  // By default, do not rewrite
  Theorem res(reflexivityRule((neg)? NegExpr : e));
  if(neg) {
    switch(e.getOpKind()) {
    case BVCONST: 
      res = d_rules->negConst(NegExpr); 
      break;
    case BVNEG:{
      Theorem thm0 = d_rules->negNeg(NegExpr);
      res = pushNegationRec(thm0.getRHS(), false);
      res = transitivityRule(thm0,res);
      break;
    }
    case BVAND: {
      //demorgan's laws. 
      Theorem thm0 = d_rules->negBVand(NegExpr);
      Expr ee = thm0.getRHS();
      if (ee.arity() == 0) res = thm0;
      else {
        //process each negated kid
        Op op = ee.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=ee.begin(), iend=ee.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec((*i)[0], true));
        res = substitutivityRule(op, thms);
        res = transitivityRule(thm0, res);
        res = transitivityRule(res, rewrite(res.getRHS()));
      }
      break;
    }
    case BVOR: {
      //demorgan's laws. 
      Theorem thm0 = d_rules->negBVor(NegExpr);
      Expr ee = thm0.getRHS();
      if (ee.arity() == 0) res = thm0;
      else {
        //process each negated kid
        Op op = ee.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=ee.begin(), iend=ee.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec((*i)[0], true));
        res = substitutivityRule(op, thms);
        res = transitivityRule(thm0, res);
        res = transitivityRule(res, rewrite(res.getRHS()));
      }
      break;
    }
    case CONCAT: {
      //demorgan's laws. 
      Theorem thm0 = d_rules->negConcat(NegExpr);
      Expr ee = thm0.getRHS();
      if (ee.arity() == 0) res = thm0;
      else {
        //process each negated kid
        Op op = ee.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=ee.begin(), iend=ee.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec((*i)[0], true));
        res = substitutivityRule(op, thms);
        res = transitivityRule(thm0, res);
      }
      break;
    }
    case BVPLUS:
      // FIXME: Need to implement the following transformation:
      // ~(x+y) <=> ~x+~y+1
      // (because  ~(x+y)+1= -(x+y) = -x-y = ~x+1+~y+1)
    case BVMULT:
      // FIXME: Need to implement the following transformation:
      // ~(x*y) <=> (~x+1)*y-1 
      // [ where we prefer x to be constant/AND/OR/NEG and then
      //   BVPLUS, and only then everything else].
      // (because  ~(x*y)+1= -(x+y) = (-x)*y = (~x+1)*y)
    default:
      res = reflexivityRule(NegExpr);
      break;
    }
  } else { // if(!neg)
    switch(e.getOpKind()) {
    case BVNEG: 
      res = pushNegationRec(e[0], true); 
      break;
    case CONCAT:
    case BVAND:
    case BVOR: {
      if (e.arity() == 0) res = reflexivityRule(e);
      else {
        Op op = e.getOp();
        vector<Theorem> thms;
        for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
          thms.push_back(pushNegationRec(*i, false));
        res = substitutivityRule(op, thms);
        res = transitivityRule(res, rewrite(res.getRHS()));
      }
      break;
    }
    default:
      res = reflexivityRule(e);
      break;
    } // end of switch(e.getOpKind())
  }
  TRACE("TheoryBitvector::pushNegation", "pushNegationRec => ", res, "}");
  d_pushNegCache[neg? NegExpr : e] = res;
  return res;
}

Theorem TheoryBitvector::pushNegationRec(const Theorem& thm, bool neg) {
  DebugAssert(thm.isRewrite(), 
	      "TheoryBitvector::pushNegationRec(Theorem): bad theorem: "
	      + thm.toString());
  Expr e(thm.getRHS());
  if(neg) {
    DebugAssert(e.isNot(), 
		"TheoryBitvector::pushNegationRec(Theorem, neg = true): bad Theorem: "
		+ thm.toString());
    e = e[0];
  }
  return transitivityRule(thm, pushNegationRec(e, neg));
}

// We assume that the cache is initially empty
Theorem TheoryBitvector::pushNegation(const Expr& e) {
  d_pushNegCache.clear();
  Theorem res;
  if(BVNEG == e.getOpKind())
    res = pushNegationRec(e[0], true);
  else if(BITVECTOR == e.getType().getExpr().getOpKind())
    res = pushNegationRec(e, false);
  else
    res = reflexivityRule(e);
  return res;
}

//! Top down simplifier
Theorem TheoryBitvector::simplifyOp(const Expr& e) {
  if (e.arity() > 0) {
    Expr ee(e);
    Theorem thm0;
    switch(e.getOpKind()) {
    case BVNEG:
      if(*d_pushNegationFlag)
	thm0 = pushNegation(e);
      break;
    case EXTRACT:
      switch(e[0].getOpKind()) {
      case BVPLUS:
	thm0 = d_rules->extractBVPlus(e);
	break;
      case BVMULT:
	thm0 = d_rules->extractBVMult(e);
	break;
      default:
	thm0 = reflexivityRule(e);
	break;
      }
      break;
    case BVPLUS:
      break;
    case BVMULT:
      //      thm0 = d_rules->padBVMult(e);
      break;
    case CONCAT: // 0bin0_[k] @ BVPLUS(n, args) => BVPLUS(n+k, args)
      if(e.arity()==2 && e[0].getKind()==BVCONST && e[1].getOpKind()==BVPLUS
	 && computeBVConst(e[0]) == 0) {
	thm0 = d_rules->bvplusZeroConcatRule(e);
      }
      break;
    case RIGHTSHIFT:
      thm0 = d_rules->rightShiftToConcat(e);
      break;
    case LEFTSHIFT:
      thm0 = d_rules->leftShiftToConcat(e);
      break;
    case CONST_WIDTH_LEFTSHIFT:
      thm0 = d_rules->constWidthLeftShiftToConcat(e);
      break;
    default:
      thm0 = reflexivityRule(e);
      break;
    }
    vector<Theorem> newChildrenThm;
    vector<unsigned> changed;
    if(thm0.isNull()) thm0 = reflexivityRule(e);
    ee = thm0.getRHS();
    int ar = ee.arity();
    for(int k = 0; k < ar; ++k) {
      // Recursively simplify the kids	
      Theorem thm = simplify(ee[k]);
      if (thm.getLHS() != thm.getRHS()) {
	newChildrenThm.push_back(thm);
	changed.push_back(k);
      }
    }
    if(changed.size() > 0) {
      Theorem thm1 = substitutivityRule(ee, changed, newChildrenThm);
      return transitivityRule(thm0,thm1);
    } else
      return thm0;
  }
  return reflexivityRule(e);
}

///////////////////////////////////////////////////////////////////////////////
// TheoryBitvector Public Methods                                            //
///////////////////////////////////////////////////////////////////////////////
TheoryBitvector::TheoryBitvector(TheoryCore* core)
  : Theory(core, "Bitvector"),
    d_bvDelayEq(core->getStatistics().counter("bv delayed assert eqs")),
    d_bvAssertEq(core->getStatistics().counter("bv eager assert eqs")),
    d_bvDelayDiseq(core->getStatistics().counter("bv delayed assert diseqs")),
    d_bvAssertDiseq(core->getStatistics().counter("bv eager assert diseqs")),
    d_bvTypePreds(core->getStatistics().counter("bv type preds enqueued")),
    d_bvDelayTypePreds(core->getStatistics().counter("bv type preds delayed")),
    d_bvBitBlastEq(core->getStatistics().counter("bv bitblast eqs")),
    d_bvBitBlastDiseq(core->getStatistics().counter("bv bitblast diseqs")),
    d_bv32Flag(&(core->getFlags()["bv32-flag"].getBool())),
    d_rewriteFlag(&(core->getFlags()["bv-rewrite"].getBool())),
    d_concatRewriteFlag(&(core->getFlags()["bv-concatnormal-rewrite"].getBool())),
    d_bvplusRewriteFlag(&(core->getFlags()["bv-plusnormal-rewrite"].getBool())),
    d_rwBitBlastFlag(&(core->getFlags()["bv-rw-bitblast"].getBool())),
    d_cnfBitBlastFlag(&(core->getFlags()["bv-cnf-bitblast"].getBool())),
    d_lhsMinusRhsFlag(&(core->getFlags()["bv-lhs-minus-rhs"].getBool())),
    d_pushNegationFlag(&(core->getFlags()["bv-pushnegation"].getBool())),
    d_bitvecCache(core->getCM()->getCurrentContext()),
    d_eq(core->getCM()->getCurrentContext()),
    d_eqIdx(core->getCM()->getCurrentContext(), 0, 0),
    d_eqBlastIdx(core->getCM()->getCurrentContext(), 0, 0),
    d_diseq(core->getCM()->getCurrentContext()),
    d_diseqIdx(core->getCM()->getCurrentContext(), 0, 0),
    d_staleDB(core->getCM()->getCurrentContext()),
    d_tccs(core->getCM()->getCurrentContext()),
    d_tccsIdx(core->getCM()->getCurrentContext(), 0, 0),
    d_sharedSubterms(core->getCM()->getCurrentContext()),
    d_sharedSubtermsList(core->getCM()->getCurrentContext()),
    d_typePredsCache(core->getCM()->getCurrentContext()),
    d_maxLength(0),
    d_index1(core->getCM()->getCurrentContext(), 0, 0)
{
  getEM()->newKind(BITVECTOR, "BITVECTOR", true);
  getEM()->newKind(BVCONST, "BVCONST");
  getEM()->newKind(HEXBVCONST, "HEXBVCONST");
  getEM()->newKind(CONCAT, "CONCAT");
  getEM()->newKind(BVOR, "BVOR");
  getEM()->newKind(BVAND, "BVAND");
  getEM()->newKind(BVXOR, "BVXOR");
  getEM()->newKind(BVNAND, "BVNAND");
  getEM()->newKind(BVNOR, "BVNOR");
  getEM()->newKind(BVXNOR, "BVXNOR");
  getEM()->newKind(BVNEG, "BVNEG");
  getEM()->newKind(EXTRACT, "EXTRACT");
  getEM()->newKind(LEFTSHIFT, "LEFTSHIFT");
  getEM()->newKind(CONST_WIDTH_LEFTSHIFT, "CONST_WIDTH_LEFTSHIFT");
  getEM()->newKind(RIGHTSHIFT, "RIGHTSHIFT");
  getEM()->newKind(VARSHIFT, "VARSHIFT");
  getEM()->newKind(BVPLUS, "BVPLUS");
  getEM()->newKind(BVMULT, "BVMULT");
  getEM()->newKind(BVSUB, "BVSUB");
  getEM()->newKind(BVUMINUS, "BVUMINUS");
  getEM()->newKind(BOOLEXTRACT, "BOOLEXTRACT");
  getEM()->newKind(SX,"SX");
  getEM()->newKind(SBVLT, "SBVLT");
  getEM()->newKind(SBVLE, "SBVLE");
  getEM()->newKind(SBVGT, "SBVGT");
  getEM()->newKind(SBVGE, "SBVGE");
  getEM()->newKind(BVLT, "BVLT");
  getEM()->newKind(BVLE, "BVLE");
  getEM()->newKind(BVGT, "BVGT");
  getEM()->newKind(BVGE, "BVGE");
  getEM()->newKind(INTTOBV, "INTTOBV");
  getEM()->newKind(BVTOINT, "BVTOINT");
  getEM()->newKind(BVTYPEPRED, "BVTYPEPRED");
  getEM()->newKind(BVPARAMOP, "BVPARAMOP");

 
  std::vector<int> kinds;
  kinds.push_back(BITVECTOR);
  kinds.push_back(BVCONST);
  kinds.push_back(HEXBVCONST);
  kinds.push_back(CONCAT);
  kinds.push_back(BVOR);
  kinds.push_back(BVAND);
  kinds.push_back(BVXOR);
  kinds.push_back(BVXNOR);
  kinds.push_back(BVNAND);
  kinds.push_back(BVNOR);
  kinds.push_back(BVNEG);
  kinds.push_back(EXTRACT);
  kinds.push_back(LEFTSHIFT);
  kinds.push_back(CONST_WIDTH_LEFTSHIFT);
  kinds.push_back(RIGHTSHIFT);
  kinds.push_back(VARSHIFT);
  kinds.push_back(BVPLUS);
  kinds.push_back(BVMULT);
  kinds.push_back(BVSUB);
  kinds.push_back(BVUMINUS);
  kinds.push_back(BOOLEXTRACT);
  kinds.push_back(SX);
  kinds.push_back(SBVLT);
  kinds.push_back(SBVLE);
  kinds.push_back(SBVGT);
  kinds.push_back(SBVGE);
  kinds.push_back(BVLT);
  kinds.push_back(BVLE);
  kinds.push_back(BVGT);
  kinds.push_back(BVGE);
  kinds.push_back(INTTOBV);
  kinds.push_back(BVTOINT);
  kinds.push_back(BVTYPEPRED);
  kinds.push_back(BVPARAMOP);

  registerTheory(this, kinds);
 
  d_bvConstExprIndex = getEM()->registerSubclass(sizeof(BVConstExpr));

  // Cache constants 0bin0 and 0bin1
  vector<bool> bits(1);
  bits[0]=false;
  d_bvZero = newBVConstExpr(bits);
  bits[0]=true;
  d_bvOne = newBVConstExpr(bits);

  // Instantiate the rules after all expression creation is
  // registered, since the constructor creates some bit-vector
  // expressions.
  d_rules = createProofRules();
}


// Destructor: delete the proof rules class if it's present
TheoryBitvector::~TheoryBitvector() {
  if(d_rules != NULL) delete d_rules;
}

// Main theory API

void TheoryBitvector::addSharedTerm(const Expr& e)
{
  if(d_sharedSubterms.count(e)>0) return;
  TRACE("bvAddSharedTerm", "TheoryBitvector::addSharedTerm(", e.toString(PRESENTATION_LANG), ")");
  IF_DEBUG(debugger.counter("bv shared subterms")++);
  d_sharedSubterms[e]=e;
  d_sharedSubtermsList.push_back(e);
  e.addToNotify(this, Expr());
  // Bitblast this term
//   Theorem thm;
//   for (int i = 0; i < BVSize(e); ++i) {
//     thm = bitBlastTerm(e, i, 0);
//     if (thm.getLHS() == thm.getRHS()) {
//       addSplitter(thm.getLHS());
//     }
//     else enqueueFact(thm);
//   }
}


void TheoryBitvector::assertFact(const Theorem& e)
{
  TRACE("bvAssertFact", "TheoryBitvector::assertFact(", e.getExpr().toString(PRESENTATION_LANG), ")");
  const Expr& expr = e.getExpr();

  switch(expr.getOpKind()) {
    case NOT: {
      const Expr& e0 = expr[0];
      switch(e0.getOpKind()) {
        case BVTYPEPRED:
          assertTypePred(e0[0], e);
          break;
        default:
          break;
      }
      break;
    }
    case BVTYPEPRED:
      assertTypePred(expr[0], e);
      break;
    default:
      break;
  }
}


void
TheoryBitvector::assertTypePred(const Expr& e, const Theorem& pred) {
  // Ignore bitvector constants (they always satisfy type predicates)
  // and bitvector operators.  When rewrites and updates are enabled.
  // their type predicates will be implicitly derived from the type
  // predicates of the arguments.

  if (theoryOf(e) == this) return;
  TRACE("bvAssertTypePred", "TheoryBitvector::assertTypePred(", e.toString(PRESENTATION_LANG), ")");
  addSharedTerm(e);
}


bool TheoryBitvector::comparebv(const Expr& e1, const Expr& e2)
{
  int size = BVSize(e1);
  FatalAssert(size == BVSize(e2), "expected same size");
  Expr c1, c2, value1, value2;
  for (int i = 0; i < size; ++i) {
    c1 = bitBlastTerm(e1, i).getRHS();
    value1 = simplifyExpr(c1);
    c2 = bitBlastTerm(e2, i).getRHS();
    value2 = simplifyExpr(c2);
    if (value1.isBoolConst() && value2.isBoolConst() && value1 != value2) return false;
  }
  return true;
}


void TheoryBitvector::checkSat(bool fullEffort) {
  if(fullEffort) {

    unsigned size = d_sharedSubtermsList.size(), j;
    Theorem thm;
//     d_evalCache.clear();
    for (; d_index1 < size; d_index1 = d_index1 + 1) {
      const Expr& e1 = d_sharedSubtermsList[d_index1];
      if (e1.getKind() == BVCONST) continue;
      if (find(e1).getRHS() != e1) continue;
      for (j = 0; j < size; ++j) {
        const Expr& e2 = d_sharedSubtermsList[j];
        if (j < d_index1 && e2.getKind() != BVCONST) continue;
        else if (j == d_index1) continue;
        if (find(e2).getRHS() != e2) continue;
        DebugAssert(e1 != e2, "should be distinct");
        if (BVSize(e1) != BVSize(e2)) continue;
        if (!comparebv(e1, e2)) continue;
        thm = bitBlastEqn(e1.eqExpr(e2));
        thm = iffMP(thm, simplify(thm.getExpr()));
        if (thm.getExpr().isTrue()) continue;
        enqueueFact(thm);
//         d_evalCache.clear();
        return;
      }
    }
//     d_evalCache.clear();
  }
}


Theorem TheoryBitvector::rewrite(const Expr& e) {
  Theorem res;
  if(*d_rewriteFlag)
    res = rewriteBV(e, true);
  else {
    res = rewriteConst(e);
    IF_DEBUG(if(res.getRHS()!=res.getLHS())
	     debugger.counter("bv rewrite const")++);
    // Ensure that the result is a find pointer of itself (if it has any)
    Expr rhs = res.getRHS();
    if(rhs.hasFind())
      res = transitivityRule(res, find(rhs));
  }
  return res;
}

Theorem TheoryBitvector::rewriteAtomic(const Expr& e) {
  TRACE("bv rewriteatomic", "rewriteAtomic(", e.toString(), ") {"); 
  
  Theorem res = reflexivityRule(e);
  if(*d_cnfBitBlastFlag && res.getRHS().isEq()) {
    //res = rewrite(e);
    res = transitivityRule(res, bitBlastEqn(res.getRHS()));
    res = transitivityRule(res, simplify(res.getRHS()));
  }
  else if(*d_cnfBitBlastFlag && 
	  (BVLT== res.getRHS().getOpKind() || BVLE==res.getRHS().getOpKind())) {
    //res = rewrite(e);
    res = transitivityRule(res, bitBlastIneqn(res.getRHS()));
    res = transitivityRule(res, simplify(res.getRHS()));
  }
  TRACE("bv rewriteatomic", "rewriteAtomic => ", res.toString(), "}"); 
  return res;
}


// Bitblast predicates eagerly, but not terms (use shared term mechanism for terms)
void TheoryBitvector::setup(const Expr& e) {
  if (!e.isAtomicFormula()) return;
  TRACE("bvSetup", "TheoryBitvector::setup(", e.toString(PRESENTATION_LANG), ")");
  Theorem result;
  switch(e.getOpKind()) {
    case EQ: {
      // Equalities between shared subterms are handled by update and checkSat
//       if (d_sharedSubterms.count(e[0]) > 0 &&
//           d_sharedSubterms.count(e[1]) > 0) break;
      result = bitBlastEqn(e);
      break;
    }
    case BVLT:
    case BVLE: {
      result = bitBlastIneqn(e);
      break;
    }
    case BOOLEXTRACT:
      result = bitBlastTerm(e[0], getBoolExtractIndex(e));
      break;
    case BVTYPEPRED:
      break;
    default:
      FatalAssert(false, "Unexpected case");
      break;
  }
  if (result.isNull()) return;
  result = transitivityRule(result, simplify(result.getRHS()));
  enqueueFact(result);
}


void TheoryBitvector::setupExpr(const Expr& e) {
  FatalAssert(false, "not implemented");
}


void TheoryBitvector::update(const Theorem& e, const Expr& d) {
  // Constants should never change their find pointers to non-constant
  // expressions
  DebugAssert(e.getLHS().getOpKind()!=BVCONST,
	      "TheoryBitvector::update(e="+e.getExpr().toString()
	      +", d="+d.toString());
  Expr lhs = e.getLHS();
  Expr rhs = e.getRHS();

  CDMap<Expr,Expr>::iterator it = d_sharedSubterms.find(lhs);
  DebugAssert(it != d_sharedSubterms.end(), "Expected lhs to be shared");
  CDMap<Expr,Expr>::iterator it2 = d_sharedSubterms.find(rhs);
  if (it2 != d_sharedSubterms.end()) {
    // found an equality between shared subterms: bitblast it!
    if ((*it).second != lhs) {
      lhs = (*it).second;
      it = d_sharedSubterms.find(lhs);
      DebugAssert(it != d_sharedSubterms.end() && (*it).second == lhs,
                  "Invariant violated in TheoryBitvector::update");
    }
    if ((*it2).second != rhs) {
      rhs = (*it2).second;
      it2 = d_sharedSubterms.find(rhs);
      DebugAssert(it2 != d_sharedSubterms.end() && (*it2).second == rhs,
                  "Invariant violated in TheoryBitvector::update");
    }
    DebugAssert(findExpr(lhs) == e.getRHS() &&
                findExpr(rhs) == e.getRHS(), "Unexpected value for finds");
    Theorem thm = transitivityRule(find(lhs),symmetryRule(find(rhs)));
    enqueueFact(iffMP(thm, bitBlastEqn(thm.getExpr())));
  }
  else {
    d_sharedSubterms[rhs] = (*it).second;
  }
}


Theorem TheoryBitvector::solve(const Theorem& e)
{
  const Expr& lhs = e.getLHS();
  const Expr& rhs = e.getRHS();
  bool constLHS(lhs.getKind()==BVCONST);
  bool constRHS(rhs.getKind()==BVCONST);
  if(lhs != rhs) {
    if(constLHS && constRHS)
      return iffMP(e, d_rules->eqConst(e.getExpr()));
    else if(constLHS) // Put a constant on the RHS
      return symmetryRule(e);
  }
  // Otherwise don't do anything
  return e;
}


void TheoryBitvector::checkType(const Expr& e)
{
  switch (e.getOpKind()) {
    case BITVECTOR: 
      //TODO: check that this is a well-formed type
      break;
    default:
      DebugAssert(false, "Unexpected kind in TheoryBitvector::checkType"
                  +getEM()->getKindName(e.getOpKind()));
  }
}


void TheoryBitvector::computeType(const Expr& e)
{
  if (e.isApply()) {
    switch(e.getOpKind()) {
      case BOOLEXTRACT: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "attempted extraction from non-bitvector \n"+ 
                                   e.toString());
        int extractLength = getBoolExtractIndex(e);
        if(!(0 <= extractLength))
          throw TypecheckException("Type Checking error: \n"
                                   "attempted out of range extraction  \n"+ 
                                   e.toString());
        e.setType(boolType());
        break;
      }
      case BVMULT:{
        if(!(2 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind() &&
             BITVECTOR == getBaseType(e[1]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in BVMULT:\n\n  "
             +e.toString());
        int bvLen = getBVMultParam(e);
        Type bvType = newBitvectorType(bvLen);
        e.setType(bvType);
        break;
      }
      case EXTRACT:{
        if(!(1 == e.arity() && 
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector extraction:\n\n  "
             + e.toString());
        int bvLength = BVSize(e[0]);
        int leftExtract = getExtractHi(e);
        int rightExtract = getExtractLow(e);
        if(!(0 <= rightExtract && 
             rightExtract <= leftExtract && leftExtract < bvLength))
          throw TypecheckException
            ("Wrong bounds in bit-vector extract:\n\n  "+e.toString());
        int extractLength = leftExtract - rightExtract + 1;
        Type bvType = newBitvectorType(extractLength);
        e.setType(bvType);
        break;
      }
      case BVPLUS: {
        int bvPlusLength = getBVPlusParam(e);
        if(!(0 <= bvPlusLength))
          throw TypecheckException
            ("Bad bit-vector length specified in BVPLUS expression:\n\n  "
             + e.toString());
        for(Expr::iterator i=e.begin(), iend=e.end(); i != iend; ++i) {
          if(BITVECTOR != getBaseType(*i).getExpr().getOpKind())
            throw TypecheckException
              ("Not a bit-vector expression in BVPLUS:\n\n  "+e.toString());
        }
        Type bvType = newBitvectorType(bvPlusLength);
        e.setType(bvType);
        break;
      }
      case LEFTSHIFT: {
        if(!(1 == e.arity() && 
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector shift:\n\n  "
             +e.toString());
        int bvLength = BVSize(e[0]);
        int shiftLength = getFixedLeftShiftParam(e);
        if(!(shiftLength >= 0))
          throw TypecheckException("Bad shift value in bit-vector shift:\n\n  "
                                   +e.toString());
        int newLength = bvLength + shiftLength;
        Type bvType = newBitvectorType(newLength);
        e.setType(bvType);
        break;
      }
      case CONST_WIDTH_LEFTSHIFT: {
        if(!(1 == e.arity() && 
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector shift:\n\n  "
             +e.toString());
        int bvLength = BVSize(e[0]);
        int shiftLength = getFixedLeftShiftParam(e);
        if(!(shiftLength >= 0))
          throw TypecheckException("Bad shift value in bit-vector shift:\n\n  "
                                   +e.toString());
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case RIGHTSHIFT: {
        if(!(1 == e.arity() && 
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-vector shift:\n\n  "
             +e.toString());
        int bvLength = BVSize(e[0]);
        int shiftLength = getFixedRightShiftParam(e);
        if(!(shiftLength >= 0))
          throw TypecheckException("Bad shift value in bit-vector shift:\n\n  "
                                   +e.toString());
        //int newLength = bvLength + shiftLength;
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVTYPEPRED:    
        e.setType(boolType());
        break;
      case SX: {
        if(!(1 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException("Type Checking error:"\
                                   "non-bitvector \n"+ e.toString());
        int bvLength = getSXIndex(e);
        if(!(0 <= bvLength))
          throw TypecheckException("Type Checking error: \n"
                                   "out of range\n"+ e.toString());
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVCONST:
      case CONCAT:
      case BVUMINUS:
      case BVNEG:
      case BVAND:
      case BVOR:
      case SBVLT:
      case SBVLE:
      case BVLT:
      case BVLE:
      default:
        DebugAssert(false,
                    "TheoryBitvector::computeType: unexpected kind in application" +
                    int2string(e.getOpKind()));
        break;
    }
  }
  else {
    switch(e.getKind()) {
      case BOOLEXTRACT:
      case BVMULT:
      case EXTRACT:
      case BVPLUS:
      case LEFTSHIFT:
      case CONST_WIDTH_LEFTSHIFT:
      case RIGHTSHIFT:
      case BVTYPEPRED:
      case SX:
        // These operators are polymorphic, so don't assign them a
        // specific type.
        e.setType(Type::anyType(getEM()));
        break;
      case BVCONST: {
        Type bvType = newBitvectorType(getBVConstSize(e));
        e.setType(bvType);
        break;
      }
      case CONCAT: {
        if(e.arity() < 2) 
          throw TypecheckException
            ("Concatenation must have at least 2 bit-vectors:\n\n  "+e.toString());

        // Compute the total length of concatenation
        int bvLength(0);
        for(int i=0, iend=e.arity(); i<iend; ++i) {
          if(BITVECTOR != getBaseType(e[i]).getExpr().getOpKind())
            throw TypecheckException
              ("Not a bit-vector expression (child #"+int2string(i+1)
               +") in concatenation:\n\n  "+e[i].toString()
               +"\n\nIn the expression:\n\n  "+e.toString());
          bvLength += BVSize(e[i]);
        }
        Type bvType = newBitvectorType(bvLength);
        e.setType(bvType);
        break;
      }
      case BVUMINUS:{
        Type bvType(getBaseType(e[0]));
        if(!(1 == e.arity() &&
             BITVECTOR == bvType.getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in BVUMINUS:\n\n  "
             +e.toString());
        e.setType(bvType);
        break;
      }
      case BVNEG:{
        if(!(1 == e.arity() && 
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind()))
          throw TypecheckException
            ("Not a bit-vector expression in bit-wise negation:\n\n  "
             + e.toString());
        e.setType(e[0].getType());
        break;
      }
      case BVAND:
      case BVOR: {
        string kindStr((e.getOpKind()==BVAND)? "AND" : "OR");
        if(e.arity() < 2) 
          throw TypecheckException
            ("Bit-wise "+kindStr+" must have at least 2 bit-vectors:\n\n  "
             +e.toString());

        int bvLength(0);
        bool first(true);
        for(int i=0, iend=e.arity(); i<iend; ++i) {
          if(BITVECTOR != getBaseType(e[i]).getExpr().getOpKind())
            throw TypecheckException
              ("Not a bit-vector expression (child #"+int2string(i+1)
               +") in bit-wise "+kindStr+":\n\n  "+e[i].toString()
               +"\n\nIn the expression:\n\n  "+e.toString());
          if(first) {
            bvLength = BVSize(e[i]);
            first=false;
          } else { // Check that the size is the same for all subsequent BVs
            if(BVSize(e[i]) != bvLength)
              throw TypecheckException
                ("Mismatched bit-vector size in bit-wise "+kindStr+" (child #"
                 +int2string(i)+").\nExpected type: "
                 +newBitvectorType(bvLength).toString()
                 +"\nFound: "+e[i].getType().toString()
                 +"\nIn the following expression:\n\n  "+e.toString());
          }
        }
        e.setType(newBitvectorType(bvLength));
        break;
      }
      case SBVLT:
      case SBVLE:
      case BVLT:
      case BVLE:
        if(!(2 == e.arity() &&
             BITVECTOR == getBaseType(e[0]).getExpr().getOpKind() &&
             BITVECTOR == getBaseType(e[1]).getExpr().getOpKind()))
          throw TypecheckException
            ("BVLT/BVLE expressions must have arity=2, and"
             "each subterm must be a bitvector term:\n"
             "e = " +e.toString());
        e.setType(boolType());
        break;
      default:
        DebugAssert(false,
                    "TheoryBitvector::computeType: wrong input" +
                    int2string(e.getOpKind()));
        break;
    }
  }
  TRACE("bitvector", "TheoryBitvector::computeType => ", e.getType(), " }"); 
}


void TheoryBitvector::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  switch(e.getOpKind()) {
  case BVPLUS:
  case BVSUB:
  case BVUMINUS:
  case BVMULT:
  case LEFTSHIFT:
  case CONST_WIDTH_LEFTSHIFT:
  case RIGHTSHIFT:
  case BVOR:
  case BVAND:
  case BVXOR:
  case BVXNOR:
  case BVNAND:
  case BVNOR:
  case BVNEG:
  case VARSHIFT:
  case CONCAT:
  case EXTRACT:
  case SBVLT:
  case SBVLE:
  case SBVGT:
  case SBVGE:
  case BVLT:
  case BVLE:
  case BVGT:
  case BVGE:
  case INTTOBV:
  case BVTOINT:
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
      // getModelTerm(*i, v);
      v.push_back(*i);
    return;
  case HEXBVCONST:
  case BVCONST: // No model variables here
    return;
  default: break; // It's a variable; continue processing
  }
  
  Type tp(e.getType());
  switch(tp.getExpr().getOpKind()) {
  case BITVECTOR: {
    int n = getBitvectorTypeParam(tp);
    for(int i=0; i<n; i = i+1)
      v.push_back(newBoolExtractExpr(e, i));
    break;
  }
  default:
    v.push_back(e);
  }
}


void TheoryBitvector::computeModel(const Expr& e, std::vector<Expr>& v) {
  switch(e.getOpKind()) {
  case BVPLUS:
  case BVSUB:
  case BVUMINUS:
  case BVMULT:
  case LEFTSHIFT:
  case CONST_WIDTH_LEFTSHIFT:
  case RIGHTSHIFT:
  case BVOR:
  case BVAND:
  case BVXOR:
  case BVXNOR:
  case BVNAND:
  case BVNOR:
  case BVNEG:
  case VARSHIFT:
  case CONCAT:
  case EXTRACT:
  case SX:
  case SBVLT:
  case SBVLE:
  case SBVGT:
  case SBVGE:
  case BVLT:
  case BVLE:
  case BVGT:
  case BVGE:
  case INTTOBV:
  case BVTOINT: {
    // More primitive vars are kids, and they should have been
    // assigned concrete values
    assignValue(simplify(e));
    v.push_back(e);
    return;
  }
  case HEXBVCONST:
  case BVCONST: // No model variables here
    return;
  default: break; // It's a variable; continue processing
  }
  
  Type tp(e.getType());
  switch(tp.getExpr().getOpKind()) {
  case BITVECTOR: {
    const Rational& n = getBitvectorTypeParam(tp);
    vector<bool> bits;
    // FIXME: generate concrete assignment from bits using proof
    // rules. For now, just create a new assignment.
    for(int i=0; i<n; i++) {
      Theorem val(getModelValue(newBoolExtractExpr(e, i)));
      DebugAssert(val.getRHS().isBoolConst(), 
		  "TheoryBitvector::computeModel: unassigned bit: "
		  +val.getExpr().toString());
      bits.push_back(val.getRHS().isTrue());
    }
    Expr c(newBVConstExpr(bits));
    assignValue(e, c);
    v.push_back(e);
    break;
  }
  default:
    DebugAssert(false, "TheoryBitvector::computeModel[not BITVECTOR type]("
		+e.toString()+")");
  }
}


Expr
TheoryBitvector::computeTypePred(const Type& t, const Expr& e) {
  DebugAssert(t.getExpr().getOpKind() == BITVECTOR,
	      "TheoryBitvector::computeTypePred: t = "+t.toString());
//   switch(e.getKind()) {
//   case BVCONST:
//     return getEM()->trueExpr();
//   default:
    return newBitvectorTypePred(t, e);
    //  }
}


Expr
TheoryBitvector::computeTCC(const Expr& e) {
  Expr tcc(Theory::computeTCC(e));
  //switch(e.getOpKind()) {
  //default:
    return tcc;
  //}
}

///////////////////////////////////////////////////////////////////////////////
// Pretty-printing                                                           //
///////////////////////////////////////////////////////////////////////////////

ExprStream&
TheoryBitvector::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
  case PRESENTATION_LANG:
    switch(e.getOpKind()) {
    case BVCONST: {
      std::ostringstream ss;
      ss << "0bin";
      for(int i=(int)getBVConstSize(e)-1; i>=0; --i)
	ss << (getBVConstValue(e, i) ? "1" : "0");
      os << ss.str();
      break;
    }
    case CONCAT:
      if(e.arity() <= 1) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first=false;
	  else os << space << "@" << space;
	  os << (*i);
	}
	os << push << ")";
      }
      break;
    case BVUMINUS:
      os << "BVUMINUS(" << push << e[0] << push << ")";
      break;
    case BVSUB:
      break;
    case BVMULT:
      os << "BVMULT(" << push
	 << getBVMultParam(e) << "," << e[0] << "," << e[1]<<push<<")"; 
      break;
    case BVAND:
      if(e.arity() <= 1) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first=false;
	  else os << space << "&" << space;
	  os << (*i);
	}
	os << push << ")";
      }
      break;
    case BVOR:
      if(e.arity() <= 1) e.printAST(os);
      else {
	os << "(" << push;
	bool first(true);
	for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	  if(first) first=false;
	  else os << space << "|" << space;
	  os << (*i);
	}
	os << push << ")";
      }
      break;
    case BVNEG:
      os << "(~(" << push << e[0] << push << "))";
      break;
    case BVLT:
      os << "BVLT(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case BVLE:
      os << "BVLE(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case SBVLT:
      os << "SBVLT(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case SBVLE:
      os << "SBVLE(" << push << e[0] << "," << e[1] << push << ")";
      break;
    case EXTRACT:
      os << "(" << push << e[0] << push << ")" << pop << pop
	 << "[" << push << getExtractHi(e) << ":";
      os << getExtractLow(e) << push << "]";
      break;
    case BOOLEXTRACT:
      os << "BOOLEXTRACT(" << push  << e[0] << "," 
	 << getBoolExtractIndex(e) << push << ")";
      break;
    case SX:
      os << "SX(" << push  << e[0] << "," 
	 << push <<  getSXIndex(e) << ")";
      break;
    case LEFTSHIFT:
      os <<  "(" << push << e[0] << space << "<<" << space
	 << getFixedLeftShiftParam(e) << push << ")";
      break;
    case CONST_WIDTH_LEFTSHIFT:
      os <<  "(" << push << e[0] << space << "<<" << space
	 << getFixedLeftShiftParam(e) << push << ")";
      os << "[" << push << BVSize(e)-1 << ":0]";
      break;
    case RIGHTSHIFT:
      os <<  "(" << push << e[0] << space << ">>" << space
	 << getFixedRightShiftParam(e) << push << ")";
      break;
    case BITVECTOR: //printing type expression
      os << "BITVECTOR(" << push
	 << getBitvectorTypeParam(e) << push << ")";
      break;
    case INTTOBV:
      break;
    case BVTOINT:
      break;
    case BVPLUS:
      os << "BVPLUS(" << push << getBVPlusParam(e);
      for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
	os << push << "," << pop << space << (*i);
      }
      os << push << ")";
      break;
    case BVTYPEPRED:
      if(e.isApply()) {
	os << "BVTYPEPRED[" << push << e.getOp().getExpr()
	   << push << "," << pop << space << e[0]
	   << push << "]";
      } else
	e.printAST(os);
      break;
    default:
      e.printAST(os);
      break;
    }
    break;
  case SMTLIB_LANG:
    d_theoryUsed = true;
    switch(e.getOpKind()) {
    case BVCONST: {
      Rational r = computeBVConst(e);
      DebugAssert(r.isInteger() && r >= 0, "Expected non-negative integer");
      os << push << "(extract[" << BVSize(e)-1 << ":0]" << space << push << "bv" << r << ")";
      break;
    }
    case CONCAT:
      if (e.arity() == 0) throw SmtlibException("TheoryBitvector::print: CONCAT arity = 0");
      else if (e.arity() == 1) os << e[0];
      else {
        int i;
	for(i = 0; i < e.arity(); ++i) {
          if ((i+1) == e.arity()) {
            os << e[i];
          }
          else {
            os << "(concat" << space << push << e[i] << space << push;
          }
	}
        for (--i; i != 0; --i) os << push << ")";
      }
      break;
    case BVUMINUS:
      os << "(bvneg" << space << push << e[0] << push << ")";
      break;
    case BVSUB:
      throw SmtlibException("TheoryBitvector::print: BVSUB, SMTLIB not supported");
      break;
    case BVMULT: {
      int length = getBVMultParam(e);
      os << "(bvmul"
         << space << push << pad(length, e[0])
         << space << push << pad(length, e[1])
         << push << ")";
      break;
    }
    case BVAND:
      if (e.arity() == 0) throw SmtlibException("TheoryBitvector::print: BVAND arity = 0");
      else if (e.arity() == 1) os << e[0];
      else {
        int i;
	for(i = 0; i < e.arity(); ++i) {
          if ((i+1) == e.arity()) {
            os << e[i];
          }
          else {
            os << "(bvand" << space << push << e[i] << space << push;
          }
	}
        for (--i; i != 0; --i) os << push << ")";
      }
      break;
    case BVOR:
      if (e.arity() == 0) throw SmtlibException("TheoryBitvector::print: BVAND arity = 0");
      else if (e.arity() == 1) os << e[0];
      else {
        int i;
	for(i = 0; i < e.arity(); ++i) {
          if ((i+1) == e.arity()) {
            os << e[i];
          }
          else {
            os << "(bvor" << space << push << e[i] << space << push;
          }
	}
        for (--i; i != 0; --i) os << push << ")";
      }
      break;
    case BVNEG:
      os << "(bvnot" << space << push << e[0] << push << ")";
      break;
    case BVLT:
      os << "(bvlt" << space << push << e[0] << space << push << e[1] << push << ")";
      break;
    case BVLE:
      os << "(bvleq" << space << push << e[0] << space << push << e[1] << push << ")";
      break;
    case SBVLT:
      os << "(bvslt" << space << push << e[0] << space << push << e[1] << push << ")";
      break;
    case SBVLE:
      os << "(bvsleq" << space << push << e[0] << space << push << e[1] << push << ")";
      break;
    case BOOLEXTRACT:
      os << "(=" << space << push 
         << "(extract[" << getBoolExtractIndex(e) << ":" << getBoolExtractIndex(e) << "]";
      os << space << push << e[0] << push << ")" << space << "bit1" << push << ")";
      break;
    case EXTRACT:
      os << push << "(extract[" << getExtractHi(e) << ":" << getExtractLow(e) << "]";
      os << space << push << e[0] << push << ")";
      break;
    case SX: {
      int extend = getSXIndex(e) - BVSize(e[0]);
      if (extend == 0) os << e[0];
      else if (extend < 0)
        throw SmtlibException("TheoryBitvector::print: SX: extension is shorter than argument");
      else os << "(sign_extend" << space << push << e[0] << space << push << extend << push << ")";
      break;
    }
    case LEFTSHIFT: {
      int bvLength = getFixedLeftShiftParam(e);
      if (bvLength != 0) {
        os << "(concat" << space << push << e[0] << space;
        os << push << "(extract[" << bvLength-1 << ":0]" << space << push << "bv0)";
        os << push << ")";
        break;
      }
      // else fall-through
    }
    case CONST_WIDTH_LEFTSHIFT:
      os << "(shift_left0" << space << push << e[0] << space << push
         << getFixedLeftShiftParam(e) << push << ")";
      break;
    case RIGHTSHIFT:
      os << "(shift_right0" << space << push << e[0] << space << push
         << getFixedRightShiftParam(e) << push << ")";
      break;
    case BITVECTOR: //printing type expression
      os << push << "BitVec[" << getBitvectorTypeParam(e) << "]";
      break;
    case INTTOBV:
      throw SmtlibException("TheoryBitvector::print: INTTOBV, SMTLIB not supported");
      break;
    case BVTOINT:
      throw SmtlibException("TheoryBitvector::print: BVTOINT, SMTLIB not supported");
      break;
    case BVPLUS:
      {
        DebugAssert(e.arity() > 0, "expected arity > 0 in BVPLUS");
        int length = getBVPlusParam(e);
        int i;
        for(i = 0; i < e.arity(); ++i) {
          if ((i+1) == e.arity()) {
            os << pad(length, e[i]);
          }
          else {
            os << "(bvadd" << space << push << pad(length, e[i]) << space << push;
          }
        }
        for (--i; i != 0; --i) os << push << ")";
      }
      break;
    case BVTYPEPRED:
      throw SmtlibException("TheoryBitvector::print: BVTYPEPRED, SMTLIB not supported");
      if(e.isApply()) {
	os << "BVTYPEPRED[" << push << e.getOp().getExpr()
	   << push << "," << pop << space << e[0]
	   << push << "]";
      } else
	e.printAST(os);
      break;
    default:
      throw SmtlibException("TheoryBitvector::print: default, SMTLIB not supported");
      e.printAST(os);
      break;
    }
    break;
  default:
    switch(e.getOpKind()) {
    case BVCONST: {
      os << "0bin";
      for(int i=(int)getBVConstSize(e)-1; i>=0; --i)
	os << (getBVConstValue(e, i) ? "1" : "0");
      break;
    }
    default:
      e.printAST(os);
      break;
    }
  }
  return os;
}


///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryBitvector::parseExprOp(const Expr& e) {
  d_theoryUsed = true;
  TRACE("parser", "TheoryBitvector::parseExprOp(", e, ")");
  
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  if(!(e.arity() > 0))      
    throw ParserException("TheoryBitvector::parseExprOp: wrong input:\n\n"
			  +e.toString());
  
  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {
  case BITVECTOR:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BITVECTOR" 
			    "kind should have exactly 1 arg:\n\n" 
			    + e.toString());    
    if(!(e[1].isRational() && e[1].getRational().isInteger()))
      throw ParserException("BITVECTOR TYPE must have an integer constant" 
			    "as its first argument:\n\n"
			    +e.toString());    
    if(!(e[1].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());    
    return newBitvectorTypeExpr(e[1].getRational().getInt());
    break;
  case CONCAT: {
    if(!(e.arity() >= 3))
      throw ParserException("TheoryBitvector::parseExprOp: CONCAT" 
			    "kind should have at least 2 args:\n\n" 
			    + e.toString());
    vector<Expr> kids;
    Expr::iterator i=e.begin(), iend=e.end();
    DebugAssert(i!=iend, "TheoryBitvector::parseExprOp("+e.toString()+")");
    ++i; // Skip the first element - the operator name
    for(; i!=iend; ++i)
      kids.push_back(parseExpr(*i));
    return newConcatExpr(kids);
    break;
  }
  case BVAND: {
    if(!(e.arity() >= 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVAND " 
			    "kind should have at least 2 arg:\n\n" 
			    + e.toString());
    vector<Expr> kids;
    for(int i=1, iend=e.arity(); i<iend; ++i)
      kids.push_back(parseExpr(e[i]));
    return newBVAndExpr(kids);
    break;
  }
  case BVOR: {
    if(!(e.arity() >= 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVOR " 
			    "kind should have at least 2 arg:\n\n" 
			    + e.toString());
    vector<Expr> kids;
    for(int i=1, iend=e.arity(); i<iend; ++i)
      kids.push_back(parseExpr(e[i]));
    return newBVOrExpr(kids);
    break;
  }
  case BVXOR: {
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVXOR " 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    Expr or1 = 
      newBVAndExpr(newBVNegExpr(parseExpr(e[1])), parseExpr(e[2]));
    or1 = rewriteBV(or1,3,false).getRHS();
    Expr or2 = 
      newBVAndExpr(parseExpr(e[1]), newBVNegExpr(parseExpr(e[2])));
    or2 = rewriteBV(or2,3,false).getRHS();
    return rewrite(newBVOrExpr(or1, or2)).getRHS();
    break;
  }
  case BVXNOR: {
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVXNOR" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    Expr or1 = 
      newBVAndExpr(newBVNegExpr(parseExpr(e[1])), 
		   newBVNegExpr(parseExpr(e[2])));
    Expr or2 = newBVAndExpr(parseExpr(e[1]), parseExpr(e[2]));
    return newBVOrExpr(or1, or2);
    break;
  }
  case BVNAND:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVNAND" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    return newBVNegExpr(newBVAndExpr(parseExpr(e[1]),parseExpr(e[2])));
    break;
  case BVNOR:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVNOR" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newBVNegExpr(newBVOrExpr(parseExpr(e[1]),parseExpr(e[2])));    
    break;
  case BVLT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newBVLTExpr(parseExpr(e[1]),parseExpr(e[2]));    
    break;
  case BVLE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLE" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newBVLEExpr(parseExpr(e[1]),parseExpr(e[2]));    
    break;
  case BVGT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newBVLTExpr(parseExpr(e[2]),parseExpr(e[1]));    
    break;
  case BVGE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGE" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newBVLEExpr(parseExpr(e[2]),parseExpr(e[1]));    
    break;
  case SX:
    // smtlib format interprets the integer argument as the number of bits to
    // extend, while CVC format interprets it as the new total size.
    // The smtlib parser inserts an extra argument "_smtlib" for this operator
    // so that we can distinguish the two cases here.
    if (e.arity() == 4 &&
        e[1].getKind() == ID &&
        e[1][0].getString() == "_smtlib") {
      if(!e[3].isRational() || !e[3].getRational().isInteger())
        throw ParserException("sign_extend must have an integer constant as its"
                              " 2nd argument:\n\n"
                              +e.toString());    
      if(!(e[3].getRational().getInt() >=0 ))
        throw ParserException("sign_extend must have an integer constant as its"
                              " 2nd argument >= 0:\n\n"
                              +e.toString());
      Expr e2 = parseExpr(e[2]);
      return newSXExpr(e2, BVSize(e2) + e[3].getRational().getInt());
    }
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: SX" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("SX must have an integer constant as its"
			    " 2nd argument:\n\n"
			    +e.toString());    
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("SX must have an integer constant as its"
			    " 2nd argument >= 0:\n\n"
			    +e.toString());    
    return newSXExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case SBVLT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newSBVLTExpr(parseExpr(e[1]),parseExpr(e[2]));    
    break;
  case SBVLE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVLE" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newSBVLEExpr(parseExpr(e[1]),parseExpr(e[2]));    
    break;
  case SBVGT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newSBVLTExpr(parseExpr(e[2]),parseExpr(e[1]));    
    break;
  case SBVGE:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVGE" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());
    return newSBVLEExpr(parseExpr(e[2]),parseExpr(e[1]));    
    break;
  case BVNEG:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BVNEG" 
			    "kind should have exactly 1 arg:\n\n" 
			    + e.toString());    
    return newBVNegExpr(parseExpr(e[1]));
    break;
  case BVCONST:
    if(!(e.arity() == 2 || e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
			    "kind should have 1 or 2 args:\n\n"
			    + e.toString());
    if(!(e[1].isRational() || e[1].isString()))
      throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
			    "kind should have arg of type Rational "
			    "or String:\n\n" + e.toString());
    if(e[1].isRational()) { // ("BVCONST" value [bitwidth])
      if(e.arity()==3) {
	if(!e[2].isRational() || !e[2].getRational().isInteger())
	  throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
				"2nd argument must be an integer:\n\n"
				+e.toString());
	return newBVConstExpr(e[1].getRational(), e[2].getRational().getInt());
      } else
	return newBVConstExpr(e[1].getRational());
    } else if(e[1].isString()) { // ("BVCONST" string [base])
      if(e.arity() == 3) {
	if(!e[2].isRational() || !e[2].getRational().isInteger())
	  throw ParserException("TheoryBitvector::parseExprOp: BVCONST "
				"2nd argument must be an integer:\n\n"
				+e.toString());
	return newBVConstExpr(e[1].getString(), e[2].getRational().getInt());
      } else
	return newBVConstExpr(e[1].getString());
    }
    break;
  case HEXBVCONST:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BVCONST" 
			    "kind should have exactly 1 arg:\n\n" 
			    + e.toString());    
    if(!(e[1].isRational() || e[1].isString()))
      throw ParserException("TheoryBitvector::parseExprOp: BVCONST" 
			    "kind should have arg of type Rational" 
			    "or String:\n\n" + e.toString());    
    if(e[1].isRational()) 
      return newBVConstExpr(e[1].getRational());
    if(e[1].isString())
      return newBVConstExpr(e[1].getString(),16);
    break;
  case LEFTSHIFT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: LEFTSHIFT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("LEFTSHIFT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());    
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());    
    return newFixedLeftShiftExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case CONST_WIDTH_LEFTSHIFT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: CONST_WIDTH_LEFTSHIFT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("CONST_WIDTH_LEFTSHIFT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());    
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());    
    return newFixedConstWidthLeftShiftExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case RIGHTSHIFT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: RIGHTSHIFT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("RIGHTSHIFT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());    
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());    
    return newFixedRightShiftExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case BOOLEXTRACT:
    if(!(e.arity() == 3))
      throw ParserException("TheoryBitvector::parseExprOp: BOOLEXTRACT" 
			    "kind should have exactly 2 arg:\n\n" 
			    + e.toString());    
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("BOOLEXTRACT must have an integer constant as its"
			    " 2nd argument:\n\n"
			    +e.toString());    
    if(!(e[2].getRational().getInt() >=0 ))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());    
    return newBoolExtractExpr(parseExpr(e[1]), e[2].getRational().getInt());
    break;
  case EXTRACT:
    if(!(e.arity() == 4))
      throw ParserException("TheoryBitvector::parseExprOp: EXTRACT" 
			    "kind should have exactly 3 arg:\n\n" 
			    + e.toString());    
    if(!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("EXTRACT must have an integer constant as its "
			    "1st argument:\n\n"
			    +e.toString());    
    if(!e[2].isRational() || !e[2].getRational().isInteger())
      throw ParserException("EXTRACT must have an integer constant as its "
			    "2nd argument:\n\n"
			    +e.toString());    
    if(!(e[1].getRational().getInt() >=0 && e[2].getRational().getInt() >=0))
      throw ParserException("parameter must be an integer constant >= 0.\n"
			    +e.toString());    
    return newBVExtractExpr(parseExpr(e[3]), 
			    e[1].getRational().getInt(), 
			    e[2].getRational().getInt());
    break;
  case BVSUB: {
    if(e.arity() != 4)
      throw ParserException("BVSUB must have 3 arguments:\n\n"
			    +e.toString());
    if(!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("BVSUB must have an integer constant as its "
			    "first argument:\n\n"
			    +e.toString());
    if(!(e[1].getRational().getInt() > 0))
      throw ParserException("parameter must be an integer constant > 0.\n"
			    +e.toString());    
    int bvsublength = e[1].getRational().getInt();
    std::vector<Expr> k;
    Expr summand1 = parseExpr(e[2]);
    summand1 = pad(bvsublength, summand1);
    k.push_back(summand1);    
    Expr summand2 = parseExpr(e[3]);
    summand2 = pad(bvsublength, summand2);
    Expr bvuminus = newBVUminusExpr(summand2);
    k.push_back(bvuminus);
    return newBVPlusExpr(bvsublength, k);
    break;
  }
  case BVUMINUS:
    if(!(e.arity() == 2))
      throw ParserException("TheoryBitvector::parseExprOp: BVUMINUS" 
			    "kind should have exactly 1 arg:\n\n" 
			    + e.toString());    
    return newBVUminusExpr(parseExpr(e[1]));
    break;
  case BVPLUS: {
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    if (!e[1].isRational()) {
      int maxsize = 0;
      Expr child;
      // Parse the kids of e and push them into the vector 'k'
      for(++i; i!=iend; ++i) {
        child = parseExpr(*i);
        if (getBaseType(child).getExpr().getOpKind() != BITVECTOR) {
          throw ParserException("BVPLUS argument is not bitvector");
        }
        if (BVSize(child) > maxsize) maxsize = BVSize(child);
        k.push_back(child);
      }
      if (e.arity() == 1) return k[0];
      return newBVPlusExpr(maxsize, k);
    }
    else {
      if(!(e.arity() >= 4))
        throw ParserException("Expected at least 3 args in BVPLUS:\n\n"
                              +e.toString());
      if(!e[1].isRational() || !e[1].getRational().isInteger())
        throw ParserException
          ("Expected integer constant in BVPLUS:\n\n"
           +e.toString());
      if(!(e[1].getRational().getInt() > 0))
        throw ParserException("parameter must be an integer constant > 0.\n"
                              +e.toString());    
      // Skip first two elements of the vector of kids in 'e'.
      // The first element is the kind, and the second is the
      // numOfBits of the bvplus operator.
      ++i;++i; 
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) k.push_back(parseExpr(*i));
      return newBVPlusExpr(e[1].getRational().getInt(), k);
    }
    break;
  }
  case BVMULT: {
    vector<Expr> k;
    Expr::iterator i = e.begin(), iend=e.end();
    if (!e[1].isRational()) {
      if (e.arity() != 3) {
        throw ParserException("TheoryBitvector::parseExprOp: BVMULT: " 
                              "expected exactly 2 args:\n\n" 
                              + e.toString());
      } 
      int maxsize = 0;
      Expr child;
      // Parse the kids of e and push them into the vector 'k'
      for(++i; i!=iend; ++i) {
        child = parseExpr(*i);
        if (getBaseType(child).getExpr().getOpKind() != BITVECTOR) {
          throw ParserException("BVMULT argument is not bitvector");
        }
        if (BVSize(child) > maxsize) maxsize = BVSize(child);
        k.push_back(child);
      }
      if (e.arity() == 1) return k[0];
      return newBVMultExpr(maxsize, k[0], k[1]);
    }
    if(!(e.arity() == 4))
      throw ParserException("TheoryBitvector::parseExprOp: BVMULT: " 
			    "expected exactly 3 args:\n\n" 
			    + e.toString());    
    if(!e[1].isRational() || !e[1].getRational().isInteger())
      throw ParserException("BVMULT: expected integer constant" 
			    "as first argument:\n\n"
			    +e.toString());
    if(!(e[1].getRational().getInt() > 0))
      throw ParserException("parameter must be an integer constant > 0.\n"
			    +e.toString());        
    return newBVMultExpr(e[1].getRational().getInt(), 
			 parseExpr(e[2]), parseExpr(e[3]));
    break;
  }
  default:
    DebugAssert(false,
		"TheoryBitvector::parseExprOp: input must be either"\
		"not be a bitvector:" + int2string(e.getKind()));
    break;
  }
  return e;
}


///////////////////////////////////////////////////////////////////////////////
//helper functions
///////////////////////////////////////////////////////////////////////////////
Expr TheoryBitvector::newBitvectorTypeExpr(int bvLength) {
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBitvectorTypeExpr:\n"
	      "len of a BV must be a positive integer:\n bvlength = "+
	      int2string(bvLength));
  if (bvLength > d_maxLength)
    d_maxLength = bvLength;
  return Expr(BITVECTOR, getEM()->newRatExpr(bvLength));
}

Expr TheoryBitvector::newBitvectorTypePred(const Type& t, const Expr& e) {
  return Expr(Expr(BVTYPEPRED, t.getExpr()).mkOp(), e);
}


Expr TheoryBitvector::newBVAndExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVAndExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVAND, t1, t2);
}

Expr TheoryBitvector::newBVAndExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVAndExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVAndExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVAND, kids, getEM());
}

Expr TheoryBitvector::newBVOrExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVOrExpr: "
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise OR operator: "
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVOR, t1, t2);
}

Expr TheoryBitvector::newBVOrExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVOrExpr: "
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVOrExpr: "
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVOR, kids, getEM());
}


Expr TheoryBitvector::newBVNandExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNandExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVNAND, t1, t2);
}

Expr TheoryBitvector::newBVNandExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVNandExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVNandExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVNAND, kids, getEM());
}

Expr TheoryBitvector::newBVNorExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNorExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVNOR, t1, t2);
}

Expr TheoryBitvector::newBVNorExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVNorExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVNorExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert( BVSize(kids[i]) ==  BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVNOR, kids, getEM());
}

Expr TheoryBitvector::newBVXorExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVXorExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVXOR, t1, t2);
}

Expr TheoryBitvector::newBVXorExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVXorExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVXorExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) ==  BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVXOR, kids, getEM());
}

Expr TheoryBitvector::newBVXnorExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVXnorExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  DebugAssert(BVSize(t1) == BVSize(t2),
	      "TheoryBitvector::bitwise operator"
	      "inputs must have same length:\n t1 = " + t1.toString()
	      + "\n t2 = " + t2.toString());
  return Expr(CVC3::BVXNOR, t1, t2);
}
 
Expr TheoryBitvector::newBVXnorExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVXnorExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVXnorExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
    if(i < kids.size()-1) {
      DebugAssert(BVSize(kids[i]) == BVSize(kids[i+1]),
		  "TheoryBitvector::bitwise operator"
		  "inputs must have same length:\n t1 = " + kids[i].toString()
		  + "\n t2 = " + kids[i+1].toString());
    }
  }
  return Expr(CVC3::BVXNOR, kids, getEM());
}

Expr TheoryBitvector::newBVLTExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVLTExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::BVLT, t1, t2);
}

Expr TheoryBitvector::newBVLEExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVLEExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::BVLE, t1, t2);
}

Expr TheoryBitvector::newSXExpr(const Expr& t1, int len) {
  DebugAssert(len >=0,
	      " TheoryBitvector::newSXExpr:" 
	      "SX index must be a non-negative integer"+
	      int2string(len));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newSXExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  if(len==0) return t1;
  return Expr(Expr(SX, getEM()->newRatExpr(len)).mkOp(), t1);
}

Expr TheoryBitvector::newSBVLTExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newSBVLTExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::SBVLT, t1, t2);
}

Expr TheoryBitvector::newSBVLEExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newSBVLEExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CVC3::SBVLE, t1, t2);
}

Expr TheoryBitvector::newBVNegExpr(const Expr& t1) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNegExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(CVC3::BVNEG, t1);
}


Expr TheoryBitvector::newBVUminusExpr(const Expr& t1) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVNegExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(CVC3::BVUMINUS, t1);
}

Expr TheoryBitvector::newBoolExtractExpr(const Expr& t1, int index) {
  DebugAssert(index >=0,
	      " TheoryBitvector::newBoolExtractExpr:" 
	      "bool_extract index must be a non-negative integer"+
	      int2string(index));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVBoolExtractExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(BOOLEXTRACT, getEM()->newRatExpr(index)).mkOp(), t1);
}

Expr TheoryBitvector::newFixedLeftShiftExpr(const Expr& t1, int shiftLength) {
  DebugAssert(shiftLength >=0,
	      " TheoryBitvector::newFixedleftshift:" 
	      "fixed_shift index must be a non-negative integer"+
	      int2string(shiftLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVFixedleftshiftExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(LEFTSHIFT, getEM()->newRatExpr(shiftLength)).mkOp(), t1);
}

Expr TheoryBitvector::newFixedConstWidthLeftShiftExpr(const Expr& t1, int shiftLength) {
  DebugAssert(shiftLength >=0,
	      " TheoryBitvector::newFixedConstWidthLeftShift:" 
	      "fixed_shift index must be a non-negative integer"+
	      int2string(shiftLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVFixedleftshiftExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  return Expr(Expr(CONST_WIDTH_LEFTSHIFT, getEM()->newRatExpr(shiftLength)).mkOp(), t1);
}

Expr TheoryBitvector::newFixedRightShiftExpr(const Expr& t1, int shiftLength) {
  DebugAssert(shiftLength >=0,
	      " TheoryBitvector::newFixedRightShift:" 
	      "fixed_shift index must be a non-negative integer"+
	      int2string(shiftLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVFixedRightShiftExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString());
  if(shiftLength==0) return t1;
  return Expr(Expr(RIGHTSHIFT, getEM()->newRatExpr(shiftLength)).mkOp(), t1);
}

Expr TheoryBitvector::newConcatExpr(const Expr& t1, const Expr& t2) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVConcatExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(CONCAT, t1, t2);
}

Expr TheoryBitvector::newConcatExpr(const Expr& t1, const Expr& t2,
				    const Expr& t3) {
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind() &&
	      BITVECTOR == t3.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVConcatExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + 
	      "\n t2 = " +t2.toString() + 
	      "\n t3 =" + t3.toString());
  return Expr(CONCAT, t1, t2, t3);
}

Expr TheoryBitvector::newConcatExpr(const vector<Expr>& kids) {
  DebugAssert(kids.size() >= 2,
	      "TheoryBitvector::newBVConcatExpr:"
	      "# of subterms must be at least 2");
  for(unsigned int i=0; i<kids.size(); ++i) {
    DebugAssert(BITVECTOR == kids[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVConcatExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		kids[i].toString());
  }
  return Expr(CONCAT, kids, getEM());
}

Expr TheoryBitvector::newBVMultExpr(int bvLength,
				    const Expr& t1, const Expr& t2) {
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVmultExpr:"
	      "bvLength must be an integer > 0: bvLength = " +
	      int2string(bvLength));
  DebugAssert(BITVECTOR == t1.getType().getExpr().getOpKind() &&
	      BITVECTOR == t2.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVmultExpr:"
	      "inputs must have type BITVECTOR:\n t1 = " +
	      t1.toString() + "\n t2 = " +t2.toString());
  return Expr(Expr(BVMULT, getEM()->newRatExpr(bvLength)).mkOp(), t1, t2);
}

//! produces a string of 0's of length bvLength
Expr TheoryBitvector::newBVZeroString(int bvLength) {
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newZeroBVExpr:must be >= 0: "
	      + int2string(bvLength));
  std::vector<bool> bits;
  for(int count=0; count < bvLength; count++) {
    bits.push_back(false);
  }
  return newBVConstExpr(bits);
}

//! produces a string of 1's of length bvLength
Expr TheoryBitvector::newBVOneString(int bvLength) {
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newOneBVExpr:must be >= 0: "
	      + int2string(bvLength));
  std::vector<bool> bits;
  for(int count=0; count < bvLength; count++) {
    bits.push_back(true);
  }
  return newBVConstExpr(bits);
}

Expr TheoryBitvector::newBVConstExpr(const vector<bool>& bits) {
  DebugAssert(bits.size() > 0,
	      "TheoryBitvector::newBVConstExpr:"
	      "size of bits should be > 0");
  BVConstExpr bv(getEM(), bits, d_bvConstExprIndex);
  return getEM()->newExpr(&bv);
}

Expr TheoryBitvector::newBVConstExpr(const Rational& r, int bvLength) {
  DebugAssert(r.isInteger(),
	      "TheoryBitvector::newBVConstExpr: not an integer: "
	      + r.toString());
  DebugAssert(bvLength > 0,
	      "TheoryBitvector::newBVConstExpr: bvLength = "
	      + int2string(bvLength));
  string s(r.toString(2));
  size_t strsize = s.size();
  size_t length = bvLength;
  Expr res;
  if(length > 0 && length != strsize) {
    //either (length > strsize) or (length < strsize)
    if(length < strsize) {
      s = s.substr((strsize-length), length);
    } else {
      string zeros("");
      for(size_t i=0, pad=length-strsize; i < pad; ++i)
	zeros += "0";
      s = zeros+s;
    }
    res = newBVConstExpr(s, 2);
  } 
  else
    res = newBVConstExpr(s, 2);
  
  return res;
}

Expr TheoryBitvector::newBVConstExpr(const std::string& s, int base) {
  DebugAssert(s.size() > 0,
	      "TheoryBitvector::newBVConstExpr:"
	      "# of subterms must be at least 2");
  DebugAssert(base == 2 || base == 16, 
	      "TheoryBitvector::newBVConstExpr: base = "
	      +int2string(base));
  //hexadecimal
  std::string str = s;
  if(16 == base) {
    Rational r(str, 16);
    return newBVConstExpr(r, str.size()*4);
  } 
  else {
    BVConstExpr bv(getEM(), str, d_bvConstExprIndex);
    return getEM()->newExpr(&bv);
  }
}

Expr 
TheoryBitvector::
newBVExtractExpr(const Expr& e, int hi, int low){
  DebugAssert(low>=0 && hi>=low,
	      " TheoryBitvector::newBVExtractExpr: " 
	      "bad bv_extract indices: hi = " 
	      + int2string(hi)
	      + ", low = " 
	      + int2string(low));
  if (e.getOpKind() == LEFTSHIFT &&
      hi == BVSize(e[0])-1 &&
      low == 0) {
    return newFixedConstWidthLeftShiftExpr(e[0], getFixedLeftShiftParam(e));
  }
  DebugAssert(BITVECTOR == e.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVExtractExpr:"
	      "inputs must have type BITVECTOR:\n e = " +
	      e.toString());
  return Expr(Expr(EXTRACT,
                   getEM()->newRatExpr(hi),
                   getEM()->newRatExpr(low)).mkOp(), e);
}

Expr TheoryBitvector::newBVPlusExpr(int bvLength, 
				    const std::vector<Expr>& k) {
  DebugAssert(bvLength > 0,
	      " TheoryBitvector::newBVPlusExpr:" 
	      "bvplus length must be a positive integer: "+
	      int2string(bvLength));
  DebugAssert(k.size() > 1,
	      " TheoryBitvector::newBVPlusExpr:" 
	      " size of input vector must be greater than 0: ");
  for(unsigned int i=0; i<k.size(); ++i) {
    DebugAssert(BITVECTOR == k[i].getType().getExpr().getOpKind(),
		"TheoryBitvector::newBVPlusExpr:"
		"inputs must have type BITVECTOR:\n t1 = " +
		k[i].toString());
  }
  return Expr(Expr(BVPLUS, getEM()->newRatExpr(bvLength)).mkOp(), k);
}

//! Converts e into a BITVECTOR of length 'len'
/*!
 * \param len is the desired length of the resulting bitvector
 * \param e is the original bitvector of arbitrary length
 */
Expr 
TheoryBitvector::pad(int len, const Expr& e) {
  DebugAssert(len >=0,
	      "TheoryBitvector::newBVPlusExpr:" 
	      "padding length must be a non-negative integer: "+
	      int2string(len));
  DebugAssert(BITVECTOR == e.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVPlusExpr:" 
	      "input must be a BITVECTOR: " + e.toString());
	      
  int size = BVSize(e);
  Expr res;
  if(size == len)
    res = e;
  else if (len < size)
    res = newBVExtractExpr(e,len-1,0);
  else {
    // size < len
    Expr zero = newBVZeroString(len-size);
    res = newConcatExpr(zero,e);
  }
  return res;
}


// Accessors for expression parameters
int TheoryBitvector::getBitvectorTypeParam(const Expr& e) {
  DebugAssert(BITVECTOR == e.getKind(),
	      "TheoryBitvector::getBitvectorTypeParam: wrong kind: " +
	      e.toString());
  return e[0].getRational().getInt();
}


Type TheoryBitvector::getTypePredType(const Expr& tp) {
  DebugAssert(tp.getOpKind()==BVTYPEPRED && tp.isApply(),
	      "TheoryBitvector::getTypePredType:\n tp = "+tp.toString());
  return Type(tp.getOpExpr()[0]);
}


const Expr& TheoryBitvector::getTypePredExpr(const Expr& tp) {
  DebugAssert(tp.getOpKind()==BVTYPEPRED,
	      "TheoryBitvector::getTypePredType:\n tp = "+tp.toString());
  return tp[0];
}

int TheoryBitvector::getBoolExtractIndex(const Expr& e) {
  DebugAssert(BOOLEXTRACT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getBoolExtractIndex: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}

int TheoryBitvector::getSXIndex(const Expr& e) {
  DebugAssert(SX == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getSXIndex: wrong kind\n"+e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}

int TheoryBitvector::getFixedLeftShiftParam(const Expr& e) {
  DebugAssert(e.isApply() &&
              (LEFTSHIFT == e.getOpKind() ||
               CONST_WIDTH_LEFTSHIFT == e.getOpKind()),
	      "TheoryBitvector::getFixedLeftShiftParam: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getFixedRightShiftParam(const Expr& e) {
  DebugAssert(RIGHTSHIFT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getFixedRightShiftParam: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}

int TheoryBitvector::getExtractLow(const Expr& e) {
  DebugAssert(EXTRACT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getExtractLow: wrong kind" +
	      e.toString());
  return e.getOpExpr()[1].getRational().getInt();
}

int TheoryBitvector::getExtractHi(const Expr& e) {
  DebugAssert(EXTRACT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getExtractHi: wrong kind" +
	      e.toString());
  return e.getOpExpr()[0].getRational().getInt();
}

int TheoryBitvector::getBVPlusParam(const Expr& e) {
  DebugAssert(BVPLUS == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getBVPlusParam: wrong kind" +
	      e.toString(AST_LANG));
  return e.getOpExpr()[0].getRational().getInt();
}


int TheoryBitvector::getBVMultParam(const Expr& e) {
  DebugAssert(BVMULT == e.getOpKind() && e.isApply(),
	      "TheoryBitvector::getBVMultParam: wrong kind " +
	      e.toString(AST_LANG));
  return e.getOpExpr()[0].getRational().getInt();
}

//////////////////////////////////////////////////////////////////////
// class BVConstExpr methods
/////////////////////////////////////////////////////////////////////
//! Constructor
BVConstExpr::BVConstExpr(ExprManager* em, std::string bvconst,
			 size_t mmIndex, ExprIndex idx)
  : ExprValue(em, BVCONST, idx), d_MMIndex(mmIndex) {
  std::string::reverse_iterator i = bvconst.rbegin();
  std::string::reverse_iterator iend = bvconst.rend();
  DebugAssert(bvconst.size() > 0,
	      "TheoryBitvector::newBVConstExpr:"
	      "# of subterms must be at least 2");
  
  for(;i != iend; ++i) {
    TRACE("bitvector", "BVConstExpr: bit ", *i, "");
    if('0' == *i)
      d_bvconst.push_back(false);
    else { 
      if('1' == *i)
	d_bvconst.push_back(true);
      else
	DebugAssert(false, "BVConstExpr: bad binary bit-vector: "
		    + bvconst);
    }
  }
  TRACE("bitvector", "BVConstExpr: #bits ", d_bvconst.size(), "");
}

BVConstExpr::BVConstExpr(ExprManager* em, std::vector<bool> bvconst,
                         size_t mmIndex, ExprIndex idx)
  : ExprValue(em, BVCONST, idx), d_bvconst(bvconst), d_MMIndex(mmIndex) {
  TRACE("bitvector", "BVConstExpr(vector<bool>): arg. size = ", bvconst.size(),
	", d_bvconst.size = "+int2string(d_bvconst.size()));
}
  
size_t BVConstExpr::computeHash() const {
  std::vector<bool>::const_iterator i = d_bvconst.begin();
  std::vector<bool>::const_iterator iend = d_bvconst.end(); 
  size_t hash_value = 0;
  hash_value = ExprValue::hash(BVCONST);
  for (;i != iend; i++)
    if(*i)
      hash_value = PRIME*hash_value + HASH_VALUE_ONE;
    else 
      hash_value = PRIME*hash_value + HASH_VALUE_ZERO;
  return hash_value;
}

namespace CVC3 {

unsigned TheoryBitvector::getBVConstSize(const Expr& e)
{
  DebugAssert(BVCONST == e.getKind(), "getBVConstSize called on non-bvconst");
  const BVConstExpr* bvc = dynamic_cast<const BVConstExpr*>(e.getExprValue());
  DebugAssert(bvc, "getBVConstSize: cast failed");
  return bvc->size();
}

bool TheoryBitvector::getBVConstValue(const Expr& e, int i)
{
  DebugAssert(BVCONST == e.getKind(), "getBVConstSize called on non-bvconst");
  const BVConstExpr* bvc = dynamic_cast<const BVConstExpr*>(e.getExprValue());
  DebugAssert(bvc, "getBVConstSize: cast failed");
  return bvc->getValue(i);
}

// Computes the integer value of a bitvector constant
Rational TheoryBitvector::computeBVConst(const Expr& e) {
  DebugAssert(BVCONST == e.getKind(),
	      "TheoryBitvector::computeBVConst:" 
	      "input must be a BITVECTOR CONST: " + e.toString());
  if(*d_bv32Flag) {
    int c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + getBVConstValue(e, j) ? 1 : 0;
    Rational d(c);
    return d;
  } else {
    Rational c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + (getBVConstValue(e, j) ? Rational(1) : Rational(0));
    return c;
  }
}

// Computes the integer value of ~c+1
Rational TheoryBitvector::computeNegBVConst(const Expr& e) {
  DebugAssert(BVCONST == e.getKind(),
	      "TheoryBitvector::computeBVConst:" 
	      "input must be a BITVECTOR CONST: " + e.toString());
  if(*d_bv32Flag) {
    int c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + getBVConstValue(e, j) ? 0 : 1;
    Rational d(c+1);
    return d;
  } else {
    Rational c(0);
    for(int j=(int)getBVConstSize(e)-1; j>=0; j--)
      c = 2*c + (getBVConstValue(e, j) ? Rational(0) : Rational(1));
    return c+1;
  }
}

// Computes the integer value of a bitvector constant
Rational computeBVConst(const Expr& e) {
  DebugAssert(BVCONST == e.getKind(),
	      "TheoryBitvector::computeBVConst:" 
	      "input must be a BITVECTOR CONST: " + e.toString());
  Rational c(0);

  const BVConstExpr* bvc = dynamic_cast<const BVConstExpr*>(e.getExprValue());
  DebugAssert(bvc, "getBVConstSize: cast failed");

  for(int j=(int)bvc->size()-1; j>=0; j--)
    c = 2*c + (bvc->getValue(j) ? Rational(1) : Rational(0));
  return c;
}

Theorem
TheoryBitvector::rewriteBoolean(const Expr& e) {
  Theorem thm;
  switch (e.getKind()) {
  case NOT:
    if (e[0].isTrue())
      thm = getCommonRules()->rewriteNotTrue(e);
    else if (e[0].isFalse())
      thm = getCommonRules()->rewriteNotFalse(e);
    else if (e[0].isNot())
      thm = getCommonRules()->rewriteNotNot(e);
    break;
  case IFF: {
    thm = getCommonRules()->rewriteIff(e);
    const Expr& rhs = thm.getRHS();
    // The only time we need to rewrite the result (rhs) is when
    // e==(FALSE<=>e1) or (e1<=>FALSE), so rhs==!e1.
    if (e != rhs && rhs.isNot())
      thm = transitivityRule(thm, rewriteBoolean(rhs));
    break;
  }
  case AND:{
    std::vector<Theorem> newK;
    std::vector<unsigned> changed;
    unsigned count(0);
    for(Expr::iterator ii=e.begin(),iiend=e.end();ii!=iiend;ii++,count++) {
      Theorem temp = rewriteBoolean(*ii);
      if(temp.getLHS() != temp.getRHS()) {
	newK.push_back(temp);
	changed.push_back(count);
      }
    }
    if(changed.size() > 0) {
      Theorem res = substitutivityRule(e,changed,newK);
      thm = transitivityRule(res, rewriteAnd(res.getRHS()));
    } else
      thm = rewriteAnd(e);
  }
    break;
  case OR:{
    std::vector<Theorem> newK;
    std::vector<unsigned> changed;
    unsigned count(0);
    for(Expr::iterator ii=e.begin(),iiend=e.end();ii!=iiend;ii++,count++) {
      Theorem temp = rewriteBoolean(*ii);
      if(temp.getLHS() != temp.getRHS()) {
	newK.push_back(temp);
	changed.push_back(count);
      }
    }
    if(changed.size() > 0) {
      Theorem res = substitutivityRule(e,changed,newK);
      thm = transitivityRule(res, rewriteOr(res.getRHS()));
    } else
      thm = rewriteOr(e);
  }
    break;

  default:
    break;
  }
  if(thm.isNull()) thm = reflexivityRule(e);
  
  return thm;
}


} // end of namespace CVC3
