/*****************************************************************************/
/*!
 * \file bitvector_theorem_producer.cpp
 * 
 * Author: Vijay Ganesh
 * 
 * Created: Wed May  5 16:19:49 PST 2004
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
// CLASS: BitvectorProofRules
//
// AUTHOR: Vijay Ganesh,   05/30/2003
//
// Description: TRUSTED implementation of bitvector proof rules.
//
///////////////////////////////////////////////////////////////////////////////

// This code is trusted
#define _CVC3_TRUSTED_

#include "bitvector_theorem_producer.h"
#include "common_proof_rules.h"
#include "theory_core.h"
#include "theory_bitvector.h"

using namespace std;
using namespace CVC3;

///////////////////////////////////////////////////////////////////////
// TheoryBitvector:trusted method for creating BitvectorTheoremProducer
///////////////////////////////////////////////////////////////////////
BitvectorProofRules*
TheoryBitvector::createProofRules() {
  return new BitvectorTheoremProducer(this);
}


BitvectorTheoremProducer::BitvectorTheoremProducer(TheoryBitvector* theoryBV)
  : TheoremProducer(theoryBV->theoryCore()->getTM()),
    d_theoryBitvector(theoryBV) { 
  // Cache constants 0bin0 and 0bin1
  vector<bool> bits(1);
  bits[0]=false;
  d_bvZero = d_theoryBitvector->newBVConstExpr(bits);
  bits[0]=true;
  d_bvOne = d_theoryBitvector->newBVConstExpr(bits);
}


///////////////////////////////////////////////////////////////////////
// BitBlasting rules for equations
///////////////////////////////////////////////////////////////////////
Theorem BitvectorTheoremProducer::bitvectorFalseRule(const Theorem& thm) {
  if(CHECK_PROOFS) {
    const Expr e = thm.getExpr();
    CHECK_SOUND(e.isIff() && e[0].isIff(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be a iff theorem:\n e = "
		+e.toString());
    CHECK_SOUND(e[1].isFalse(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(e[0][0].getOpKind() == BOOLEXTRACT && 
		e[0][1].getOpKind() == BOOLEXTRACT,
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(d_theoryBitvector->getBoolExtractIndex(e[0][0]) ==
		d_theoryBitvector->getBoolExtractIndex(e[0][1]),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
  }
  const Expr& e = thm.getExpr();
  const Expr& t1 = e[0][0][0];
  const Expr& t2 = e[0][1][0];
  
  Proof pf;
  if(withProof())
    pf = newPf("bitvector_false_rule", e, thm.getProof());
  return newRWTheorem(t1.eqExpr(t2), e[1], thm.getAssumptionsRef(), pf);
}

Theorem BitvectorTheoremProducer::bitvectorTrueRule(const Theorem& thm) {
  if(CHECK_PROOFS) {
    const Expr e = thm.getExpr();
    CHECK_SOUND(e.isIff() && e[0].isIff(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be a iff theorem:\n e = "
		+e.toString());
    CHECK_SOUND(e[1].isTrue(),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(e[0][0].getKind() == NOT &&
		e[0][0][0].getOpKind() == BOOLEXTRACT && 
		e[0][1].getOpKind() == BOOLEXTRACT,
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
    CHECK_SOUND(d_theoryBitvector->getBoolExtractIndex(e[0][0][0]) ==
		d_theoryBitvector->getBoolExtractIndex(e[0][1]),
		"TheoryBitvector::bitvectorFalseRule: "
		"premise must be iff Theorem, with False as the RHS:\n e = "
		+e.toString());
  }
  const Expr& e = thm.getExpr();
  //e is (~BE(t1,i)<=>BE(t2,i))<=>true. to extract t1 we have to go 4 level deep
  //FIXME: later
  const Expr& t1 = e[0][0][0][0];
  const Expr& t2 = e[0][1][0];
  
  Proof pf;
  if(withProof())
    pf = newPf("bitvector_true_rule", e, thm.getProof());
  return newRWTheorem(t1.eqExpr(t2).negate(), e[1], thm.getAssumptionsRef(), pf);
}

Theorem BitvectorTheoremProducer::bitBlastEqnRule(const Expr& e,
						  const Expr& f) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isEq(),
		"TheoryBitvector::bitBlastEqnRule: "
		"premise must be a rewrite theorem:\n e = "
		+e.toString());
    const Expr& lhs = e[0];
    const Expr& rhs = e[1];
    const Type& leftType = lhs.getType();
    const Type& rightType = rhs.getType();
    CHECK_SOUND(BITVECTOR == leftType.getExpr().getOpKind() &&
		BITVECTOR == rightType.getExpr().getOpKind(),
		"TheoryBitvector::bitBlastEqnRule: "
		"lhs & rhs must be bitvectors:\n e ="
		+e.toString());
    int lhsLength = d_theoryBitvector->BVSize(lhs);
    int rhsLength = d_theoryBitvector->BVSize(rhs);
    CHECK_SOUND(lhsLength == rhsLength,
		"TheoryBitvector::bitBlastEqnRule: "
		"lhs & rhs must be bitvectors of same bvLength.\n size(lhs) = "
		+ int2string(lhsLength)
		+"\n size(rhs) = " 
		+ int2string(rhsLength)
		+"\n e = "+e.toString());
    int bvLength = d_theoryBitvector->BVSize(leftType.getExpr());
    CHECK_SOUND(f.isAnd(),
		"TheoryBitvector::bitBlastEqnRule: "
		"consequence of the rule must be an AND.\n f = "
		+f.toString());
    CHECK_SOUND(bvLength == f.arity(),
		"TheoryBitvector::bitBlastEqnRule: "
		"the arity of the consequence AND must "
		"equal the bvLength of the bitvector:\n f = "
		+f.toString()+"\n bvLength = "+ int2string(bvLength));
    for(int i=0; i <bvLength; i++) {
      const Expr& conjunct = f[i];
      CHECK_SOUND(conjunct.isIff() && 2 == conjunct.arity(),
		  "TheoryBitvector::bitBlastEqnRule: "
		  "each conjunct in consequent must be an IFF.\n f = "
		  +f.toString());
      const Expr& leftExtract = conjunct[0];
      const Expr& rightExtract = conjunct[1];
      CHECK_SOUND(BOOLEXTRACT == leftExtract.getOpKind(),
		  "TheoryBitvector::bitBlastEqnRule: "
		  "each conjunct in consequent must be boolextract.\n"
		  " f["+int2string(i)+"] = "+conjunct.toString());
      CHECK_SOUND(BOOLEXTRACT == rightExtract.getOpKind(),
		  "TheoryBitvector::bitBlastEqnRule: "
		  "each conjunct in consequent must be boolextract.\n"
		  " f["+int2string(i)+"] = "+conjunct.toString());
      const Expr& leftBV = leftExtract[0];
      const Expr& rightBV = rightExtract[0];
      CHECK_SOUND(leftBV == lhs && rightBV == rhs,
		  "TheoryBitvector::bitBlastEqnRule: each boolextract"
		  " must be applied to the correct bitvector.\n conjunct = "
		  +conjunct.toString()
		  +"\n leftBV = "+ leftBV.toString()
		  +"\n lhs = "+ lhs.toString()
		  +"\n rightBV = "+rightBV.toString()
		  +"\n rhs = "+rhs.toString());
      int leftBitPosition = 
	d_theoryBitvector->getBoolExtractIndex(leftExtract);
      int rightBitPosition = 
	d_theoryBitvector->getBoolExtractIndex(rightExtract);
      CHECK_SOUND(leftBitPosition == i && rightBitPosition == i,
		  "TheoryBitvector::bitBlastEqnRule: "
		  "boolextract positions must match i= "+int2string(i)
		  +"\n conjunct = "+conjunct.toString());
    }
  }
  
  Proof pf;
  if(withProof())
    pf = newPf("bit_blast_equations", e, f);
  return newRWTheorem(e, f, Assumptions::emptyAssump(), pf);
}


///////////////////////////////////////////////////////////////////////
// BitBlasting rules for dis-equations: separate rule for disequations
// for efficiency sake
///////////////////////////////////////////////////////////////////////
Theorem BitvectorTheoremProducer::bitBlastDisEqnRule(const Theorem& notE,
						     const Expr& f){

  TRACE("bitvector", "input to bitBlastDisEqnRule(", notE.toString(), ")");
  DebugAssert(notE.getExpr().isNot() && (notE.getExpr())[0].isEq(),
	      "TheoryBitvector::bitBlastDisEqnRule:"
	      "expecting an equation" + notE.getExpr().toString());
  //e is the equation
  const Expr& e = (notE.getExpr())[0];
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isEq(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"premise must be a rewrite theorem" + e.toString());
    const Expr& lhs = e[0];
    const Expr& rhs = e[1];
    const Type& leftType = lhs.getType();
    const Type& rightType = rhs.getType();
    CHECK_SOUND(BITVECTOR == leftType.getExpr().getOpKind() &&
		BITVECTOR == rightType.getExpr().getOpKind(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"lhs & rhs must be bitvectors" + e.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(leftType.getExpr()) ==
		d_theoryBitvector->BVSize(rightType.getExpr()),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"lhs & rhs must be bitvectors of same bvLength");	      
    int bvLength = d_theoryBitvector->BVSize(leftType.getExpr());
    CHECK_SOUND(f.isOr(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"consequence of the rule must be an OR" + f.toString());
    CHECK_SOUND(bvLength == f.arity(),
		"TheoryBitvector::bitBlastDisEqnRule:"
		"the arity of the consequence OR must be"
		"equal to the bvLength of the bitvector" + 
		f.toString() + int2string(bvLength));
    for(int i=0; i <bvLength; i++) {
      const Expr& disjunct = f[i];
      CHECK_SOUND(disjunct.isIff() && 
		  2 == disjunct.arity() && disjunct[0].isNot(),
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each conjunct in consequent must be an Iff"+f.toString());
      const Expr& leftExtract = (disjunct[0])[0];
      const Expr& rightExtract = disjunct[1];
      CHECK_SOUND(BOOLEXTRACT == leftExtract.getOpKind(),
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each disjunct in consequent must be boolextract" +
		  disjunct.toString());
      CHECK_SOUND(BOOLEXTRACT == rightExtract.getOpKind(),
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each conjunct in consequent must be boolextract" +
		  disjunct.toString());
      const Expr& leftBV = leftExtract[0];
      const Expr& rightBV = rightExtract[0];
      CHECK_SOUND(leftBV == lhs && rightBV == rhs,
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "each boolextract must be applied to the correct bitvector"+
		  disjunct.toString() + leftBV.toString() + lhs.toString() + 
		  rightBV.toString() + rhs.toString());
      int leftBitPosition = 
	d_theoryBitvector->getBoolExtractIndex(leftExtract);
      int rightBitPosition = 
	d_theoryBitvector->getBoolExtractIndex(rightExtract);
      CHECK_SOUND(leftBitPosition == i && rightBitPosition == i,
		  "TheoryBitvector::bitBlastDisEqnRule:"
		  "boolextract positions must match" + disjunct.toString());
    }
  }
  
  Proof pf;
  if(withProof())
    pf = newPf("bit_blast_disequations", notE.getExpr(), f, notE.getProof());
  return newTheorem(f, notE.getAssumptionsRef(), pf);
}

///////////////////////////////////////////////////////////////////////
// Rules for Inequations
///////////////////////////////////////////////////////////////////////


//! Pad the kids of BVLT/BVLE to make their bvLength equal
Theorem
BitvectorTheoremProducer::padBVLTRule(const Expr& e, int len) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((BVLT == e.getOpKind() || BVLE == e.getOpKind()) && 
		e.arity()==2,
		"BitvectorTheoremProducer::padBVLTRule: " 
		"input must e be a BVLT/BVLE: e = " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::padBVLTRule: " 
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
    CHECK_SOUND(0<len,
		"BitvectorTheoremProducer::padBVLTRule: " 
		"input len must be >=0 and an integer: len = " + 
		int2string(len));
  }
  Expr e0 = pad(len, e[0]);
  Expr e1 = pad(len, e[1]);
  int kind = e.getOpKind();

  Expr output;
  if(kind == BVLT)
    output = d_theoryBitvector->newBVLTExpr(e0,e1);
  else
    output = d_theoryBitvector->newBVLEExpr(e0,e1);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvlt_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! signExtendRule: pads the input e with topBit to length len
Theorem
BitvectorTheoremProducer::signExtendRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR==e.getType().getExpr().getOpKind(),
		"input must be a bitvector. \n e = " + e.toString());
    CHECK_SOUND(SX == e.getOpKind(),
		"input must be SX(e).\n e = " + e.toString());
    CHECK_SOUND(SX != e[0].getOpKind(),
		"input cannot have nested SX.\n e = " + e.toString());
  }   
  Expr input0 = e[0];
  //strip the top level SX applications
  while(SX == input0.getOpKind())
    input0 = input0[0];

  int bvLength = d_theoryBitvector->BVSize(e);
  int bvLength0 = d_theoryBitvector->BVSize(input0);
    
  Expr output;
  if(bvLength0 == bvLength) {
    output = input0;
  } else if(bvLength0 < bvLength) {
    std::vector<Expr> k;
    int c = bvLength - bvLength0;
    Expr topBit = 
      d_theoryBitvector->newBVExtractExpr(input0,bvLength0-1,bvLength0-1);
    while(c--)
      k.push_back(topBit);
    k.push_back(input0);
    output = d_theoryBitvector->newConcatExpr(k);
  } else
    output = d_theoryBitvector->newBVExtractExpr(input0, bvLength-1, 0);

  Proof pf;
  if(withProof())
    pf = newPf("sign_extend_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! bitExtractSXRule
Theorem
BitvectorTheoremProducer::bitExtractSXRule(const Expr& e, int i) {
  //little bit of cheating here. calling a rule from inside a rule.
  //just a shorthand
  Theorem thm = signExtendRule(e);
  Expr e_i = d_theoryBitvector->newBoolExtractExpr(e,i);
  Expr newE_i = d_theoryBitvector->newBoolExtractExpr(thm.getRHS(),i);

  Proof pf;
  if(withProof())
    pf = newPf("bitExtract_SX_rule",e,rat(i));
  Theorem result(newRWTheorem(e_i,newE_i,Assumptions::emptyAssump(),pf));
  return result;  
}


//! Pad the kids of SIGN BVLT/SIGN BVLE to make their bvLength equal
Theorem
BitvectorTheoremProducer::padBVSLTRule(const Expr& e, int len) {
  if(CHECK_PROOFS) {
    CHECK_SOUND((BVSLT == e.getOpKind() || BVSLE == e.getOpKind()) && 
		e.arity()==2,
		"BitvectorTheoremProducer::padBVSLTRule: " 
		"input must e be a BVSLT/BVSLE: e = " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::padBVSLTRule: " 
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
    CHECK_SOUND(0<=len,
		"BitvectorTheoremProducer::padBVSLTRule: " 
		"input len must be >=0 and an integer: len = " + 
		int2string(len));
  }
  Expr e0 = d_theoryBitvector->newSXExpr(e[0], len);
  Expr e1 = d_theoryBitvector->newSXExpr(e[1], len);
  int kind = e.getOpKind();

  Expr output;
  if(kind == BVSLT)
    output = d_theoryBitvector->newBVSLTExpr(e0,e1);
  else
    output = d_theoryBitvector->newBVSLEExpr(e0,e1);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvslt_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

/*! input: e0 <=(s) e1. output depends on whether the topbits(MSB) of
 *  e0 and e1 are constants. If they are constants then optimizations
 *  are done, otherwise the following rule is implemented.
 *
 *  e0 <=(s) e1 <==> (e0[n-1] AND NOT e1[n-1]) OR 
 *                   (e0[n-1] = e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
 */
Theorem
BitvectorTheoremProducer::signBVLTRule(const Expr& e, 
				       const Theorem& topBit0, 
				       const Theorem& topBit1){
  if(CHECK_PROOFS) {
    CHECK_SOUND((BVSLT == e.getOpKind() || BVSLE == e.getOpKind()) && 
		e.arity()==2,
		"BitvectorTheoremProducer::signedBVLTRule: " 
		"input must e be a BVSLT/BVSLE: e = " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::signedBVLTRule: " 
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
  }
  const Expr e0 = e[0];
  const Expr e1 = e[1];
  int e0len = d_theoryBitvector->BVSize(e0);
  int e1len = d_theoryBitvector->BVSize(e1);

  if(CHECK_PROOFS) {
    const Expr e0ext = 
      d_theoryBitvector->newBVExtractExpr(e0,e0len-1,e0len-1);
    const Expr e1ext = 
      d_theoryBitvector->newBVExtractExpr(e1,e1len-1,e1len-1);
    CHECK_SOUND(e0ext == topBit0.getLHS(),
		"BitvectorTheoremProducer::signedBVLTRule: " 
		"topBit0.getLHS() is the un-rewritten form of MSB of e0\n"
		"topBit0 is screwed up: topBit0 = " + 
		topBit0.getExpr().toString());
    CHECK_SOUND(e1ext == topBit1.getLHS(),
		"BitvectorTheoremProducer::signedBVLTRule: " 
		"topBit1.getLHS() is the un-rewritten form of MSB of e1\n"
		"topBit1 is screwed up: topBit1 = " + 
		topBit1.getExpr().toString());
    CHECK_SOUND(e0len == e1len,
		"BitvectorTheoremProducer::signedBVLTRule: " 
		"both e[0] and e[1] must have the same length\n. e =" +
		e.toString());
  }  
  const Expr MSB0 = topBit0.getRHS();
  const Expr MSB1 = topBit1.getRHS();
  
  int eKind = e.getOpKind();
  Expr output;
 
  //if both MSBs are constants, then we can optimize the output.  we
  //know precisely the value of the signed comparison in cases where
  //topbit of e0 and e1 are constants. e.g. |-1@t0 < 0@t1 is clearly
  //|-TRUE.

  //-1 indicates that both topBits are not known to be BVCONSTS
  Rational b0 = -1;
  Rational b1 = -1;
  if(MSB0.getKind() == BVCONST) b0 = d_theoryBitvector->computeBVConst(MSB0);
  if(MSB1.getKind() == BVCONST) b1 = d_theoryBitvector->computeBVConst(MSB1);

  //useful expressions to be used below
  const Expr tExpr = d_theoryBitvector->trueExpr();
  const Expr fExpr = d_theoryBitvector->falseExpr();
  const Expr MSB0isZero = MSB0.eqExpr(bvZero());
  const Expr MSB0isOne  = MSB0.eqExpr(bvOne());
  const Expr MSB1isZero = MSB1.eqExpr(bvZero());
  const Expr MSB1isOne  = MSB1.eqExpr(bvOne());

  //handle single bit e0 <=(s) e1 in a special way. this is clumsy
  //(i.e. extra and redundant code) but much more efficient and easy
  //to read
  if(e0len == 1) {
    if(b0==0 && b1==0) 
      output = eKind==BVSLT ? fExpr      : tExpr;
    else if(b0==0  && b1==1)
      output = fExpr;
    else if(b0==1  && b1==0)
      output = tExpr;
    else if(b0==1  && b1==1)
      output = eKind==BVSLT ? fExpr      : tExpr;
    else if(b0==0  && b1==-1)
      output = eKind==BVSLT ? fExpr      : MSB1isZero;
    else if(b0==1  && b1==-1)
      output = eKind==BVSLT ? MSB1isZero : tExpr;
    else if(b0==-1 && b1==0)
      output = eKind==BVSLT ? MSB0isOne  : tExpr;
    else if(b0==-1 && b1==1)
      output = eKind==BVSLT ? fExpr      : MSB0isOne;
    else
      //both b0 and b1 are -1
      output = 
	eKind==BVSLT ? 
	MSB0isOne.andExpr(MSB1isZero) : 
	MSB0isOne.orExpr(MSB1isZero);
  } else {
    //useful expressions to be used below
    Expr newE0 = d_theoryBitvector->newBVExtractExpr(e0,e0len-2,0);
    Expr newE1 = d_theoryBitvector->newBVExtractExpr(e1,e1len-2,0);
    Expr newBVLT = 
      eKind==BVSLT ?
      d_theoryBitvector->newBVLTExpr(newE0,newE1):
      d_theoryBitvector->newBVLEExpr(newE0,newE1);
//     Expr newBVLTreverse = 
//       eKind==BVSLT ?
//       d_theoryBitvector->newBVLTExpr(newE1,newE0):
//       d_theoryBitvector->newBVLEExpr(newE1,newE0);

    
    //both MSBs are simultaneously constants
    if(-1 != b0 && -1 !=b1) {
      //e0 is negative and e1 is positive
      if(b0 == 1 && b1 == 0)
	output = tExpr;
      //e0 is positive and e1 is negative
      else if(b0 == 0 && b1 == 1)
	output = fExpr;
      //e0 = e1, so result is determined by the rest of the bits
      else {
	output = newBVLT;
      }
    }
    else if(-1 != b0 && -1 == b1) {  
      //only b0 is a constant. Both topBits are not simultaneously constants. 
      
      //if (b0==0)
      //    e0 <=(s) e1 <==> NOT e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
      //else
      //    e0 <=(s) e1 <==> NOT e1[n-1] OR (e1[n-1] AND e0[n-2:0] <= e1[n-2:0]))

      output = 
	(b0==0) ?
	//means that b1 has to be 0 and e0[n-2:0] <= e1[n-2:0] 
	MSB1isZero.andExpr(newBVLT) :
	//means that either b1 is 0 or (b1 is 1 and e0[n-2:0] <= e1[n-2:0])
	MSB1isZero.orExpr(MSB1isOne.andExpr(newBVLT));
    }
    else if(-1 == b0 && -1 != b1) {  
      //only b1 is a constant. Both topBits are not simultaneously constants.     
      
      //if (b1==0)
      //    e0 <=(s) e1 <==> e0[n-1] OR (NOT e0[n-1] AND e0[n-2:0] <= e1[n-2:0]))
      //else
      //    e0 <=(s) e1 <==> e0[n-1] AND e0[n-2:0] <= e1[n-2:0]))
      
      output = 
	(b1==0) ?
	//means that either b0 must be 1 or (b0 = 0 and e0[n-2:0] <= e1[n-2:0])
	MSB0isOne.orExpr(MSB0isZero.andExpr(newBVLT)) :
	//means that b0 must be 1 and e0[n-2:0] <= e1[n-2:0]
	MSB0isOne.andExpr(newBVLT);
    } else {
      //both top bits are not constants.

      //(e0[n-1] AND NOT e1[n-1])
      Expr k0 = MSB0isOne.andExpr(MSB1isZero);
      
      //(e0[n-1] = e1[n-1])
      Expr k1 = MSB0.eqExpr(MSB1);
      
      //e0 <=(s) e1 <==> (e0[n-1] AND NOT e1[n-1]) OR 
      //                 (e0[n-1] = e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
      output = k0.orExpr(k1.andExpr(newBVLT));
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("sign_bvlt_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}


/*! NOT(e[0][0] < e[0][1]) <==> (e[0][1] <= e[0][0]), 
 *  NOT(e[0][0] <= e[0][1]) <==> (e[0][1] < e[0][0])
 */
Theorem BitvectorTheoremProducer::notBVLTRule(const Expr& e, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == NOT,
		"BitvectorTheoremProducer::notBVLTRule: "
		"input kind must be a NOT:\n e = " + e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVLT || 
		e[0].getOpKind() == BVLE,
		"BitvectorTheoremProducer::notBVLTRule: "
		"e[0] must be BVLT or BVLE: \n e = " + e.toString());
    CHECK_SOUND(kind == e[0].getOpKind(),
		"BitvectorTheoremProducer::notBVLTRule: "
		"input kind must be the correct one: e[0] = " + 
		e[0].toString());
  }
  Expr output;
  
  const Expr& e00 = e[0][0];
  const Expr& e01 = e[0][1];
  if(BVLT == e[0].getOpKind())
    output = d_theoryBitvector->newBVLEExpr(e01,e00);
  else
    output = d_theoryBitvector->newBVLTExpr(e01,e00);

  Proof pf;
  if(withProof())
    pf = newPf("not_bvlt_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! if(lhs==rhs) then we have (lhs < rhs <==> false),(lhs <= rhs <==> true)
Theorem BitvectorTheoremProducer::lhsEqRhsIneqn(const Expr& e, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLT == e.getOpKind() || BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::lhsEqRhsIneqn: "
		"input kind must be BVLT or BVLE: e = " + e.toString());
    CHECK_SOUND(kind == e.getOpKind(),
		"BitvectorTheoremProducer::lhsEqRhsIneqn: "
		"input kind must match e.getOpKind(): "
		"\n e = " + e.toString());		
    CHECK_SOUND((e.arity()==2) && (e[0]==e[1]),
		"BitvectorTheoremProducer::lhsEqRhsIneqn: "
		"input arity must be 2, and e[0] must be equal to e[1]: " 
		"\ne = " + e.toString());
  }
  Expr output;
  if(kind == BVLT)
    output = d_theoryBitvector->falseExpr();
  else 
    output = d_theoryBitvector->trueExpr();

  Proof pf;
  if(withProof())
    pf = newPf("lhs_eq_rhs_ineqn", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! |= 0 <= foo <-> TRUE
Theorem BitvectorTheoremProducer::zeroLeq(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::zeroLeq: "
		"input kind must be BVLE: e = " + e.toString());
    CHECK_SOUND(e.arity()==2 && e[0].getOpKind() == BVCONST &&
                computeBVConst(e[0]) == 0,
		"BitvectorTheoremProducer::zeroLeq: "
		"unexpected input: e = " + e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("zeroLeq", e);
  return newRWTheorem(e, d_theoryBitvector->trueExpr(), Assumptions::emptyAssump(), pf);
}


//! if indeed e[0] < e[1] then (e<==>true) else (e<==>false)
Theorem BitvectorTheoremProducer::bvConstIneqn(const Expr& e, int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLT == e.getOpKind() || BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"input kind must be BVLT or BVLE: e = " + e.toString());
    CHECK_SOUND(kind == e.getOpKind(),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"input kind must match e.getOpKind(): "
		"\n e = " + e.toString());		
    CHECK_SOUND((e.arity()==2),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"input arity must be 2: \ne = " + e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind() && BVCONST == e[1].getKind(),
		"BitvectorTheoremProducer::bvConstIneqn: "
		"e[0] and e[1] must both be constants:\n e = " + 
		e.toString());
  }

  int e0len = d_theoryBitvector->BVSize(e[0]);
  int e1len = d_theoryBitvector->BVSize(e[1]);
  if(CHECK_PROOFS)
    CHECK_SOUND(e0len == e1len,
		"BitvectorTheoremProducer::bvConstIneqn: "
		"e[0] and e[1] must have the same bvLength:\ne = " + 
		e.toString());

  Rational lhsVal = d_theoryBitvector->computeBVConst(e[0]);
  Rational rhsVal = d_theoryBitvector->computeBVConst(e[1]);
  Expr output;

  if(BVLT == kind) {
    if(lhsVal < rhsVal)
      output = d_theoryBitvector->trueExpr();
    else
      output = d_theoryBitvector->falseExpr();
  } else {
    if(lhsVal <= rhsVal)
      output = d_theoryBitvector->trueExpr();
    else
      output = d_theoryBitvector->falseExpr();
  }
  
  Proof pf;
  if(withProof())
    pf = newPf("bv_const_ineqn", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

Theorem BitvectorTheoremProducer::generalIneqn(const Expr& e, 
					       const Theorem& lhs_i, 
					       const Theorem& rhs_i, 
					       int kind) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVLT == e.getOpKind() || BVLE == e.getOpKind(),
		"BitvectorTheoremProducer::generalIneqn: "
		"input kind must be BVLT or BVLE: e = " + e.toString());
    CHECK_SOUND(kind == e.getOpKind(),
		"BitvectorTheoremProducer::generalIneqn: "
		"input kind must match e.getOpKind(): "
		"\n e = " + e.toString());		
    CHECK_SOUND((e.arity()==2),
		"BitvectorTheoremProducer::generalIneqn: "
		"input arity must be 2: \ne = " + e.toString());
    CHECK_SOUND(lhs_i.isRewrite() && rhs_i.isRewrite(),
		"BitvectorTheoremProducer::generalIneqn: "
		"lhs_i and rhs_i must be rewrite theorems: "
		"\nlhs_i = " + lhs_i.toString() +
		"\nrhs_i = " + rhs_i.toString());
  }

  int e0len = d_theoryBitvector->BVSize(e[0]);
  int e1len = d_theoryBitvector->BVSize(e[1]);
  const Expr& e0_iBit = lhs_i.getLHS();
  const Expr& e1_iBit = rhs_i.getLHS();  
  if(CHECK_PROOFS) {
    CHECK_SOUND(BOOLEXTRACT == e0_iBit.getOpKind() &&
		BOOLEXTRACT == e1_iBit.getOpKind(),
		"BitvectorTheoremProducer::generalIneqn: "
		"lhs_i.getRHS() and rhs_i.getRHS() must be BOOLEXTRACTs:" 
		"\nlhs_i = " + lhs_i.toString() + 
		"\nrhs_i = " + rhs_i.toString());
    CHECK_SOUND(e[0] == e0_iBit[0],
		"BitvectorTheoremProducer::generalIneqn: "
		"e[0] must be equal to LHS of lhs_i: \nlhs_i = " + 
		lhs_i.toString() + "\n e[0] = " + e[0].toString());
    CHECK_SOUND(e[1] == e1_iBit[0],
		"BitvectorTheoremProducer::generalIneqn: "
		"e[1] must be equal to LHS of rhs_i: \nrhs_i = " + 
		rhs_i.toString() + "\n e[1] = " + e[1].toString());
    CHECK_SOUND(e0len == e1len,
		"BitvectorTheoremProducer::generalIneqn: "
		"e[0] and e[1] must have the same bvLength:\ne = " + 
		e.toString());
    int e0_iBitIndex = 
      d_theoryBitvector->getBoolExtractIndex(e0_iBit);
    int e1_iBitIndex = 
      d_theoryBitvector->getBoolExtractIndex(e1_iBit);
    CHECK_SOUND(e0_iBitIndex == e1_iBitIndex && 
		e0_iBitIndex == e0len-1,
		"BitvectorTheoremProducer::generalIneqn: "
		"e0_iBit & e1_iBit must have same extract index: "
		"\ne0_iBit = " + e0_iBit.toString() +
		"\ne1_iBit = " + e1_iBit.toString());
  }

  //recall that lhs_i,rhs_i are produced by bitblastTerm(), and hence
  //are boolean terms. we need to make them bitvector terms
  const Expr& b1 = lhs_i.getRHS();
  const Expr& b2 = rhs_i.getRHS();
  const Expr& trueExpression = d_theoryBitvector->trueExpr();
  const Expr& falseExpression = d_theoryBitvector->falseExpr();

  if(CHECK_PROOFS) {
    CHECK_SOUND(b1.getType().isBool(),
		"BitvectorTheoremProducer::generalIneqn: "
		"b1 must be a boolean type: "
		"\n b1 = " + b1.toString());
    CHECK_SOUND(b2.getType().isBool(),
		"BitvectorTheoremProducer::generalIneqn: "
		"b2 must be boolean type: "
		"\n b2 = " + b2.toString());    
  }

  Expr output;
  // Check for the shortcuts
  if(b1.isFalse() && b2.isTrue()) // b1 < b2
    output = trueExpression;
  else if(b1.isTrue() && b2.isFalse()) // b1 > b2
    output = falseExpression;
  //   else if(e0len==1) {
  // If this is the last bit, and one of them is a constant
  //     if(kind==BVLE && (b1.isFalse() || b2.isTrue())) // F <= x or x <= T
  //       output = trueExpression;
  //     else if(kind==BVLT && (b2.isFalse() || b1.isTrue())) // x < F or T < x
  //       output = falseExpression;
  //}
  
  // No shortcuts found
  if(output.isNull()) {   
    //construct b1<=>false
    //Expr b1_0 = b1.iffExpr(falseExpression);
    Expr b1_0 = b1.notExpr();
    //construct b2<=>true
    //Expr b2_1 = b2.iffExpr(trueExpression);    
    Expr b2_1 = b2;
    //construct (b1<=>b2)
    Expr b1_eq_b2 = b1.iffExpr(b2);

    //first process the top most bits
    output = (kind==BVLT) ? 
      b1_0.andExpr(b2_1) : 
      (e0len==1) ? b1_0.orExpr(b2_1) : b1_0.andExpr(b2_1);
    
    //if the bvLength of the vector > 1 processfurther, otherwise we are
    //done
    if(e0len > 1) {
      //construct e0[n-2:0]
      Expr e0_extract = 
	d_theoryBitvector->newBVExtractExpr(e[0],e0len-2,0);
      //construct e1[n-2:0]
      Expr e1_extract = 
	d_theoryBitvector->newBVExtractExpr(e[1],e1len-2,0);

      Expr a;
      if(kind==BVLT)
	//construct e0[n-2:0] < e1[n-2:0]
	a = d_theoryBitvector->newBVLTExpr(e0_extract,e1_extract);
      else
	//construct e0[n-2:0] <= e1[n-2:0]
	a = d_theoryBitvector->newBVLEExpr(e0_extract,e1_extract);
	
      //construct (b1=b2 and a)
      Expr b1_eq_b2_and_a = b1_eq_b2.andExpr(a);
      //construct (b1=0 and/or b2=1) or (b1=b2 and a)
      output = output.orExpr(b1_eq_b2_and_a);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("general_ineqn", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

///////////////////////////////////////////////////////////////////////
// BitExtracting rules for terms
///////////////////////////////////////////////////////////////////////

//! t[i] ==> t[i:i] = 0bin1   or    NOT t[i] ==> t[i:i] = 0bin0
Theorem BitvectorTheoremProducer::bitExtractToExtract(const Theorem& thm) {
  const Expr& e = thm.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND((e.isNot() && e[0].getOpKind() == BOOLEXTRACT)
		|| (e.getOpKind() == BOOLEXTRACT),
		"BitvectorTheoremProducer::bitExtractToExtract:\n e = "
		+e.toString());
  }
  bool negative = e.isNot();
  const Expr& boolExtract = negative? e[0] : e;
  int i = d_theoryBitvector->getBoolExtractIndex(boolExtract);
  Expr lhs = d_theoryBitvector->newBVExtractExpr(boolExtract[0], i, i);

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_to_extract", e, thm.getProof());
  return newRWTheorem(lhs, negative? bvZero() : bvOne(), thm.getAssumptionsRef(), pf);
}


//! t[i] <=> t[i:i][0]   (to use rewriter for simplifying t[i:i])
Theorem BitvectorTheoremProducer::bitExtractRewrite(const Expr& x) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(x.getOpKind() == BOOLEXTRACT,
		"BitvectorTheoremProducer::bitExtractRewrite: x = "
		+x.toString());
  }
  
  int i = d_theoryBitvector->getBoolExtractIndex(x);
  const Expr& t = x[0];
  int bvLength = d_theoryBitvector->BVSize(t);

  if(CHECK_PROOFS) {
    CHECK_SOUND(0<=i && i<bvLength,
		"BitvectorTheoremProducer::bitExtractRewrite:"
		"\n bvLength = "
		+ int2string(bvLength)
		+"\n i = "+ int2string(i)
		+"\n x = "+ x.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_rewrite", x);
  Expr res = d_theoryBitvector->newBVExtractExpr(t, i, i);
  res = d_theoryBitvector->newBoolExtractExpr(res, 0);
  return newRWTheorem(x, res, Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::bitExtractConstant(const Expr & x, 
						     int i) 
{
  TRACE("bitvector", "bitExtractConstant(", x, ", "+ int2string(i) +" ) {");
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector constant.   
    CHECK_SOUND(BVCONST == x.getKind(),
		"BitvectorTheoremProducer::bitExtractConstant:"
		"the bitvector must be a constant.");
    //check if 0<= i < bvLength of bitvector constant    
    CHECK_SOUND(0 <= i && (unsigned)i < d_theoryBitvector->getBVConstSize(x),
		"BitvectorTheoremProducer::bitExtractConstant:"
		"illegal extraction attempted on the bitvector x = " 
		+ x.toString() 
		+ "\nat the position i = " 
		+ int2string(i));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  
  //extract the actual expr_value string, bitextract it at i and check
  //if the value is 'false'. if so then return c[i] <==> false else
  //return c[i] <==> true.
  Expr output;
  if(!d_theoryBitvector->getBVConstValue(x, i))
    output = d_theoryBitvector->falseExpr();
  else
    output = d_theoryBitvector->trueExpr();

  Proof pf;
  if(withProof()) pf = newPf("bit_extract_constant", x, rat(i));
  Theorem result(newRWTheorem(bitExtract,output,Assumptions::emptyAssump(),pf));
  TRACE("bitvector", "bitExtractConstant => ", result, " }");
  return result;
}


Theorem BitvectorTheoremProducer::bitExtractConcatenation(const Expr & x, 
							  int i) {
  TRACE("bitvector", "bitExtractConcatenation(", 
	x.toString(), ", "+ int2string(i) + " ) {");
  Type type = d_theoryBitvector->getBaseType(x);
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.   
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractConcatenation: "
		"term must be bitvector:\n x = "+x.toString());
    CHECK_SOUND(CONCAT == x.getOpKind() && x.arity() >= 2,
		"BitvectorTheoremProducer::bitExtractConcatenation: "
		"the bitvector must be a concat:\n x = " + x.toString());
  }

  //check if 0<= i < bvLength of bitvector constant    
  int bvLength = d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS) {
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }

  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);

  int numOfKids = x.arity();
  int lenOfKidsSeen = 0;
  Expr bitExtractKid;
  for(int count = numOfKids-1; count >= 0; --count) {
    int bvLengthOfKid = d_theoryBitvector->BVSize(x[count]);
    if(lenOfKidsSeen <= i && i < bvLengthOfKid + lenOfKidsSeen) {
      bitExtractKid = 
	d_theoryBitvector->newBoolExtractExpr(x[count], i - lenOfKidsSeen);
      break;
    }
    lenOfKidsSeen += bvLengthOfKid;
  }
  DebugAssert(!bitExtractKid.isNull(), 
	      "BitvectorTheoremProducer::bitExtractConcatenation: "
	      "something's broken...");

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_concatenation", x, rat(i));
  Theorem result(newRWTheorem(bitExtract, bitExtractKid, Assumptions::emptyAssump(), pf));
  TRACE("bitvector", "bitExtractConcatenation => ", result, " }");
  return result;
}

Theorem BitvectorTheoremProducer::bitExtractConstBVMult(const Expr& t,
							int i)
{
  TRACE("bitvector", "input to bitExtractConstBVMult(", t.toString(), ")");
  TRACE("bitvector", "input to bitExtractConstBVMult(", int2string(i), ")");

  Type type = t.getType();
  int bvLength = d_theoryBitvector->BVSize(t);
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractConstBVMult:"
		"the term must be a bitvector" + t.toString());
    CHECK_SOUND(BVMULT == t.getOpKind() && 2 == t.arity(),
		"BitvectorTheoremProducer::bitExtractConstBVMult:"
		"the term must be a bitvector" + t.toString());

    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector x = " + t.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
    CHECK_SOUND(BVCONST == t[0].getKind(),
		"BitvectorTheoremProducer::bitExtractConstBVMult:"
		"illegal BVMULT expression" + t.toString());
  }
  int len = d_theoryBitvector->BVSize(t[0]);
  std::vector<Expr> k;
  Expr t1 = pad(bvLength, t[1]);
  for(int j=0; j < len; ++j)
    if (d_theoryBitvector->getBVConstValue(t[0], j)) {
      Expr leftshiftTerm = 
	d_theoryBitvector->newFixedConstWidthLeftShiftExpr(t1, j);
      k.push_back(leftshiftTerm);
    }
  
  Expr mult;
  //size of k will always be >= 0
  switch(k.size()) {
  case 0:
    //the vector k will remain empty if all bits in coeff are 0's
    mult = d_theoryBitvector->newBVZeroString(bvLength);
    break;
  case 1:
    mult = k[0];
    break;
  default:
    mult = d_theoryBitvector->newBVPlusExpr(bvLength, k);
    break;
  }
  Expr output = d_theoryBitvector->newBoolExtractExpr(mult, i);
  
  // bool-extract of the bitvector term
  const Expr bitExtract = 
    d_theoryBitvector->newBoolExtractExpr(t, i);
    
  Proof pf;
  if(withProof()) pf = newPf("bit_extract_const_bvmult", t, rat(i));
  const Theorem result = newRWTheorem(bitExtract,output,Assumptions::emptyAssump(),pf);
  TRACE("bitvector", 
	"output of bitExtract_const_bvmult(", result, ")");
  return result;
}


Theorem BitvectorTheoremProducer::bitExtractBVMult(const Expr& t,
						   int i)
{
  TRACE("bitvector", "input to bitExtractBVMult(", t.toString(), ")");
  TRACE("bitvector", "input to bitExtractBVMult(", int2string(i), ")");

  Type type = t.getType();
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"the term must be a bitvector" + t.toString());
    CHECK_SOUND(BVMULT == t.getOpKind() && 2 == t.arity(),
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"the term must be a bitvector" + t.toString());
    int bvLength= d_theoryBitvector->BVSize(t);
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector t = " + t.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));
    CHECK_SOUND(BVCONST != t[0].getOpKind(),
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"illegal BVMULT expression" + t.toString());
  }
  int len = d_theoryBitvector->BVSize(t[0]);
  Expr trueExpression = d_theoryBitvector->trueExpr();
  std::vector<Expr> k;
  for(int j=len-1; j >= 0; j--) {
    Expr boolExt = d_theoryBitvector->newBoolExtractExpr(t[0],j);
    Expr cond = trueExpression.iffExpr(boolExt);
    Expr lShiftTerm = d_theoryBitvector->newFixedLeftShiftExpr(t[1], j);
    int shiftLen = d_theoryBitvector->BVSize(lShiftTerm);
    Expr zeroString = d_theoryBitvector->newBVZeroString(shiftLen);
    Expr iteTerm = cond.iteExpr(lShiftTerm, zeroString);
    k.push_back(iteTerm);
  }
  
  if(CHECK_PROOFS)
    CHECK_SOUND(k.size() > 0,
		"BitvectorTheoremProducer::bitExtractBVMult:"
		"size of output vector must be > 0");

  int bvLength = d_theoryBitvector->BVSize(t);  
  Expr mult;
  if(k.size() >= 2)
    mult = d_theoryBitvector->newBVPlusExpr(bvLength, k);
  else
    mult = k[0];
  Expr output = d_theoryBitvector->newBoolExtractExpr(mult, i);
  
  // bool-extract of the bitvector term
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(t, i);
    
  Proof pf;
  if(withProof()) pf = newPf("bit_extract_bvmult", t, rat(i));
  const Theorem result = newRWTheorem(bitExtract,output,Assumptions::emptyAssump(),pf);
  TRACE("bitvector","output of bitExtract_bvmult(", result, ")");
  return result;
}

Theorem BitvectorTheoremProducer::bitExtractExtraction(const Expr & x, 
						       int i) 
{
  TRACE("bitvector", "input to bitExtractExtraction(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractExtraction(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.   
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"term must be bitvector.");
    CHECK_SOUND(EXTRACT == x.getOpKind() && 1 == x.arity(), 
		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"the bitvector must be an extract." + x.toString());
    //check if 0<= i < bvLength of bitvector constant    
    int bvLength= d_theoryBitvector->BVSize(type.getExpr());
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector t = " + x.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));
    int extractLeft = d_theoryBitvector->getExtractHi(x);
    int extractRight = d_theoryBitvector->getExtractLow(x);
    CHECK_SOUND(extractLeft >= extractRight && extractLeft >= 0,
		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"illegal boolean extraction was attempted." + int2string(i) + 
		int2string(extractLeft) + int2string(extractRight));
    CHECK_SOUND(0 <= i && i < extractLeft-extractRight+1,
    		"BitvectorTheoremProducer::bitExtract-Extraction:"
		"illegal boolean extraction was attempted." + int2string(i) + 
		int2string(extractLeft) + int2string(extractRight));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  const Expr bitExtractExtraction = 
    d_theoryBitvector->newBoolExtractExpr(x[0], i + 
					  d_theoryBitvector->getExtractLow(x));
			
  Proof pf;				
  if(withProof()) pf = newPf("bit_extract_extraction", x, rat(i));
  Theorem result(newRWTheorem(bitExtract, bitExtractExtraction, Assumptions::emptyAssump(), pf));
  TRACE("bitvector", 
	"output of bitExtractExtraction(", result, ")");
  return result;
}

Theorem 
BitvectorTheoremProducer::
bitExtractBVPlus(const std::vector<Theorem>& t1BitExtractThms,
	      const std::vector<Theorem>& t2BitExtractThms,
	      const Expr& bvPlusTerm, int bitPos)
{
  TRACE("bitvector","input to bitExtractBVPlus(", bvPlusTerm.toString(), ")");
  TRACE("bitvector","input to bitExtractBVPlus(", int2string(bitPos), ")");

  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == bvPlusTerm.getOpKind() && 2 == bvPlusTerm.arity(),
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." + 
		bvPlusTerm.toString());
    CHECK_SOUND(d_theoryBitvector->getBVPlusParam(bvPlusTerm) >= 0,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." + 
		bvPlusTerm.toString());
    CHECK_SOUND(bitPos+1 == (int)t1BitExtractThms.size() &&
		bitPos+1 == (int)t2BitExtractThms.size(),
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." +
		int2string(bitPos));
    const Expr& t1 = bvPlusTerm[0];
    const Expr& t2 = bvPlusTerm[1];
    std::vector<Theorem>::const_iterator i = t1BitExtractThms.begin();
    std::vector<Theorem>::const_iterator iend = t1BitExtractThms.end();
    std::vector<Theorem>::const_iterator j = t2BitExtractThms.begin();
    for(; i !=iend; ++i, ++j) {
      const Expr& t1Expr = i->getLHS();
      const Expr& t2Expr = j->getLHS();
      CHECK_SOUND(t1Expr[0] == t1 && t2Expr[0] == t2,
		  "BitvectorTheoremProducer::bitExtractBVPlus:"
		  "illegal bitvector fed to the function." + 
		  t1Expr.toString() + " ==\n" + 
		  t1.toString() + "\n" +
		  t2.toString() + " == \n" +
		  t2Expr.toString());
    }
  }
  const Expr lhs = 
    d_theoryBitvector->newBoolExtractExpr(bvPlusTerm, bitPos);
  Expr rhs;
  const Expr& t1_iBit = (t1BitExtractThms[bitPos]).getRHS();
  const Expr& t2_iBit = (t2BitExtractThms[bitPos]).getRHS();
  if(0 != bitPos) {
    const Expr carry_iBit =
      computeCarry(t1BitExtractThms, t2BitExtractThms, bitPos);
    //constructing an XOR of 3 exprs using equivalences.  Note that (x
    //\xor y \xor z) is the same as (x \iff y \iff z). but remember, x
    //\xor y is not the same as x \iff y, but is equal instead to x
    //\neg\iff y
    rhs = t1_iBit.iffExpr(t2_iBit).iffExpr(carry_iBit);
    //cout << "the addition output is : " << rhs.toString() << "\n";
    //TRACE("bitvector",
    //  "output of bitExtractBVPlus(", carry_iBit.toString(), ")");
  } else
    //bitblasting the 0th bit. construct NOT(t1_iBit <=> t2_iBit)
    rhs = !(t1_iBit.iffExpr(t2_iBit));

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_BVPlus_rule",bvPlusTerm,rat(bitPos));
  Theorem result = newRWTheorem(lhs, rhs, Assumptions::emptyAssump(), pf);
  TRACE("bitvector","output of bitExtractBVPlus(", result, ")");
  return result;
}

Expr
BitvectorTheoremProducer::
computeCarry(const std::vector<Theorem>& t1BitExtractThms,
	     const std::vector<Theorem>& t2BitExtractThms,
	     int i){
  vector<Expr> carry;
  int bitPos = i;
  DebugAssert(bitPos >= 0,
	      "computeCarry: negative bitExtract_Pos is illegal");
  if(0 == bitPos) {
    const Expr& t1Thm = t1BitExtractThms[bitPos].getRHS();
    const Expr& t2Thm = t2BitExtractThms[bitPos].getRHS();
    carry.push_back(t1Thm.andExpr(t2Thm));
  }
  else {
    const Expr& t1Thm = t1BitExtractThms[bitPos-1].getRHS();
    const Expr& t2Thm = t2BitExtractThms[bitPos-1].getRHS();
    const Expr iMinusOneTerm = t1Thm.andExpr(t2Thm);
    carry.push_back(iMinusOneTerm);
    
    const Expr iMinusOneCarry = 
      computeCarry(t1BitExtractThms,t2BitExtractThms,bitPos-1);
    const Expr secondTerm = t1Thm.andExpr(iMinusOneCarry);
    carry.push_back(secondTerm);
    
    const Expr thirdTerm  = t2Thm.andExpr(iMinusOneCarry);

    carry.push_back(thirdTerm);
  }
  return orExpr(carry);
}

Theorem 
BitvectorTheoremProducer::
bitExtractBVPlusPreComputed(const Theorem& t1_i,
			    const Theorem& t2_i,
			    const Expr& bvPlusTerm, 
			    int bitPos,
			    int precomputedFlag)
{
  DebugAssert(0 != precomputedFlag,
	      "precomputedFlag cannot be 0");
  TRACE("bitvector","input to bitExtractBVPlus(", bvPlusTerm.toString(), ")");
  TRACE("bitvector","input to bitExtractBVPlus(", int2string(bitPos), ")");

  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == bvPlusTerm.getOpKind() && 2 == bvPlusTerm.arity(),
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." + 
		bvPlusTerm.toString());
    CHECK_SOUND(d_theoryBitvector->getBVPlusParam(bvPlusTerm) >= 0,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal bitvector fed to the function." + 
		bvPlusTerm.toString());
    const Expr& t1 = bvPlusTerm[0];
    const Expr& t2 = bvPlusTerm[1];
    CHECK_SOUND(t1_i.getLHS()[0] == t1 && 
		t2_i.getLHS()[0] == t2,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal theorems fed to the function. Theorem1 = " + 
		t1_i.toString() + "\nTheorem2 = " + t2_i.toString());
    CHECK_SOUND(t1_i.getLHS().getOpKind() == BOOLEXTRACT &&
		t2_i.getLHS().getOpKind() == BOOLEXTRACT,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal theorems fed to the function. Theorem1 = " + 
		t1_i.toString() + "\nTheorem2 = " + t2_i.toString());
    CHECK_SOUND(d_theoryBitvector->getBoolExtractIndex(t1_i.getLHS()) == bitPos &&
		d_theoryBitvector->getBoolExtractIndex(t2_i.getLHS()) == bitPos,
		"BitvectorTheoremProducer::bitExtractBVPlus:"
		"illegal theorems fed to the function. Theorem1 = " + 
		t1_i.toString() + "\nTheorem2 = " + t2_i.toString());
  }
  const Expr lhs = 
    d_theoryBitvector->newBoolExtractExpr(bvPlusTerm, bitPos);
  Expr rhs;
  const Expr& t1_iBit = t1_i.getRHS();
  const Expr& t2_iBit = t2_i.getRHS();

  const Expr carry_iBit = computeCarryPreComputed(t1_i, t2_i, bitPos, precomputedFlag);

  if(0 != bitPos) {
    //constructing an XOR of 3 exprs using equivalences.  Note that (x
    //\xor y \xor z) is the same as (x \iff y \iff z). but remember, x
    //\xor y is not the same as x \iff y, but is equal instead to x
    //\neg\iff y
    rhs = t1_iBit.iffExpr(t2_iBit).iffExpr(carry_iBit);
    //cout << "the addition output is : " << rhs.toString() << "\n";
  } else
    //bitblasting the 0th bit. construct NOT(t1_iBit <=> t2_iBit)
    rhs = !(t1_iBit.iffExpr(t2_iBit));

  Proof pf;
  if(withProof())
    pf = newPf("bit_extract_BVPlus_precomputed_rule",bvPlusTerm,rat(bitPos));
  Theorem result = newRWTheorem(lhs, rhs, Assumptions::emptyAssump(), pf);
  TRACE("bitvector","output of bitExtractBVPlus(", result, ")");
  return result;
}

//! compute carryout of the current bits and cache them, and return
//carryin of the current bits
Expr
BitvectorTheoremProducer::
computeCarryPreComputed(const Theorem& t1_i, 
			const Theorem& t2_i, 
			int bitPos, int preComputed){
  DebugAssert(1 == preComputed ||
	      2 == preComputed,
	      "cannot happen");
  Expr carryout;
  Expr carryin;
  DebugAssert(bitPos >= 0,
	      "computeCarry: negative bitExtract_Pos is illegal");

  const Expr& t1Thm = t1_i.getRHS();
  const Expr& t2Thm = t2_i.getRHS();
  Expr x = t1Thm.andExpr(t2Thm);
  const Expr& t1 = t1_i.getLHS()[0];
  const Expr& t2 = t2_i.getLHS()[0];
  Expr t1Andt2 = t1.andExpr(t2);
  Expr index = t1Andt2.andExpr(rat(bitPos));
  
  if(0 == bitPos) {    
    if(1 == preComputed)
      d_theoryBitvector->d_bvPlusCarryCacheLeftBV.insert(index,x);
    else
      d_theoryBitvector->d_bvPlusCarryCacheRightBV.insert(index,x);
    carryout = x;
    //carry.push_back(x);
  }
  else {
    if(1 == preComputed) {
      Expr indexMinusOne = t1Andt2.andExpr(rat(bitPos-1));
      if(d_theoryBitvector->d_bvPlusCarryCacheLeftBV.find(indexMinusOne) == 
	 d_theoryBitvector->d_bvPlusCarryCacheLeftBV.end())
	DebugAssert(false,
		    "this should not happen");
      carryin = 
	(d_theoryBitvector->d_bvPlusCarryCacheLeftBV).find(indexMinusOne)->second;
      Expr secondTerm = t1Thm.andExpr(carryin);
      Expr thirdTerm = t2Thm.andExpr(carryin);
      
      carryout = (x.orExpr(secondTerm)).orExpr(thirdTerm);
      d_theoryBitvector->d_bvPlusCarryCacheLeftBV.insert(index,carryout);
    }
    else {
      Expr indexMinusOne = t1Andt2.andExpr(rat(bitPos-1));
      if(d_theoryBitvector->d_bvPlusCarryCacheRightBV.find(indexMinusOne) == 
	 d_theoryBitvector->d_bvPlusCarryCacheRightBV.end())
	DebugAssert(false,
		    "this should not happen");
      carryin = 
	(d_theoryBitvector->d_bvPlusCarryCacheRightBV).find(indexMinusOne)->second;
      //(*d_bvPlusCarryCacheRightBV.find(indexMinusOne)).second;
      Expr secondTerm = t1Thm.andExpr(carryin);
      Expr thirdTerm = t2Thm.andExpr(carryin);
      
      carryout = (x.orExpr(secondTerm)).orExpr(thirdTerm);
      d_theoryBitvector->d_bvPlusCarryCacheRightBV.insert(index,carryout);
    }
  }
  //cout << "the carry for" << index << " is : " << carryout << "\n";
  return carryin;
}

Theorem
BitvectorTheoremProducer::
zeroPaddingRule(const Expr& e, int i) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == e.getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::zeroPaddingRule:"
		"Wrong Input: Input must be a bitvector. But the input is: " +
		e.toString());
  }

  int bvLength =
    d_theoryBitvector->BVSize(d_theoryBitvector->getBaseType(e).getExpr());
  
  if(CHECK_PROOFS) {
    CHECK_SOUND(0 <= i &&  i >= bvLength,
		"BitvectorTheoremProducer::zeroPaddingRule:"
		"bitPosition of extraction must be greater than bvLength" +
		int2string(i) + "bvLength:" + int2string(bvLength));
  }
  const Expr boolExtractExpr = d_theoryBitvector->newBoolExtractExpr(e, i);

  Proof pf;
  if(withProof()) 
    pf = newPf("zeropadding_rule", e, rat(i));
  return newRWTheorem(boolExtractExpr, d_theoryBitvector->falseExpr(), Assumptions::emptyAssump(), pf);
}

Theorem 
BitvectorTheoremProducer::
bvPlusAssociativityRule(const Expr& bvPlusTerm)
{
  TRACE("bitvector", 
	"input to bvPlusAssociativityRule(", bvPlusTerm.toString(), ")");

  Type type = bvPlusTerm.getType();
  if(CHECK_PROOFS) {
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bvPlusAssociativityRule:"
		"term must be BITVECTOR type.");		
    CHECK_SOUND(BVPLUS == bvPlusTerm.getOpKind(),
		"BitvectorTheoremProducer::bvPlusAssociativityRule:"
		"term must have the kind BVPLUS.");
    CHECK_SOUND(2 < bvPlusTerm.arity(),
		"BitvectorTheoremProducer::bvPlusAssociativityRule:"
		"term must have arity() greater than 2 for associativity.");
  }
  std::vector<Expr> BVPlusTerms0;
  std::vector<Expr>::const_iterator j = (bvPlusTerm.getKids()).begin();
  std::vector<Expr>::const_iterator jend = (bvPlusTerm.getKids()).end();
  //skip the first kid
  j++;
  BVPlusTerms0.insert(BVPlusTerms0.end(), j, jend);
  int bvLength = d_theoryBitvector->BVSize(bvPlusTerm);
  const Expr bvplus0 = d_theoryBitvector->newBVPlusExpr(bvLength, 
							BVPlusTerms0);
  
  std::vector<Expr> BVPlusTerms1;
  BVPlusTerms1.push_back(*((bvPlusTerm.getKids()).begin()));
  BVPlusTerms1.push_back(bvplus0);
  const Expr bvplusOutput = d_theoryBitvector->newBVPlusExpr(bvLength, 
							     BVPlusTerms1);
  
  Proof pf;
  if(withProof()) pf = newPf("bv_plus_associativityrule", bvPlusTerm);
  const Theorem result(newRWTheorem(bvPlusTerm, bvplusOutput, Assumptions::emptyAssump(), pf));
  TRACE("bitvector", 
	"output of bvPlusAssociativityRule(", result, ")");
  return result;
}


Theorem BitvectorTheoremProducer::bitExtractNot(const Expr & x, 
						int i) {
  TRACE("bitvector", "input to bitExtractNot(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractNot(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.   
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractNot:"
		"term must be bitvector.");
    CHECK_SOUND(BVNEG == x.getOpKind() && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtractNot:"
		"the bitvector must be an bitwise negation." + x.toString());
    //check if 0<= i < Length of bitvector constant    
    int bvLength= d_theoryBitvector->BVSize(type.getExpr());
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  const Expr bitNegTerm = d_theoryBitvector->newBoolExtractExpr(x[0], i);
  
  Proof pf;
  if(withProof()) pf = newPf("bit_extract_bitwiseneg", x, rat(i));
  const Theorem result(newRWTheorem(bitExtract,!bitNegTerm,Assumptions::emptyAssump(),pf));
  TRACE("bitvector","output of bitExtractNot(", result, ")");
  return result;    	    
}

Theorem
BitvectorTheoremProducer::bitExtractBitwise(const Expr & x, 
					    int i, int kind) {
  string funName = (kind==BVAND)? "bitExtractAnd" : "bitExtractOr";
  string pfName = (kind==BVAND)? "bit_extract_and" : "bit_extract_or";
  TRACE("bitvector", funName+"(", x, ", "+ int2string(i)+") {");
  Type type = x.getType();
  if(CHECK_PROOFS) {
    CHECK_SOUND(kind == BVAND || kind == BVOR,
		"BitvectorTheoremProducer::"+funName+": kind = "
		+d_theoryBitvector->getEM()->getKindName(kind));
    //check if the expr is indeed a bitvector term and a concat.   
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::"+funName+": "
		"term must be bitvector.\n x = "+x.toString()
		+" : "+type.toString());
    CHECK_SOUND(x.getOpKind() == kind && 2 <= x.arity(),
		"BitvectorTheoremProducer::"+funName+": "
		"the bitvector must be a bitwise AND.\n x = "
		+ x.toString());
    //check if 0<= i < Length of bitvector constant 
    int size = d_theoryBitvector->BVSize(x);
    CHECK_SOUND(0 <= i && i < size,
		"BitvectorTheoremProducer::"+funName+": "
		"illegal boolean extraction was attempted.\n i = "
		+ int2string(i) + "\n size = "+ int2string(size));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  vector<Expr> kids;
  for(Expr::iterator j=x.begin(), jend=x.end(); j!=jend; ++j) {
    kids.push_back(d_theoryBitvector->newBoolExtractExpr(*j, i));
  }
  
  Expr rhs = (kind==BVAND)? andExpr(kids) : orExpr(kids);

  Proof pf;
  if(withProof()) pf = newPf(pfName,x,rat(i));
  const Theorem result(newRWTheorem(bitExtract, rhs, Assumptions::emptyAssump(), pf));
  TRACE("bitvector", funName+" => ", result.toString(), " }");
  return result;    	    
}


Theorem
BitvectorTheoremProducer::bitExtractAnd(const Expr & x, int i) {
  return bitExtractBitwise(x, i, BVAND);
}


Theorem
BitvectorTheoremProducer::bitExtractOr(const Expr & x, int i) {
  return bitExtractBitwise(x, i, BVOR);
}


Theorem BitvectorTheoremProducer::bitExtractFixedLeftShift(const Expr & x,
							   int i) {
  TRACE("bitvector", "input to bitExtractFixedleftshift(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractFixedleftshift(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a left shift.
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractFixedleftshift:"
		"term must be bitvector.");
    CHECK_SOUND((x.getOpKind() == LEFTSHIFT ||
                x.getOpKind() == CONST_WIDTH_LEFTSHIFT) && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtractFixedleftshift:"
		"the bitvector must be a bitwise LEFTSHIFT." + 
		x.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedLeftShiftParam(x) >= 0,
		"BitvectorTheoremProducer::bitExtractFixedleftshift:"
		"the bitvector must be a bitwise LEFTSHIFT." + 
		x.toString());
    //check if 0<= i < bvLength of bitvector constant    
    int bvLength= d_theoryBitvector->BVSize(type.getExpr());
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector x = " + x.toString()
		+ "\nwhose bvLength is = " +
		int2string(bvLength));
  }
  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  int shiftLength = d_theoryBitvector->getFixedLeftShiftParam(x);
  Expr output;
  if(0 <= i && i < shiftLength)
    output = d_theoryBitvector->falseExpr();
  else 
    output = 
      d_theoryBitvector->newBoolExtractExpr(x[0], i-shiftLength);

  Proof pf;
  if(withProof()) 
    pf = newPf("bit_extract_bitwisefixedleftshift", x,rat(i));
  const Theorem result = newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf); 
  TRACE("bitvector",
	"output of bitExtractFixedleftshift(", result, ")");
  return result;
}

Theorem BitvectorTheoremProducer::bitExtractFixedRightShift(const Expr & x, 
							    int i) {
  TRACE("bitvector", "input to bitExtractFixedRightShift(", x.toString(), ")");
  TRACE("bitvector", "input to bitExtractFixedRightShift(", int2string(i), ")");

  Type type = x.getType();
  if(CHECK_PROOFS) {
    //check if the expr is indeed a bitvector term and a concat.   
    CHECK_SOUND(BITVECTOR == type.getExpr().getOpKind(),
		"BitvectorTheoremProducer::bitExtractFixedRightShift:"
		"term must be bitvector.");
    CHECK_SOUND(RIGHTSHIFT == x.getOpKind() && 1 == x.arity(),
		"BitvectorTheoremProducer::bitExtractFixedRightShift:"
		"the bitvector must be an bitwise RIGHTSHIFT." + 
		x.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedRightShiftParam(x) >= 0,
		"BitvectorTheoremProducer::bitExtractFixedRightShift:"
		"the bitvector must be an bitwise RIGHTSHIFT." + 
		x.toString());
  }
  //check if 0<= i < bvLength of bitvector constant    
  int bvLength = d_theoryBitvector->BVSize(x);
  if(CHECK_PROOFS)
    CHECK_SOUND(0 <= i && i < bvLength,
		"BitvectorTheoremProducer::bitExtractNot:"
		"illegal boolean extraction was attempted at position i = " 
		+ int2string(i) 
		+ "\non bitvector t = " + x.toString()
		+ "\nwhose Length is = " +
		int2string(bvLength));

  // bool-extract of the bitvector constant
  const Expr bitExtract = d_theoryBitvector->newBoolExtractExpr(x, i);
  int shiftLength = d_theoryBitvector->getFixedRightShiftParam(x);
  Expr output;
  if(bvLength > i && i > bvLength-shiftLength-1)
    output = d_theoryBitvector->falseExpr();
  else 
    output = 
      d_theoryBitvector->newBoolExtractExpr(x[0], i);

  Proof pf;
  if(withProof()) 
    pf = newPf("bit_extract_bitwiseFixedRightShift", x,rat(i));
  const Theorem result = newRWTheorem(bitExtract, output, Assumptions::emptyAssump(), pf); 
  TRACE("bitvector",
	"output of bitExtractFixedRightShift(", result, ")");
  return result;
}

//! Check that all the kids of e are BVCONST
static bool constantKids(const Expr& e) {
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)
    if(i->getOpKind() != BVCONST) return false;
  return true;
}


//! c1=c2 <=> TRUE/FALSE (equality of constant bitvectors)
Theorem BitvectorTheoremProducer::eqConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.isEq(),
		"BitvectorTheoremProducer::eqConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::eqConst: e = "+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("bitvector_eq_const", e);
  Expr res((e[0]==e[1])? d_theoryBitvector->trueExpr() :
                         d_theoryBitvector->falseExpr());
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! |- c1=c2 ==> |- AND(c1[i:i] = c2[i:i]) - expanding equalities into bits
Theorem BitvectorTheoremProducer::eqToBits(const Theorem& eq) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(eq.isRewrite(),
		"BitvectorTheoremProducer::eqToBits: eq = "+eq.toString());
  }

  const Expr& lhs = eq.getLHS();
  const Expr& rhs = eq.getRHS();
  
  if(CHECK_PROOFS) {
    CHECK_SOUND(d_theoryBitvector->getBaseType(lhs).getExpr().getOpKind() == BITVECTOR,
		"BitvectorTheoremProducer::eqToBits: eq = "+eq.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(lhs)
		== d_theoryBitvector->BVSize(rhs),
		"BitvectorTheoremProducer::eqToBits: eq = "+eq.toString());
  }

  int i=0, size=d_theoryBitvector->BVSize(lhs);
  vector<Expr> bitEqs;
  for(; i<size; i++) {
    Expr l = d_theoryBitvector->newBVExtractExpr(lhs, i, i);
    Expr r = d_theoryBitvector->newBVExtractExpr(rhs, i, i);
    bitEqs.push_back(l.eqExpr(r));
  }
  Expr res = andExpr(bitEqs);
  Proof pf;
  if(withProof())
    pf = newPf("eq_to_bits", eq.getExpr(), eq.getProof());
  return newTheorem(res, eq.getAssumptionsRef(), pf);
}


//! t<<n = c @ 0bin00...00, takes e == (t<<n)
Theorem BitvectorTheoremProducer::leftShiftToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == LEFTSHIFT && e.arity() == 1,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedLeftShiftParam(e) >= 0,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  Expr res(e0);
  int shiftSize=d_theoryBitvector->getFixedLeftShiftParam(e);

  if (shiftSize != 0) {
    Expr padding = d_theoryBitvector->newBVConstExpr(Rational(0), shiftSize);
    res = d_theoryBitvector->newConcatExpr(e0, padding);
  }

  Proof pf;
  if(withProof())
    pf = newPf("leftshift_to_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! t<<n = c @ 0bin00...00, takes e == (t<<n)
Theorem BitvectorTheoremProducer::constWidthLeftShiftToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == CONST_WIDTH_LEFTSHIFT && e.arity() == 1,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedLeftShiftParam(e) >= 0,
		"BitvectorTheoremProducer::leftShiftConst: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  Expr res;

  int shiftSize=d_theoryBitvector->getFixedLeftShiftParam(e);
  if (shiftSize == 0)
    res = e0;
  else {
    int bvLength = d_theoryBitvector->BVSize(e);
    if (shiftSize >= bvLength)
      res = d_theoryBitvector->newBVConstExpr(Rational(0), bvLength);
    else {
      Expr padding = d_theoryBitvector->newBVConstExpr(Rational(0), shiftSize);
      res = d_theoryBitvector->newBVExtractExpr(e0, bvLength-shiftSize-1, 0);
      res = d_theoryBitvector->newConcatExpr(res, padding);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("constWidthLeftShift_to_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! t>>m = 0bin00...00 @ t[bvLength-1:m], takes e == (t>>n)
Theorem BitvectorTheoremProducer::rightShiftToConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == RIGHTSHIFT && e.arity() == 1,
		"BitvectorTheoremProducer::rightShiftConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getFixedRightShiftParam(e) >= 0,
		"BitvectorTheoremProducer::rightShiftConst: e = "+e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e[0]);

  int shiftSize=d_theoryBitvector->getFixedRightShiftParam(e);
  Expr padding = d_theoryBitvector->newBVZeroString(shiftSize);

  Expr output;
  if(shiftSize >= bvLength)
    output = d_theoryBitvector->newBVZeroString(bvLength);
  else {
    Expr out0 = 
      d_theoryBitvector->newBVExtractExpr(e[0],bvLength-1,shiftSize);
    output = 
      d_theoryBitvector->newConcatExpr(padding,out0);
  }

  DebugAssert(bvLength == d_theoryBitvector->BVSize(output),
	      "BitvectorTheoremProducer::rightShiftConst: e = "+e.toString());

  Proof pf;
  if(withProof())
    pf = newPf("rightshift_to_concat", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteXOR(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVXOR && e.arity() == 2,
                "Bad call to rewriteXOR");
  }
  Expr nege0 = d_theoryBitvector->newBVNegExpr(e[0]);
  Expr nege1 = d_theoryBitvector->newBVNegExpr(e[1]);
  Expr or1 = d_theoryBitvector->newBVAndExpr(nege0, e[1]);
  Expr or2 = d_theoryBitvector->newBVAndExpr(e[0], nege1);

  Proof pf;
  if (withProof())
    pf = newPf("rewriteXOR", e);
  return newRWTheorem(e, d_theoryBitvector->newBVOrExpr(or1, or2),
                      Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteXNOR(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVXNOR && e.arity() == 2,
                "Bad call to rewriteXNOR");
  }
  Expr nege0 = d_theoryBitvector->newBVNegExpr(e[0]);
  Expr nege1 = d_theoryBitvector->newBVNegExpr(e[1]);
  Expr or1 = d_theoryBitvector->newBVAndExpr(nege0, nege1);
  Expr or2 = d_theoryBitvector->newBVAndExpr(e[0], e[1]);

  Proof pf;
  if (withProof())
    pf = newPf("rewriteXNOR", e);
  return newRWTheorem(e, d_theoryBitvector->newBVOrExpr(or1, or2),
                      Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteNAND(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVNAND && e.arity() == 2,
                "Bad call to rewriteNAND");
  }
  Expr andExpr = d_theoryBitvector->newBVAndExpr(e[0], e[1]);
  Proof pf;
  if (withProof())
    pf = newPf("rewriteNAND", e);
  return newRWTheorem(e, d_theoryBitvector->newBVNegExpr(andExpr),
                      Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteNOR(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVNOR && e.arity() == 2,
                "Bad call to rewriteNOR");
  }
  Expr orExpr = d_theoryBitvector->newBVOrExpr(e[0], e[1]);
  Proof pf;
  if (withProof())
    pf = newPf("rewriteNOR", e);
  return newRWTheorem(e, d_theoryBitvector->newBVNegExpr(orExpr),
                      Assumptions::emptyAssump(), pf);
}


Theorem BitvectorTheoremProducer::rewriteBVSub(const Expr& e)
{
  if (CHECK_PROOFS) {
    CHECK_SOUND(e.getKind() == BVSUB && e.arity() == 2 &&
                d_theoryBitvector->BVSize(e[0]) ==
                d_theoryBitvector->BVSize(e[1]),
                "Bad call to rewriteBVSub");
  }
  int bvsize = d_theoryBitvector->BVSize(e[0]);
  vector<Expr> k;
  k.push_back(e[0]);
  k.push_back(d_theoryBitvector->newBVUminusExpr(e[1]));
  
  Proof pf;
  if (withProof())
    pf = newPf("rewriteBVSub", e);
  return newRWTheorem(e, d_theoryBitvector->newBVPlusExpr(bvsize, k),
                      Assumptions::emptyAssump(), pf);
}


//! k*t = BVPLUS(n, <sum of shifts of t>) -- translation of k*t to BVPLUS
/*! If k = 2^m, return k*t = t@0...0 */
Theorem BitvectorTheoremProducer::constMultToPlus(const Expr& e) {
  DebugAssert(false,
	      "BitvectorTheoremProducer::constMultToPlus: this rule does not work\n");
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT && e.arity() == 2
		&& e[0].isRational() && e[0].getRational().isInteger(),
		"BitvectorTheoremProducer::constMultToPlus:\n e = "
		+e.toString());
  }

  Rational k = e[0].getRational();
  const Expr& t = e[1];
  int resLength = d_theoryBitvector->BVSize(e);
  string coeffBinary = abs(k).toString(2);
  int len = coeffBinary.length();
  Expr res; // The resulting expression
  if(k == 0) {
    // Construct n-bit vector of 0's
    vector<bool> bits;
    int len = resLength;
    for(int i=0; i<len; ++i) bits.push_back(false);
    res = d_theoryBitvector->newBVConstExpr(bits);
  } else {
    // Construct the vector of shifts, the kids of the resulting BVPLUS
    vector<Expr> kids;
    for(int i=0; i<len; ++i) {
      if(coeffBinary[i] == '1')
	kids.push_back(d_theoryBitvector->newFixedLeftShiftExpr(t, (len-1)-i));
    }
    res = (kids.size() == 1)? kids[0]
      : d_theoryBitvector->newBVPlusExpr(resLength, kids);
    // For negative k, compute (~res+1), the 2's complement
    if(k < 0) {
      vector<Expr> kk;
      kk.push_back(d_theoryBitvector->newBVNegExpr(res));
      kk.push_back(rat(1));
      res = d_theoryBitvector->newBVPlusExpr(resLength, kk);
    }
  }

  Proof pf;
  if(withProof())
    pf = newPf("const_mult_to_plus", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


Theorem
BitvectorTheoremProducer::bvplusZeroConcatRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind()==CONCAT && e.arity()==2,
		"BitvectorTheoremProducer::bvplusZeroConcatRule: e = "
		+e.toString());
    CHECK_SOUND(e[0].getKind()==BVCONST && e[1].getOpKind()==BVPLUS
		&& d_theoryBitvector->computeBVConst(e[0])==0,
		"BitvectorTheoremProducer::bvplusZeroConcatRule: e = "
		+e.toString());
  }

  int constSize = d_theoryBitvector->BVSize(e[0]);
  const Expr& bvplus = e[1];
  int bvplusSize = d_theoryBitvector->getBVPlusParam(bvplus);

  // Check if we can apply the rewrite rule
  int maxKidSize(0);
  for(Expr::iterator i=bvplus.begin(), iend=bvplus.end(); i!=iend; ++i) {
    int size(d_theoryBitvector->BVSize(*i));
    // if kid is 0bin0 @ ..., then we can shorten its effective size
    if(i->getOpKind()==CONCAT && i->arity()>=2
       && (*i)[0].getKind()==BVCONST && d_theoryBitvector->computeBVConst((*i)[0])==0)
      size -= d_theoryBitvector->BVSize((*i)[0]);
    if(size > maxKidSize) maxKidSize = size;
  }
  int numKids = bvplus.arity();
  // Compute ceiling of log2(numKids)
  int log2 = 0;
  for(int i=1; i < numKids; i *=2, log2++);
  if(log2+maxKidSize > bvplusSize) {
    // Skip the rewrite, it's potentially unsound
    TRACE("bv 0@+", "bvplusZeroConcatRule(", e, "): skipped");
    return d_theoryBitvector->reflexivityRule(e);
  }
  
  Expr res(d_theoryBitvector->newBVPlusExpr(bvplusSize+constSize,
					    bvplus.getKids()));

  Proof pf;
  if(withProof())
    pf = newPf("bvplus_zero_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}



//! c1[i:j] = c  (extraction from a constant bitvector)
Theorem BitvectorTheoremProducer::extractConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND((unsigned)hi < d_theoryBitvector->getBVConstSize(e0),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }
  vector<bool> res;

  for(int bit=low; bit <= hi; bit++)
    res.push_back(d_theoryBitvector->getBVConstValue(e0, bit));

  Proof pf;
  if(withProof())
    pf = newPf("extract_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}

// t[n-1:0] = t  for n-bit t
Theorem
BitvectorTheoremProducer::extractWhole(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractWhole: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    CHECK_SOUND(low ==0 && hi == d_theoryBitvector->BVSize(e0) - 1,
		"BitvectorTheoremProducer::extractWhole: e = "+e.toString()
		+"\n BVSize(e) = "+ int2string(d_theoryBitvector->BVSize(e0)));
  }
  Proof pf;
  if(withProof())
    pf = newPf("extract_whole", e);
  return newRWTheorem(e, e0, Assumptions::emptyAssump(), pf);
}


//! t[i:j][k:l] = t[k+j:l+j]  (eliminate double extraction)
Theorem
BitvectorTheoremProducer::extractExtract(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractExtract: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    // Check the bounds
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::extractExtract: e = "+e.toString());
    // The base expression must also be EXTRACT
    CHECK_SOUND(e0.getOpKind() == EXTRACT && e0.arity() == 1,
		"BitvectorTheoremProducer::extractExtract: e0 = "
		+e0.toString());
  }

  int hi0 = d_theoryBitvector->getExtractHi(e0);
  int low0 = d_theoryBitvector->getExtractLow(e0);
  const Expr& e00 = e0[0];

  if(CHECK_PROOFS) {
    // The extractions must be within the correct bounds
    CHECK_SOUND((0 <= low) && (low <= hi) && (hi <= hi0-low0),
		"BitvectorTheoremProducer::extractExtract:\n"
		" [hi:low][hi0:low0] = ["+ int2string(hi0)+":"+ int2string(low0)
		+"]["+ int2string(hi) + ":" + int2string(low)
		+"]\n e = "+e.toString());
  }

  Expr res = d_theoryBitvector->newBVExtractExpr(e00, hi+low0, low+low0);

  Proof pf;
  if(withProof())
    pf = newPf("extract_extract", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! (t1 @ t2)[i:j] = t1[...] @ t2[...]  (push extraction through concat)
Theorem
BitvectorTheoremProducer::extractConcat(const Expr& e) {
  TRACE("bitvector rules", "extractConcat(", e, ") {");
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::extractConcat: e = "+e.toString());
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    // Check the bounds
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::extractConcat: e = "+e.toString());
    CHECK_SOUND(hi < d_theoryBitvector->BVSize(e0),
		"BitvectorTheoremProducer::extractConcat: e = "+e.toString()
		+"\n BVSize(e0) = "+ int2string(d_theoryBitvector->BVSize(e0)));
    // The base expression  must be CONCAT
    CHECK_SOUND(e0.getOpKind() == CONCAT,
		"BitvectorTheoremProducer::extractConcat: e0 = "
		+e0.toString());
  }
  // Collect the relevant kids from concatenation
  vector<Expr> kids;
  int width(d_theoryBitvector->BVSize(e0));
  TRACE("bitvector rules", "extractConcat: width=", width, "");
  for(Expr::iterator i=e0.begin(), iend=e0.end(); i!=iend && width>low; ++i) {
    TRACE("bitvector rules", "extractConcat: *i=", *i, "");
    int w(d_theoryBitvector->BVSize(*i));
    int newWidth = width-w;
    int l(0), h(0);
    TRACE("bitvector rules", "extractConcat: w=", w, "");
    TRACE("bitvector rules", "extractConcat: newWidth=", newWidth, "");
    if(width > hi) { // Previous kids were outside of extract window
      if(hi >= newWidth) { // The first relevant kid
	h = hi-newWidth;
	l = (newWidth <= low)? low-newWidth : 0;
	TRACE("bitvector rules", "extractConcat[newWidth<=hi<width]: h=",
	      h, ", l="+ int2string(l));
	kids.push_back(d_theoryBitvector->newBVExtractExpr(*i, h, l));
      }
    } else if(width > low) {
      // High end of the current kid is in the extract window
      h = w-1;
      l = (newWidth <= low)? low-newWidth : 0;
      TRACE("bitvector rules", "extractConcat[low<width<=hi]: h=",
	    h, ", l="+ int2string(l));
      kids.push_back(d_theoryBitvector->newBVExtractExpr(*i, h, l));
    } // The remaining kids are outside of extract window, skip them
    width=newWidth;
    TRACE("bitvector rules", "extractConcat: width=", width, "");
  }
  Expr res = (kids.size()==1)? kids[0]
    : d_theoryBitvector->newConcatExpr(kids);
  Proof pf;
  if(withProof())
    pf = newPf("extract_concat", e);
  Theorem thm(newRWTheorem(e, res, Assumptions::emptyAssump(), pf));
  TRACE("bitvector rules", "extractConcat => ", thm.getExpr(), " }");
  return thm;
}


// (t1 op t2)[i:j] = t1[i:j] op t2[i:j] -- push extraction through
// bit-wise operator
Theorem
BitvectorTheoremProducer::extractBitwise(const Expr& e, int kind,
					 const string& pfName) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity() == 1,
		"BitvectorTheoremProducer::"+pfName+": e = "+e.toString());
    CHECK_SOUND(kind == BVAND || kind == BVOR || 
		kind == BVNEG || kind == BVXOR || 
		kind == BVXNOR,
		"BitvectorTheoremProducer::"+pfName+": kind = "
		+d_theoryBitvector->getEM()->getKindName(kind));
  }

  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  const Expr& e0 = e[0];

  if(CHECK_PROOFS) {
    // Check the bounds
    CHECK_SOUND(0 <= low && low <= hi,
		"BitvectorTheoremProducer::"+pfName+": e = "+e.toString());
    // The base expression must also be EXTRACT
    CHECK_SOUND(e0.getOpKind() == kind,
		"BitvectorTheoremProducer::"+pfName+": e0 = "
		+e0.toString());
  }

  vector<Expr> kids;
  for(Expr::iterator i=e0.begin(), iend=e0.end(); i!=iend; ++i) {
    kids.push_back(d_theoryBitvector->newBVExtractExpr(*i, hi, low));
  }
  Expr res = Expr(e0.getOp(), kids);
  Proof pf;
  if(withProof())
    pf = newPf(pfName, e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! (t1 & t2)[i:j] = t1[i:j] & t2[i:j]  (push extraction through OR)
Theorem
BitvectorTheoremProducer::extractAnd(const Expr& e) {
  return extractBitwise(e, BVAND, "extract_and");
}


//! (t1 | t2)[i:j] = t1[i:j] | t2[i:j]  (push extraction through AND)
Theorem
BitvectorTheoremProducer::extractOr(const Expr& e) {
  return extractBitwise(e, BVOR, "extract_or");
}


//! (~t)[i:j] = ~(t[i:j]) (push extraction through NEG)
Theorem
BitvectorTheoremProducer::extractNeg(const Expr& e) {
  return extractBitwise(e, BVNEG, "extract_neg");
}

//! ite(c,t1,t2)[i:j] <=> ite(c,t1[i:j],t2[i:j])
Theorem
BitvectorTheoremProducer::iteExtractRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e.arity()==1,
		"BitvectorTheoremProducer::iteExtractRule: "
		"input must be an bitvector EXTRACT expr:\n"+
		e.toString());
  }
  int hi = d_theoryBitvector->getExtractHi(e);
  int low = d_theoryBitvector->getExtractLow(e);
  
  if(CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == ITE && 
		e[0].arity()==3 &&
		BITVECTOR == e[0].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::iteExtractRule: "
		"input must be an bitvector EXTRACT expr over an ITE:\n" +
		e.toString());
    CHECK_SOUND(hi >= low && d_theoryBitvector->BVSize(e[0]) >= hi-low, 
		"BitvectorTheoremProducer::iteExtractRule: " 
		"i should be greater than j in e[i:j] = "
		+e.toString());
  }
  const Expr ite = e[0];
  Expr cond = ite[0];
  Expr e1 = d_theoryBitvector->newBVExtractExpr(ite[1],hi,low);
  Expr e2 = d_theoryBitvector->newBVExtractExpr(ite[2],hi,low);
  Expr output = Expr(CVC3::ITE,cond,e1,e2);

  Proof pf;
  if(withProof())
    pf = newPf("ite_extract_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! ~ite(c,t1,t2) <=> ite(c,~t1,~t2)
Theorem
BitvectorTheoremProducer::iteBVnegRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity()==1,
		"BitvectorTheoremProducer::itebvnegrule: "
		"input must be an bitvector EXTRACT expr:\n"+
		e.toString());
  }
  if(CHECK_PROOFS) {
    CHECK_SOUND(e[0].getKind() == ITE && 
		e[0].arity()==3 &&
		BITVECTOR == e[0].getType().getExpr().getOpKind(),
		"BitvectorTheoremProducer::itebvnegrule: "
		"input must be an bitvector EXTRACT expr over an ITE:\n" +
		e.toString());
  }
  const Expr ite = e[0];
  Expr cond = ite[0];
  Expr e1 = d_theoryBitvector->newBVNegExpr(ite[1]);
  Expr e2 = d_theoryBitvector->newBVNegExpr(ite[2]);
  Expr output = Expr(CVC3::ITE,cond,e1,e2);

  Proof pf;
  if(withProof())
    pf = newPf("ite_bvneg_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! ~c1 = c  (bit-wise negation of a constant bitvector)
Theorem BitvectorTheoremProducer::negConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::negConst: e = "+e.toString());
  }
  const Expr& e0 = e[0];
  vector<bool> res;

  for(int bit=0, size=d_theoryBitvector->getBVConstSize(e0); bit<size; bit++)
    res.push_back(!d_theoryBitvector->getBVConstValue(e0, bit));

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}


//! ~(t1@...@tn) = (~t1)@...@(~tn) -- push negation through concat
Theorem
BitvectorTheoremProducer::negConcat(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negConcat: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == CONCAT,
		"BitvectorTheoremProducer::negConcat: e = "+e.toString());
  }

  const Expr& e0 = e[0];

  vector<Expr> kids;
  for(Expr::iterator i=e0.begin(), iend=e0.end(); i!=iend; ++i)
    kids.push_back(d_theoryBitvector->newBVNegExpr(*i));

  Expr res = d_theoryBitvector->newConcatExpr(kids);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_concat", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

//! ~(~t) = t  -- eliminate double negation
Theorem
BitvectorTheoremProducer::negNeg(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negNeg: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVNEG && e[0].arity() == 1,
		"BitvectorTheoremProducer::negNeg: e = "+e.toString());
  }

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_neg", e);
  return newRWTheorem(e, e[0][0], Assumptions::emptyAssump(), pf);
}

//! ~(t1 & t2) = ~t1 | ~t2  -- DeMorgan's Laws
Theorem
BitvectorTheoremProducer::negBVand(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negBVand: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVAND,
		"BitvectorTheoremProducer::negBVand: e = "+e.toString());
  }
  Expr output;
  std::vector<Expr> negated;
  for(Expr::iterator i = e[0].begin(),iend=e[0].end();i!=iend;++i)
    negated.push_back(d_theoryBitvector->newBVNegExpr(*i));
  output = d_theoryBitvector->newBVOrExpr(negated);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_and", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! ~(t1 | t2) = ~t1 & ~t2  -- DeMorgan's Laws
Theorem
BitvectorTheoremProducer::negBVor(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1,
		"BitvectorTheoremProducer::negBVor: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVOR,
		"BitvectorTheoremProducer::negBVor: e = "+e.toString());
  }

  Expr output;
  std::vector<Expr> negated;
  for(Expr::iterator i = e[0].begin(),iend=e[0].end();i!=iend;++i)
    negated.push_back(d_theoryBitvector->newBVNegExpr(*i));
  output = d_theoryBitvector->newBVAndExpr(negated);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_or", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! ~(t1 xor t2) = ~t1 xor t2
Theorem
BitvectorTheoremProducer::negBVxor(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1 && e[0].arity() > 0,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVXOR,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
  }

  Expr output;
  std::vector<Expr> children;
  Expr::iterator i = e[0].begin(), iend = e[0].end();
  children.push_back(d_theoryBitvector->newBVNegExpr(*i));
  ++i;
  for(; i!=iend; ++i)
    children.push_back(*i);
  output = d_theoryBitvector->newBVXorExpr(children);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_xor", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! ~(t1 xnor t2) = t1 xor t2
Theorem
BitvectorTheoremProducer::negBVxnor(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVNEG && e.arity() == 1 && e[0].arity() > 0,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
    CHECK_SOUND(e[0].getOpKind() == BVXNOR,
		"BitvectorTheoremProducer::negBVxor: e = "+e.toString());
  }

  Expr t2 = e[0][1];
  if (e[0].arity() > 2) {
    std::vector<Expr> children;
    Expr::iterator i = e[0].begin(), iend = e[0].end();
    ++i;
    for(; i!=iend; ++i)
      children.push_back(*i);
    t2 = d_theoryBitvector->newBVXnorExpr(children);
  }
  Expr output = d_theoryBitvector->newBVXorExpr(e[0][0], t2);

  Proof pf;
  if(withProof())
    pf = newPf("bitneg_xnor", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}


//! c1&c2 = c  (bit-wise AND constant bitvectors)
//! c1 op c2 = c  -- bit-wise AND and OR of constant bitvectors
Theorem BitvectorTheoremProducer::bitwiseConst(const Expr& e,
					       const std::vector<int>& idxs,
					       bool isAnd) {
  string funName(isAnd? "andConst" : "orConst");
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == (isAnd ? BVAND : BVOR),
		"BitvectorTheoremProducer::"+funName+": e = "+e.toString());
    CHECK_SOUND(idxs.size() >= 2, "BitvectorTheoremProducer::"+funName
		+"():\n e = "+e.toString());
    for(size_t i=0; i<idxs.size(); ++i) {
      CHECK_SOUND(idxs[i] < e.arity(),
		  "BitvectorTheoremProducer::"+funName+": idxs["
		  +int2string(i)+"]="+int2string(idxs[i])
		  +", e.arity() = "+int2string(e.arity())
		  +"\n e = "+e.toString());
      CHECK_SOUND(e[idxs[i]].getKind() == BVCONST,
		  "BitvectorTheoremProducer::"+funName+": e = "+e.toString());
    }
  }
  vector<bool> bits;
  // Initialize 'bits' with all 1's or 0's, depending on isAnd value
  int size = d_theoryBitvector->BVSize(e);
  for(int bit=0; bit<size; bit++)
    bits.push_back(isAnd);

  vector<Expr> kids(1); // Reserve the first element for the constant bitvector
  size_t ii(0); // The next index of idxs to match
  int idx(idxs[0]); // The index of the next constant (for efficiency)
  for(int i=0, iend=e.arity(); i<iend; ++i) {
    const Expr& ei = e[i];
    if(i == idx) {
      if(CHECK_PROOFS) {
	CHECK_SOUND(ei.getKind() == BVCONST,
		    "BitvectorTheoremProducer::"+funName+": e["
		    +int2string(i)+"] = "+ei.toString());
	CHECK_SOUND(d_theoryBitvector->getBVConstSize(ei) == (unsigned)size,
		    "BitvectorTheoremProducer::"+funName+": e["
		    +int2string(i)+"] = "+ei.toString());
      }
      // "AND" in the constant bitvector
      for(int bit=0; bit<size; bit++)
	bits[bit] = isAnd ?
          (bits[bit] && d_theoryBitvector->getBVConstValue(ei, bit))
	  : (bits[bit] || d_theoryBitvector->getBVConstValue(ei, bit));
      // Advance the index of idxs
      if(ii < idxs.size())
	idx = idxs[++ii];
      else
	idx = e.arity();
    }
    else // Not a constant, add to the list of kids
      kids.push_back(ei);
  }
  // Create the new constant bitvector and make it the first kid
  kids[0] = d_theoryBitvector->newBVConstExpr(bits);
  // Contruct the final expression.
  Expr res = (kids.size() == 1)? kids[0]
    : isAnd? d_theoryBitvector->newBVAndExpr(kids)
    : d_theoryBitvector->newBVOrExpr(kids);

  Proof pf;
  if(withProof()) {
    // Construct a list of indices as a RAW_LIST Expr
    vector<Expr> indices;
    for(size_t i=0, iend=idxs.size(); i<iend; ++i)
      indices.push_back(rat(idxs[i]));
    pf = newPf(isAnd? "bitand_const" : "bitor_const",
	       e, Expr(RAW_LIST, indices));
  }
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! ... & (t1@...@tk) & ... = (...& t1 &...)@...@(...& tk &...)
/*!
 * Lifts concatenation to the top of bit-wise AND.  Takes the
 * bit-wise AND expression 'e' and the index 'i' of the
 * concatenation.
 */
Theorem
BitvectorTheoremProducer::bitwiseConcat(const Expr& e, int idx, bool isAnd) {
  string funName(isAnd? "andConcat" : "orConcat");
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == (isAnd ? BVAND : BVOR),
		"BitvectorTheoremProducer::"+funName+": e = "+e.toString());
    CHECK_SOUND(idx < e.arity(),
		"BitvectorTheoremProducer::"+funName+": e = "+e.toString()
		+"\n idx = "+int2string(idx)
		+"\n e.arity() = "+int2string(e.arity()));
    CHECK_SOUND(e[idx].getOpKind() == CONCAT && e[idx].arity() > 0,
		"BitvectorTheoremProducer::"+funName+": e["+int2string(idx)
		+"] = "+e[idx].toString());
  }

  int arity = e.arity();
  const Expr& ei = e[idx];

  // Build the top-level concatenation
  vector<Expr> concatKids;
  // Current extraction window
  int hi=d_theoryBitvector->BVSize(e)-1;
  int low=hi-d_theoryBitvector->BVSize(ei[0])+1;

  for(int i=0, iend=ei.arity(); i<iend; ++i) {
    // Kids of the current BVAND / BVOR
    vector<Expr> kids;
    for(int j=0; j<arity; ++j) {
      if(j==idx)
	kids.push_back(ei[i]);
      else
	kids.push_back(d_theoryBitvector->newBVExtractExpr(e[j], hi, low));
    }
    if(isAnd)
      concatKids.push_back(d_theoryBitvector->newBVAndExpr(kids));
    else
      concatKids.push_back(d_theoryBitvector->newBVOrExpr(kids));
    if(i+1<iend) {
      int newHi = low-1;
      low = low - d_theoryBitvector->BVSize(ei[i+1]);
      hi = newHi;
    }
  }
  Expr res = d_theoryBitvector->newConcatExpr(concatKids);
  Proof pf;
  if(withProof())
    pf = newPf(isAnd? "bitand_concat" : "bitor_concat", e, rat(idx));
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


Theorem
BitvectorTheoremProducer::bitwiseFlatten(const Expr& e, bool isAnd) {
  string funName(isAnd? "andFlatten" : "orFlatten");
  int kind = isAnd? BVAND : BVOR;

  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == kind && e.arity()>=2,
		"BitvectorTheoremProducer::"+funName+": e = "+e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e);
  Expr output;
  int flag = 0;

  // flatten the nested ops
  std::vector<Expr> flattenkids;
  for(Expr::iterator i = e.begin(),iend=e.end();i!=iend; ++i) {
    if(i->getOpKind() == kind)
      flattenkids.insert(flattenkids.end(),
			 i->getKids().begin(),i->getKids().end());
    else
      flattenkids.push_back(*i);
  }

  // drop duplicate subterms and detect conflicts like t, ~t
  std::vector<Expr> outputkids;
  ExprMap<int> likeTerms;
  std::vector<Expr>::iterator j = flattenkids.begin();
  std::vector<Expr>::iterator jend = flattenkids.end();
  for(;j!=jend; ++j) {
    //check if *j is duplicated or its negation already occured
    flag = sameKidCheck(*j, likeTerms);
    switch(flag) {
    case 0: 
      //no duplicates
      outputkids.push_back(*j);
      break;
    case 1: 
      //duplicate detected. ignore the duplicate
      break;
    case -1:{
      //conflict detected
      if(isAnd)
	output = d_theoryBitvector->newBVZeroString(bvLength);
      else
	output = d_theoryBitvector->newBVOneString(bvLength);
      break;
    }
    default:
      DebugAssert(false,
		  "control should not reach here");
      break;
    }
    if(-1 == flag)
      break;
  }
  
  if(flag != -1) {
    DebugAssert(outputkids.size()>0,
		"TheoryBitvector::bitwiseFlatten: fatal error");
    // Sort the kids according to operator<(Expr, Expr)
    if(CHECK_PROOFS)
      CHECK_SOUND(outputkids.size() > 0,
		  "TheoryBitvector:bitwiseFlatten: fatal error");
    sort(outputkids.begin(), outputkids.end());
    if(outputkids.size() >= 2)
      output = Expr(e.getOp(), outputkids);
    else
      output = *(outputkids.begin());//iterator is cheaper than [0]      
  }

  Proof pf;
  if(withProof())
    pf = newPf(isAnd? "bitand_flatten" : "bitor_flatten", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

//! c1&c2 = c  (bit-wise AND constant bitvectors)
Theorem BitvectorTheoremProducer::andConst(const Expr& e,
					   const std::vector<int>& idxs) {
  return bitwiseConst(e, idxs, true);
}

// 0bin0...0 & t = 0bin0...0  -- bit-wise AND with zero bitvector
/* \param e is the bit-wise AND expr
 *  \param idx is the index of the zero bitvector
 */
Theorem
BitvectorTheoremProducer::andZero(const Expr& e, int idx) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVAND,
		"BitvectorTheoremProducer::andZero: e = "+e.toString());
    CHECK_SOUND(idx < e.arity(),
		"BitvectorTheoremProducer::andZero: e = "+e.toString()
		+"\n idx = "+int2string(idx)
		+"\n e.arity() = "+int2string(e.arity()));
    CHECK_SOUND(e[idx].getKind() == BVCONST && 
		0 == d_theoryBitvector->computeBVConst(e[idx]),
		"BitvectorTheoremProducer::andZero: e["+int2string(idx)
		+"] = "+e[idx].toString());
  }

  Proof pf;
  if(withProof())
    pf = newPf("bitand_zero", e, rat(idx));
  return newRWTheorem(e, e[idx], Assumptions::emptyAssump(), pf);
}


Theorem
BitvectorTheoremProducer::andOne(const Expr& e, const vector<int> idxs) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVAND,
		"BitvectorTheoremProducer::andOne: e = "+e.toString());
    CHECK_SOUND(idxs.size() > 0,
		"BitvectorTheoremProducer::andOne: e = "+e.toString());
    int lastIdx(-1);
    for(vector<int>::const_iterator i=idxs.begin(), iend=idxs.end();
	i!=iend; ++i) {
      CHECK_SOUND(lastIdx < (*i) && (*i) < e.arity(),
		"BitvectorTheoremProducer::andOne: e = "+e.toString()
		+"\n lastIdx = "+int2string(lastIdx)
		+"\n *i = "+int2string(*i)
		+"\n e.arity() = "+int2string(e.arity()));
      lastIdx=(*i);
      const Expr& ei = e[*i];
      CHECK_SOUND(ei.getKind() == BVCONST,
		  "BitvectorTheoremProducer::andOne: e["+int2string(*i)
		  +"] = "+ei.toString());

      for(int j=0,jend=(int)d_theoryBitvector->getBVConstSize(ei); j<jend; ++j)
	CHECK_SOUND(d_theoryBitvector->getBVConstValue(ei, j),
		    "BitvectorTheoremProducer::andOne: e["+int2string(j)
		    +"] = "+ei.toString());
    }
  }
  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    es.push_back(e);
    for(vector<int>::const_iterator i=idxs.begin(), iend=idxs.end();
	i!=iend; ++i)
      es.push_back(rat(*i));
    pf=newPf("bitand_one", es);
  }

  vector<Expr> kids;
  size_t idx(0);
  for (int i=0; i<e.arity(); ++i) {
    if (idx < idxs.size() && i == idxs[idx]) idx++;
    else kids.push_back(e[i]);
  }
  Expr res;
  if(kids.size()>=2) res = Expr(e.getOp(), kids);
  else if(kids.size()==1) res = kids[0];
  else res = e[0]; // All kids are const bitvectors of 1's
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}


//! ... & (t1@...@tk) & ... = (...& t1 &...)@...@(...& tk &...)
/*!
 * Lifts concatenation to the top of bit-wise AND.  Takes the
 * bit-wise AND expression 'e' and the index 'i' of the
 * concatenation.
 */
Theorem
BitvectorTheoremProducer::andConcat(const Expr& e, int idx) {
  return bitwiseConcat(e, idx, true);
}


//! (t1 & (t2 & t3) & t4) = t1 & t2 & t3 & t4  -- flatten bit-wise AND
/*! Also reorders the terms according to a fixed total ordering */
Theorem
BitvectorTheoremProducer::andFlatten(const Expr& e) {
  return bitwiseFlatten(e, true);
}



//! c1|c2 = c  (bit-wise OR of constant bitvectors)
Theorem BitvectorTheoremProducer::orConst(const Expr& e,
					  const std::vector<int>& idxs) {
  return bitwiseConst(e, idxs, false);
}


//! 0bin1...1 | t = 0bin1...1  -- bit-wise OR with bitvector of 1's
/*! \param e is the bit-wise OR expr
 *  \param idx is the index of the bitvector of 1's
 */
Theorem
BitvectorTheoremProducer::orOne(const Expr& e, int idx) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVOR,
		"BitvectorTheoremProducer::orOne: e = "+e.toString());
    CHECK_SOUND(idx < e.arity(),
		"BitvectorTheoremProducer::orOne: e = "+e.toString()
		+"\n idx = "+int2string(idx)
		+"\n e.arity() = "+int2string(e.arity()));
    CHECK_SOUND(e[idx].getKind() == BVCONST,
		"BitvectorTheoremProducer::orOne: e["+int2string(idx)
		+"] = "+e[idx].toString());
  }

  const Expr& ei = e[idx];

  if(CHECK_PROOFS) {
    for(int i=0, iend=d_theoryBitvector->getBVConstSize(ei); i<iend; ++i)
      CHECK_SOUND(d_theoryBitvector->getBVConstValue(ei,i),
		"BitvectorTheoremProducer::orOne: e["+int2string(idx)
		+"] = "+ei.toString());
  }

  Proof pf;
  if(withProof())
    pf = newPf("bitand_zero", e, rat(idx));
  return newRWTheorem(e, e[idx], Assumptions::emptyAssump(), pf);
}


Theorem
BitvectorTheoremProducer::orZero(const Expr& e, const vector<int> idxs) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVOR,
		"BitvectorTheoremProducer::orZero: e = "+e.toString());
    CHECK_SOUND(idxs.size() > 0,
		"BitvectorTheoremProducer::orZero: e = "+e.toString());
    int lastIdx(-1);
    for(vector<int>::const_iterator i=idxs.begin(), iend=idxs.end();
	i!=iend; ++i) {
      CHECK_SOUND(lastIdx < (*i) && (*i) < e.arity(),
		"BitvectorTheoremProducer::orZero: e = "+e.toString()
		+"\n lastIdx = "+int2string(lastIdx)
		+"\n *i = "+int2string(*i)
		+"\n e.arity() = "+int2string(e.arity()));
      lastIdx=(*i);
      const Expr& ei = e[*i];
      CHECK_SOUND(ei.getKind() == BVCONST &&
		  d_theoryBitvector->computeBVConst(ei)==0,
		  "BitvectorTheoremProducer::orZero: e["+int2string(*i)
		  +"] = "+ei.toString());
    }
  }
  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    es.push_back(e);
    for(vector<int>::const_iterator i=idxs.begin(), iend=idxs.end();
	i!=iend; ++i)
      es.push_back(rat(*i));
    pf=newPf("bitor_zero", es);
  }

  vector<Expr> kids;
  size_t idx(0);
  for(int i=0; i<e.arity(); ++i) {
    if (idx < idxs.size() && i == idxs[idx]) idx++;
    else kids.push_back(e[i]);
  }
  Expr res;
  if(kids.size()>=2) res = Expr(e.getOp(), kids);
  else if(kids.size()==1) res = kids[0];
  else res = e[0]; // All kids are const bitvectors of 0's
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}

/*! checks if e is already present in likeTerms without conflicts. 
 *  if yes return 1, else{ if conflict return -1 else return 0 }
 *  we have conflict if 
 *          1. the kind of e is BVNEG, 
 *                 and e[0] is already present in likeTerms
 *          2. ~e is present in likeTerms already
 */
int BitvectorTheoremProducer::sameKidCheck(const Expr&  e, 
					   ExprMap<int>& likeTerms) {  
  //initially flag = 0, i.e. we assume e is not in likeTerms
  int flag = 0;
  
  //look for e
  ExprMap<int>::iterator it = likeTerms.find(e);

  //no entry found for e
  if(it==likeTerms.end()) {
    switch(e.getOpKind()) {
     case BVNEG: {
       likeTerms[e] = 1;
       ExprMap<int>::iterator it0 = likeTerms.find(e[0]);
       if(it0!=likeTerms.end())
	 flag = -1;
       break;
     }
     default: {
       likeTerms[e] = 1;
       Expr bvNeg = d_theoryBitvector->newBVNegExpr(e);
       ExprMap<int>::iterator negIt = likeTerms.find(bvNeg);
       if(negIt!=likeTerms.end())
	 flag=-1;
       break;
     }
    }
    return flag;
  }

  //found an entry for e 
  flag = 1;
  switch(e.getOpKind()) {
   case BVNEG: {
     ExprMap<int>::iterator it0 = likeTerms.find(e[0]);
     if(it0!=likeTerms.end())
       flag = -1;
     break;
   }
   default: {
     Expr bvNeg = d_theoryBitvector->newBVNegExpr(e);
     ExprMap<int>::iterator negIt = likeTerms.find(bvNeg);
     if(negIt!=likeTerms.end())
       flag=-1;    
     break;
   }
  }
  return flag;
}

//! ... | (t1@...@tk) | ... = (...| t1 |...)@...@(...| tk |...)
/*!
 * Lifts concatenation to the top of bit-wise OR.  Takes the
 * bit-wise OR expression 'e' and the index 'i' of the
 * concatenation.
 */
Theorem
BitvectorTheoremProducer::orConcat(const Expr& e, int idx) {
  return bitwiseConcat(e, idx, false);
}


//! (t1 | (t2 | t3) | t4) = t1 | t2 | t3 | t4  -- flatten bit-wise OR
/*! Also reorders the terms according to a fixed total ordering */
Theorem
BitvectorTheoremProducer::orFlatten(const Expr& e) {
  return bitwiseFlatten(e, false);
}



//! c1@c2@...@cn = c  (concatenation of constant bitvectors)
Theorem BitvectorTheoremProducer::concatConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == CONCAT,
		"BitvectorTheoremProducer::concatConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::concatConst: e = "+e.toString());
  }
  vector<bool> res;
  for(int i=e.arity()-1; i >= 0; --i) {
    for(int bit=0, size=d_theoryBitvector->getBVConstSize(e[i]); bit < size; bit++)
      res.push_back(d_theoryBitvector->getBVConstValue(e[i], bit));
  }
  Proof pf;
  if(withProof())
    pf = newPf("concat_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}


//! Flatten one level of nested concatenation, e.g.: x@(y@z)@w = x@y@z@w
Theorem
BitvectorTheoremProducer::concatFlatten(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == CONCAT && e.arity() >= 2,
		"BitvectorTheoremProducer::concatFlatten: e = "+e.toString());
  }
  // Rebuild the expression: copy the kids and flatten the nested CONCATs
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    if(i->getOpKind() == CONCAT)
      kids.insert(kids.end(), i->getKids().begin(), i->getKids().end());
    else
      kids.push_back(*i);
  }
  Proof pf;
  if(withProof())
    pf = newPf("concat_flatten", e);
  return newRWTheorem(e, Expr(e.getOp(), kids), Assumptions::emptyAssump(), pf);
}


//! Merge n-ary concat. of adjacent extractions: x[15:8]@x[7:0] = x[15:0]
Theorem
BitvectorTheoremProducer::concatMergeExtract(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == CONCAT && e.arity() >= 2,
		"BitvectorTheoremProducer::concatMergeExtract: e = "
		+e.toString());
    CHECK_SOUND(e[0].getOpKind() == EXTRACT,
		"BitvectorTheoremProducer::concatMergeExtract: e = "
		+e.toString());
    CHECK_SOUND(d_theoryBitvector->getExtractHi(e[0]) >= d_theoryBitvector->getExtractLow(e[0]),
		"BitvectorTheoremProducer::concatMergeExtract: e = "
		+e.toString());
  }

  const Expr& base = e[0][0]; // The common base of all extractions

  if(CHECK_PROOFS) {
    // Check that all extractions have the same base and are contiguous
    int low = d_theoryBitvector->getExtractLow(e[0]);
    for(int i=1, iend=e.arity(); i<iend; ++i) {
      const Expr& ei = e[i];
      CHECK_SOUND(ei.getOpKind() == EXTRACT && ei[0] == base,
		  "BitvectorTheoremProducer::concatMergeExtract: e["
		  +int2string(i)+"] = "+ei.toString()
		  +"\n base = "+base.toString());
      CHECK_SOUND(d_theoryBitvector->getExtractHi(ei) >= d_theoryBitvector->getExtractLow(ei),
		  "BitvectorTheoremProducer::concatMergeExtract: e["
		  +int2string(i)+"] = "+e.toString());

      int newHi = d_theoryBitvector->getExtractHi(ei);
      
      CHECK_SOUND(0 <= newHi && newHi == low-1,
		  "BitvectorTheoremProducer::concatMergeExtract:\n e["
		  +int2string(i-1)+"] = "+e[i-1].toString()
		  +"\n e["+int2string(i)+"] = "+ei.toString());
      low = d_theoryBitvector->getExtractLow(ei);
    }
  }
  
  int hi = d_theoryBitvector->getExtractHi(e[0]);
  int low = d_theoryBitvector->getExtractLow(e[e.arity()-1]);
  Expr res = d_theoryBitvector->newBVExtractExpr(base, hi, low);

  Proof pf;
  if(withProof())
    pf = newPf("concat_merge_extract", e);
  return newRWTheorem(e, res, Assumptions::emptyAssump(), pf);
}



//! BVPLUS(n, c1,c2,...,cn) = c  (bit-vector plus of constant bitvectors)
Theorem BitvectorTheoremProducer::bvplusConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVPLUS,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->getBVPlusParam(e) > 0,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }
  // Transfer the values for each bitvector to a Rational, then add it
  // to the accumulator.
  Rational acc(0);
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    Rational x = d_theoryBitvector->computeBVConst(*i);
    TRACE("bitvector rewrite", "bvplusConst: x(", *i, ") = "+x.toString());
    acc += x;
    TRACE("bitvector rewrite", "bvplusConst: acc = ", acc, "");
  }
  // Extract the bits of 'acc' into the vector
  int resSize = d_theoryBitvector->getBVPlusParam(e);
  vector<bool> res(resSize);
  for(int i=0; i<resSize; i++) {
    res[i] = (mod(acc, 2) == 1);
    TRACE("bitvector rewrite", "bvplusConst: acc = ", acc, "");
    TRACE("bitvector rewrite", "bvplusConst: res["+int2string(i)+"] = ",
	  res[i], "");
    acc = floor(acc/2);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvplus_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}


/*! @brief c0*c1 = c, multiplication of two BVCONST
 */
Theorem BitvectorTheoremProducer::bvmultConst(const Expr& e) {
  if(CHECK_PROOFS) {
    // The kids must be constant expressions
    CHECK_SOUND(e.getOpKind() == BVMULT,
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
    CHECK_SOUND(constantKids(e),
		"BitvectorTheoremProducer::extractConst: e = "+e.toString());
  }
  Rational c = d_theoryBitvector->computeBVConst(e[0]);
  // Do the multiplication
  Rational x = d_theoryBitvector->computeBVConst(e[1]) * c;

  // Extract the bits of 'x' into the vector
  int resSize = d_theoryBitvector->BVSize(e.getType().getExpr());
  vector<bool> res(resSize);
  for(int i=0; i<resSize; i++) {
    res[i] = (mod(x, 2) == 1);
    x = floor(x/2);
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_const", e);
  return newRWTheorem(e, d_theoryBitvector->newBVConstExpr(res), Assumptions::emptyAssump(), pf);
}

Theorem 
BitvectorTheoremProducer::zeroCoeffBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT && e.arity() == 2,
		"BitvectorTheoremProducer::zeroCoeffBVMult: e = "+e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind(),
		"BitvectorTheoremProducer::zeroCoeffBVMult: e = "+e.toString());
    Rational c = d_theoryBitvector->computeBVConst(e[0]);
    CHECK_SOUND(0 == c,
		"BitvectorTheoremProducer::zeroCoeffBVMult:"
		"coeff must be zero:\n e = " +e.toString());
  }
  int size = d_theoryBitvector->BVSize(e);
  Expr output = d_theoryBitvector->newBVZeroString(size);
  
  Proof pf;
  if(withProof())
    pf = newPf("zerocoeff_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

Theorem 
BitvectorTheoremProducer::oneCoeffBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVMULT && e.arity() == 2,
		"BitvectorTheoremProducer::oneCoeffBVMult: e = "
		+e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind(),
		"BitvectorTheoremProducer::oneCoeffBVMult: e = "
		+e.toString());
    Rational c = d_theoryBitvector->computeBVConst(e[0]);
    CHECK_SOUND(1 == c,
		"BitvectorTheoremProducer::oneCoeffBVMult:"
		"coeff must be one:\n e = " +e.toString());
  }
  int size = d_theoryBitvector->BVSize(e);
  Expr output = pad(size,e);
  
  Proof pf;
  if(withProof())
    pf = newPf("onecoeff_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! t1*a <==> a*t1
Theorem
BitvectorTheoremProducer::flipBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.arity()==2 && BVMULT == e.getOpKind(),
		"BVMULT must have exactly 2 kids: " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  Expr output = d_theoryBitvector->newBVMultExpr(len,e[1],e[0]);
  
  Proof pf;
  if(withProof())
    pf = newPf("flip_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! Converts e into a BVVECTOR of bvLength 'len'
/*!
 * \param len is the desired bvLength of the resulting bitvector
 * \param e is the original bitvector of arbitrary bvLength
 */
Expr 
BitvectorTheoremProducer::pad(int len, const Expr& e) {
  DebugAssert(len > 0,
	      "TheoryBitvector::pad:" 
	      "padding bvLength must be a non-negative integer: "+
	      int2string(len));
  DebugAssert(BITVECTOR == e.getType().getExpr().getOpKind(),
	      "TheoryBitvector::newBVPlusExpr:" 
	      "input must be a BITVECTOR: " + e.toString());
	      
  int size = d_theoryBitvector->BVSize(e);
  Expr res;
  if(size == len)
    res = e;
  else if (len < size)
    res = d_theoryBitvector->newBVExtractExpr(e,len-1,0);
  else {
    // size < len
    Expr zero = d_theoryBitvector->newBVZeroString(len-size);
    res = d_theoryBitvector->newConcatExpr(zero,e);
  }
  return res;
}

//! Pad the kids of BVMULT to make their bvLength = # of output-bits
Theorem
BitvectorTheoremProducer::padBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == e.getOpKind() && e.arity()>1,
		"BitvectorTheoremProducer::padBVPlus: " 
		"input must be a BVPLUS: " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    if(i->getOpKind() == BVMULT) {
      Expr e0 = pad(len, (*i)[0]);
      Expr e1 = pad(len, (*i)[1]);
      Expr out = d_theoryBitvector->newBVMultExpr(len,e0,e1);
      kids.push_back(out);
    }
    else
      kids.push_back(pad(len, *i));
  }

  Expr output = d_theoryBitvector->newBVPlusExpr(len, kids);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvplus", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! Pad the kids of BVMULT to make their bvLength = # of output-bits
Theorem
BitvectorTheoremProducer::padBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity()==2,
		"BitvectorTheoremProducer::padBVMult: " 
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BITVECTOR==e[0].getType().getExpr().getOpKind() &&
		BITVECTOR==e[1].getType().getExpr().getOpKind(),
		"for BVMULT terms e[0],e[1] must be a BV: " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  Expr e0 = pad(len, e[0]);
  Expr e1 = pad(len, e[1]);
 
  Expr output = d_theoryBitvector->newBVMultExpr(len,e0,e1);

  Proof pf;
  if(withProof())
    pf = newPf("pad_bvmult", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! a*(b*t) <==> (a*b)*t, where a,b,t have same bvLength
Theorem
BitvectorTheoremProducer::bvConstMultAssocRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity() == 2,
		"BitvectorTheoremProducer::bvConstMultAssocRule: " 
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BVMULT == e[1].getOpKind(),
		"BitvectorTheoremProducer::bvConstMultAssocRule: " 
		"e[1] must be a BVMULT:\n e= " + e.toString());
    CHECK_SOUND(BVCONST == e[0].getKind() && 
		BVCONST == e[1][0].getKind(),
		"BitvectorTheoremProducer::bvConstMultAssocRule: " 
		"e[0] & e[1][0] must be a BVCONST:\n e = " + e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  int len0 = d_theoryBitvector->BVSize(e[0]);
  int len10 = d_theoryBitvector->BVSize(e[1][0]);
  int len11 = d_theoryBitvector->BVSize(e[1][1]);
  if(CHECK_PROOFS) {
    CHECK_SOUND(len == len0 && len0 == len10 && len0 == len11,
		"BitvectorTheoremProducer::bvConstMultAssocRule: "
		"kids of BVMULT must be equibvLength: ");
  }
  Rational e0 = d_theoryBitvector->computeBVConst(e[0]);
  Rational e10 = d_theoryBitvector->computeBVConst(e[1][0]);
  Expr c = d_theoryBitvector->newBVConstExpr(e0*e10, len);
  Expr output = d_theoryBitvector->newBVMultExpr(len, c, e[1][1]);

  Proof pf;
  if(withProof())
    pf = newPf("bvconstmult_assoc_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}


//FIXME: make BVMULT n-ary
//! (t1*t2)*t3 <==> t1*(t2*t3), where t1<t2<t3
Theorem
BitvectorTheoremProducer::bvMultAssocRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity() == 2,
		"BitvectorTheoremProducer::bvMultAssocRule: " 
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BVMULT == e[0].getOpKind() || 
		BVMULT == e[1].getOpKind(),
		"BitvectorTheoremProducer::bvMultAssocRule: " 
		"e[0] or e[1] must be a BVMULT:\n e= " + e.toString());
    CHECK_SOUND(!(BVCONST == e[0].getOpKind() && 
		  BVCONST == e[1][0].getOpKind()),
		"BitvectorTheoremProducer::bvMultAssocRule: " 
		"e[0] & e[1][0] cannot be a BVCONST:\n e = " + 
		e.toString());
  }
  int len = d_theoryBitvector->BVSize(e);
  int len0 = d_theoryBitvector->BVSize(e[0]);
  int len1 = d_theoryBitvector->BVSize(e[1]);
  if(CHECK_PROOFS)
    CHECK_SOUND(len == len0 && len0 == len1,
		"BitvectorTheoremProducer::bvMultAssocRule: "
		"kids of BVMULT must be equibvLength: ");
  Expr e0, e1;
  e0 = e[0];
  e1 = e[1];

  std::vector<Expr> outputkids;
  if(BVMULT == e[0].getOpKind() && BVMULT != e[1].getOpKind()) {
    outputkids.push_back(e0[0]);
    outputkids.push_back(e0[1]);
    outputkids.push_back(e1);

  } else if(BVMULT != e[0].getOpKind() && BVMULT == e[1].getOpKind()) {
    outputkids.push_back(e1[0]);
    outputkids.push_back(e1[1]);
    outputkids.push_back(e0);
  } else {
    //both must be BVMULTs
    outputkids.push_back(e0[0]);
    outputkids.push_back(e0[1]);
    outputkids.push_back(e1[0]);
    outputkids.push_back(e1[1]);
  }
  sort(outputkids.begin(),outputkids.end());

  Expr output;  
  switch(outputkids.size()) {
  case 3: {
    Expr out1 = 
      d_theoryBitvector->newBVMultExpr(len, outputkids[1],outputkids[2]);
    output = 
      d_theoryBitvector->newBVMultExpr(len, outputkids[0], out1);
    break;
  }
  case 4: {
    Expr out0 =
      d_theoryBitvector->newBVMultExpr(len, outputkids[0], outputkids[1]);
    Expr out1 = 
      d_theoryBitvector->newBVMultExpr(len, outputkids[2], outputkids[3]);
    output = 
      d_theoryBitvector->newBVMultExpr(len, out0, out1);    
    break;
  }
  }

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_assoc_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! a*(t1+...+tn) <==> (a*t1+...+a*tn), where all kids are equibvLength
Theorem 
BitvectorTheoremProducer::bvMultDistRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVMULT == e.getOpKind() && e.arity() == 2,
		"BitvectorTheoremProducer::bvMultDistRule: " 
		"input must be a BVMULT: " + e.toString());
    CHECK_SOUND(BVPLUS == e[1].getOpKind(),
		"BitvectorTheoremProducer::bvMultDistRule: " 
		"input must be of the form a*(t1+...+tn): " + e.toString());
  }
  int bvLength= d_theoryBitvector->BVSize(e);
  int e0len = d_theoryBitvector->BVSize(e[0]);
  int e1len = d_theoryBitvector->BVSize(e[1]);
  if(CHECK_PROOFS) {
    CHECK_SOUND(bvLength== e0len && e0len == e1len,
		"BitvectorTheoremProducer::bvMultDistRule: " 
		"all subterms must of equal bvLength: " + e.toString());
  }
  const Expr& e0 = e[0];
  const Expr& e1 = e[1];
  
  std::vector<Expr> v;
  Expr::iterator i = e1.begin();
  Expr::iterator iend = e1.end();
  for(;i != iend; ++i) {
    Expr s = d_theoryBitvector->newBVMultExpr(bvLength, e0, *i);
    v.push_back(s);
  }
  Expr output = d_theoryBitvector->newBVPlusExpr(bvLength,v);

  Proof pf;
  if(withProof())
    pf = newPf("bvmult_distributivity_rule", e);
  Theorem result(newRWTheorem(e,output,Assumptions::emptyAssump(),pf));
  return result;
}

//! input BVPLUS expression e.output e <==> e', where e' has no BVPLUS
//  kids. remember, the invariant is that kids are already in
//  bvplus normal-form
Theorem 
BitvectorTheoremProducer::flattenBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == BVPLUS && e.arity() >= 2,
		"BitvectorTheoremProducer::flattenBVPlus: e = "+e.toString());
  }
  int bvLength= d_theoryBitvector->BVSize(e);
  const int numOfKids = e.arity();

  if(CHECK_PROOFS) {
    for(int i=0; i<numOfKids; ++i)
      CHECK_SOUND(d_theoryBitvector->BVSize(e[i]) == bvLength,
		  "BitvectorTheoremProducer::flattenBVPlus: "
		  "summands must be of the same bvLength as BVPLUS:\n e = "
		  +e.toString());
  }
  
  //collect the kids of e in the vector v. if any kid is a BVPLUS,
  //then collect its kids into v. then construct a BVPLUS expr
  std::vector<Expr> v;
  for(int i = 0; i < numOfKids; ++i) {
    if(e[i].getOpKind() == BVPLUS) {      
      const Expr& bvplusKid = e[i];
      const int bvplusArity = bvplusKid.arity();
      for(int j=0; j < bvplusArity; ++j)
	v.push_back(bvplusKid[j]);
    } else 
      v.push_back(e[i]);
  }
  Expr eprime = d_theoryBitvector->newBVPlusExpr(bvLength, v);

  Proof pf;
  if(withProof())
    pf = newPf("flatten_bvplus", e);
  return newRWTheorem(e, eprime, Assumptions::emptyAssump(), pf);  
}

void
BitvectorTheoremProducer::collectOneTermOfPlus(const Rational & coefficient,
					       const Expr& term,
					       ExprMap<Rational> & likeTerms,
					       Rational & plusConstant)
{
  ExprMap<Rational>::iterator it = likeTerms.find(term);

  if(it!=likeTerms.end())
    likeTerms[term] += coefficient;
  else {
    // Check if there is a negated form of this term already in likeTerms map.
    bool foundNegated= false;
    if (!likeTerms.empty()) {
      Expr negTerm= d_theoryBitvector->pushNegationRec(term, true).getRHS();
      it = likeTerms.find(negTerm);
      if (it!= likeTerms.end()) {
	foundNegated = true;
	
	// Use the rule that ~(c*x) = -c*x-1 (based on the fact: -x= ~x+1).
	likeTerms[negTerm] += -coefficient;
	plusConstant+= -1;
      }
    }
    if (!foundNegated)
      // Negated form was not found, need to register the new positive form.
      likeTerms[term] = coefficient;
  }
}

void 
BitvectorTheoremProducer::collectLikeTermsOfPlus(const Expr& e, 
						 ExprMap<Rational> & likeTerms,
						 Rational & plusConstant) {
  likeTerms.clear();
  Expr::iterator i = e.begin();
  Expr::iterator iend = e.end();
  plusConstant= 0;
  //go thru' bvplus term, one monom at a time
  for(; i!=iend; ++i) {
    const Expr s = *i;
    switch(s.getOpKind()) {
    case BVMULT: {
      //if monom is BVMULT, collect like terms using ExprMap
      if (s[0].getKind() == BVCONST) {
        Rational coefficient= d_theoryBitvector->computeBVConst(s[0]);
        const Expr& var = s[1];
        collectOneTermOfPlus(coefficient, var, likeTerms, plusConstant);
      }
      else { // non-linear mult
        if(CHECK_PROOFS) {
          CHECK_SOUND(BVCONST != s[1].getKind(),
		    "TheoryBitvector::combineLikeTerms: "
		    "Unexpected MULT syntax:\n\n s = " + s.toString()
		    +"\n\n in e = "+e.toString());
        }
        collectOneTermOfPlus(1, s, likeTerms, plusConstant);
      }
      break;
    }
    case BVUMINUS:
      collectOneTermOfPlus(-1, s[0], likeTerms, plusConstant);
      break;
    case BVCONST:
      plusConstant += d_theoryBitvector->computeBVConst(s);
      break;
    default:
      //we have just a variable; check if variable in ExprMap
      collectOneTermOfPlus(1, s, likeTerms, plusConstant);
      break;
    }
  }
}

static Rational boundedModulo(const Rational & value, const Rational & modulo,
			      const Rational & lowerBound) {
    Rational ret = mod(value, modulo);
    if(ret == 0)
      return ret;

    if (ret< lowerBound)
      ret+= modulo;
    else {
      // end is one position beyond upper limit.
      Rational end= modulo+lowerBound;
      if (ret >= end)
	ret-= modulo;
    }
    return ret;
}

void 
BitvectorTheoremProducer::
createNewPlusCollection(const Expr & e,
			const ExprMap<Rational> & likeTerms,
			Rational & plusConstant,
			std::vector<Expr> & result) {
  int bvplusLength= d_theoryBitvector->BVSize(e);
  // Compute 2^n, to use as a modulus base
  Rational power2(1);
  for(int i=0; i<bvplusLength; i += 1) power2 *= 2;

  ExprMap<Rational>::iterator j = likeTerms.begin();
  ExprMap<Rational>::iterator jend = likeTerms.end();
  for(; j!=jend; ++j) {
    // The coefficient will be equivalent to j->second modulus of power2 
    // and in the range [-power2/2+1, power2/2]
    // FIXME: Need to reconsider the "best" coefficient normalization scheme.
    Rational coefficient = boundedModulo(j->second, power2, -power2/2+1);
    if(coefficient == 0) 
      continue;
    Expr multiplicand = j->first;
    Expr monomial;
    if (coefficient<0) {
      // Make the coefficient positive: c<0 ;
      // (c*x)= (-c)*(-x)= (-c)*(~x+1)=(-c)*(~x) -c
      multiplicand= 
	d_theoryBitvector->pushNegationRec(multiplicand, true).getRHS();
      coefficient= coefficient*-1;
      plusConstant +=coefficient;
    }
    if(coefficient == 1)
      monomial = multiplicand;
    else {
      Expr coeffExpr = 
	d_theoryBitvector->newBVConstExpr(coefficient, bvplusLength);
      monomial = 
	d_theoryBitvector->newBVMultExpr(bvplusLength, coeffExpr,multiplicand);
    }
    if(CHECK_PROOFS) {
      CHECK_SOUND(BITVECTOR==monomial.getType().getExpr().getOpKind(),
		  "TheoryBitvector::combineLikeTerms:"
		  "each monomial must be a bitvector:\n"
		  "monomial = " + monomial.toString());
      CHECK_SOUND(bvplusLength == d_theoryBitvector->BVSize(monomial),
		  "TheoryBitvector::combineLikeTerms:"
		  "bvLength of each monomial must be the same as e:\n"
		  "monomial = " + monomial.toString() + "\n e = " + e.toString());
    }		  
    result.push_back(monomial);
  }
  // Positive modulo of the constant 
  plusConstant = boundedModulo(plusConstant, power2, 0);

  //make the constant a subterm of the BVPLUS expression
  if(plusConstant != 0) {
    const Expr c = 
      d_theoryBitvector->newBVConstExpr(plusConstant, bvplusLength);
    result.push_back(c);
  }
}

Expr
BitvectorTheoremProducer::sumNormalizedElements(int bvplusLength,
						const std::vector<Expr>&items){
  //construct a new BVPLUS term using the ExprMap.  if size of
  //likeTerms is less than 2, then do NOT construct BVPLUS
  switch(items.size()) {
  case 0:
    //items are empty. only constant 0 remains
    return d_theoryBitvector->newBVZeroString(bvplusLength);
    
  case 1:
    //items may contain a Expr of the form a*x or x or a
    return items[0];
    
  default:
    //items have 2 or more kids
    return d_theoryBitvector->newBVPlusExpr(bvplusLength, items); 
  }
}

Theorem 
BitvectorTheoremProducer::combineLikeTermsRule(const Expr& e) {
  TRACE("bitvector rewrite", "combineLikeTermsRule(",e.toString(), ") {");
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVPLUS == e.getOpKind() && e.arity()>=2,
		"TheoryBitvector::combineLikeTerms: "
		"input must be a BVPLUS term:\n e = " + e.toString());
    int bvplusLength = d_theoryBitvector->BVSize(e);
    Expr::iterator i = e.begin();
    Expr::iterator iend = e.end();
    for(;i!=iend;++i) {
      const Expr& s = *i;
      if(s.getOpKind() == BVPLUS) {
	CHECK_SOUND(s.getOpKind() != BVPLUS,
		    "TheoryBitvector::combineLikeTerms: "
		    "BVPLUS must be flattened:\n e = " + e.toString());
      }

      int bvLength= d_theoryBitvector->BVSize(s);
      //bvLength checks for BVCONST and variables
      CHECK_SOUND(bvLength==bvplusLength,
		  "TheoryBitvector::combineLikeTerms: "
		  "BVPLUS must be padded:\n e = " + e.toString());
      //Length checks for BVMULTs
      if(s.getOpKind()==BVMULT) {
	int s0len = d_theoryBitvector->BVSize(s[0]);
	int s1len = d_theoryBitvector->BVSize(s[1]);
	CHECK_SOUND(bvplusLength == s0len && s0len== s1len,
		    "all monoms must have the samebvLength "
		    "as the bvplus term: " + e.toString());
      }
    }
  }
  int bvplusLength = d_theoryBitvector->BVSize(e);
  ExprMap<Rational> likeTerms;
  Rational theConstant(0);
  collectLikeTermsOfPlus(e, likeTerms, theConstant);
  
  std::vector<Expr> collection;
  createNewPlusCollection(e, likeTerms, theConstant, collection);

  Expr output= sumNormalizedElements(bvplusLength, collection);

  TRACE("bitvector rewrite", 
	"combineLikeTermsRule =>",output.toString(), "}");
  Proof pf;
  if(withProof())
    pf=newPf("bvplus_combine_like_terms", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::lhsMinusRhsRule(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(EQ == e.getKind() && e.arity() == 2,
		"BitvectorTheoremProducer::lhsMinusRhsRule: "
		"input must be an EQ: e = " +e.toString());
    CHECK_SOUND(BVPLUS == e[0].getOpKind() ||
		BVPLUS == e[1].getOpKind(),
		"BitvectorTheoremProducer::lhsMinusRhsRule: "
		"atleast one of the input subterms must be BVPLUS:" 
		"e = " +e.toString());
    int bvLength0 = d_theoryBitvector->BVSize(e[0]);
    int bvLength1 = d_theoryBitvector->BVSize(e[1]);
    CHECK_SOUND(bvLength0 == bvLength1,
		"BitvectorTheoremProducer::lhsMinusRhsRule: "
		"both sides of EQ must be same Length. e = " +e.toString());
    for(Expr::iterator i=e[0].begin(),iend=e[0].end();i!=iend;++i) {
      int bvLength= d_theoryBitvector->BVSize(*i);
      CHECK_SOUND(bvLength0 == bvLength,
		  "BitvectorTheoremProducer::lhsMinusRhsRule: "
		  "all subterms of e[0] must be of same Length." 
		  "e = " +e.toString());
    }
    for(Expr::iterator i=e[1].begin(),iend=e[1].end();i!=iend;++i) {
      int bvLength= d_theoryBitvector->BVSize(*i);
      CHECK_SOUND(bvLength1 == bvLength,
		  "BitvectorTheoremProducer::lhsMinusRhsRule: "
		  "all subterms of e[1] must be of same Length." 
		  "e = " +e.toString());
    }
  }
  Expr output;
  int bvLength = d_theoryBitvector->BVSize(e[0]);
  std::vector<Expr> k;

  //construct 0 of bvLength
  Expr zeroStr = d_theoryBitvector->newBVZeroString(bvLength);

  if(e[0] == e[1])
    output = Expr(EQ, zeroStr, zeroStr);
  else {
    //drop common subterms
    std::vector<Expr> e0K = e[0].getKids();
    std::vector<Expr> e1K = e[1].getKids();
    for(vector<Expr>::iterator i=e0K.begin(),iend=e0K.end();i!=iend;++i){
      for(vector<Expr>::iterator j=e1K.begin(),jend=e1K.end();j!=jend;++j){
	if(*i == *j) {
	  e0K.erase(i);
	  e1K.erase(j);
	  break;
	}	
      }
    }
    Expr newLhs = d_theoryBitvector->newBVPlusExpr(bvLength, e0K);
    k.push_back(newLhs);
    Expr newRhs = d_theoryBitvector->newBVPlusExpr(bvLength, e1K);
    //construct -rhs
    Expr uminus = d_theoryBitvector->newBVUminusExpr(newRhs);
    //push back -rhs
    k.push_back(uminus);  
    //construct lhs-rhs
    Expr lhsMinusRhs = d_theoryBitvector->newBVPlusExpr(bvLength,k);
    //construct lhs-rhs=0
    output = Expr(EQ, lhsMinusRhs, zeroStr);
  }       
   
  Proof pf;
  if(withProof())
    pf = newPf("lhs_minus_rhs_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! generic rule used for bitblasting step. -e <==> ~e+1
Theorem
BitvectorTheoremProducer::bvuminusToBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusBitBlastRule: "
		"input must be bvuminus: e = " + e.toString());
  }
  int bvLength = d_theoryBitvector->BVSize(e);
  std::vector<Expr> k;
  Expr negE0 = d_theoryBitvector->newBVNegExpr(e[0]);
  k.push_back(negE0);
  Expr plusOne = d_theoryBitvector->newBVConstExpr(1, bvLength);
  k.push_back(plusOne);

  Expr output = d_theoryBitvector->newBVPlusExpr(bvLength, k);
  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bitblast_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! -0 <==> 0, -c <==> ~c+1
Theorem 
BitvectorTheoremProducer::bvuminusBVConst(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind() && 
		BVCONST == e[0].getKind(),
		"BitvectorTheoremProducer::bvuminusBVConst: "
		"e should be bvuminus, e[0] should be bvconst: e = " + 
		e.toString());
  }
  Expr output;  
  int e0Length = d_theoryBitvector->BVSize(e[0]);
  // output == 0
  if(d_theoryBitvector->computeBVConst(e[0]) == 0)
    output = e[0];
  else {
    // Compute -c, which is ~c+1
    Rational x = d_theoryBitvector->computeNegBVConst(e[0]);
    output = d_theoryBitvector->newBVConstExpr(x, e0Length);
  }
  
  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bvconst_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! -(c*t)<=>(-c)*t; if -c==0 return e<=>0. if(-c==1) return e<=>t
Theorem 
BitvectorTheoremProducer::bvuminusBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusBVMult: "
		"e should be bvuminus: e =" + e.toString());
    CHECK_SOUND(BVMULT == e[0].getOpKind(),
		"Bitvectortheoremproducer::bvuminusBVMult: "
		"in input expression e = " + e.toString() +
		"\ne[0] should be bvmult: e[0] = " + e[0].toString());
    CHECK_SOUND(BVCONST == e[0][0].getKind(),
		"Bitvectortheoremproducer::bvuminusBVMult: "
		"in input expression e = " + e.toString() +
		"\ne[0][0] should be bvconst: e[0][0] = " + e[0][0].toString());    
    int bvLength =  d_theoryBitvector->BVSize(e);
    int e0Length =  d_theoryBitvector->BVSize(e[0]);
    int e00Length =  d_theoryBitvector->BVSize(e[0][0]);
    CHECK_SOUND(bvLength == e0Length && e0Length == e00Length,
		"Bitvectortheoremproducer::bvuminusBVMult: "
		"in input expression e = " + e.toString() +
		"\nLengths of all subexprs must be equal: e = " + e.toString());    
  }
  //e is of the form -(c*t)
  Expr output;
  int e0Length = d_theoryBitvector->BVSize(e[0]);
  //compute ~c+1 
  Rational coeff = d_theoryBitvector->computeNegBVConst(e[0][0]);
  if(0 == coeff)
    //if ~c+1 == 0
    output = d_theoryBitvector->newBVZeroString(e0Length);
  else if (1 == coeff)
    //if ~c+1 == 1
    output = e[0][1];
  else {
    //construct (~c+1)*t
    Expr newcoeff = d_theoryBitvector->newBVConstExpr(coeff, e0Length);
    output = d_theoryBitvector->newBVMultExpr(e0Length, newcoeff, e[0][1]);
  }
  
  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bvmult_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! -(-e) <==> e
Theorem 
BitvectorTheoremProducer::bvuminusBVUminus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusBVUminus: "
		"e should be bvuminus: e =" + e.toString());
    CHECK_SOUND(BVUMINUS == e[0].getOpKind(),
		"Bitvectortheoremproducer::bvuminusBVUminus: "
		"in input expression e = " + e.toString() +
		"\ne[0] should be bvmult: e[0] = " + e[0].toString());
  }
  Expr output;
  // -(-e) <==> e
  output = e[0][0];
  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_bvuminus_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! -v <==> -1*v
Theorem 
BitvectorTheoremProducer::bvuminusVar(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvuminusVar: "
		"e should be bvuminus: e =" + e.toString());    
  }
  Expr output;
  std::vector<bool> res;
  int e0Length = d_theoryBitvector->BVSize(e[0]);
  for(int i=0; i<e0Length; ++i) {
    res.push_back(true);
  }
  Expr coeff = d_theoryBitvector->newBVConstExpr(res);
  output = d_theoryBitvector->newBVMultExpr(e0Length, coeff, e[0]);

  Proof pf;
  if(withProof())
    pf = newPf("bvuminus_var_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! c*(-t) <==> (-c)*t
Theorem 
BitvectorTheoremProducer::bvmultBVUminus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(BVUMINUS == e.getOpKind(),
		"BitvectorTheoremProducer::bvmultBVUminus: "
		"e should be bvuminus: e =" + e.toString());    
    CHECK_SOUND(BVMULT == e[0].getOpKind() &&
		BVCONST == e[0][0].getKind() &&
		BVUMINUS == e[0][1].getOpKind(),
		"Bitvectortheoremproducer::bvmultBVUminus: "
		"in input expression e = " + e.toString() +
		"\ne[0] has to be bvmult" 
		"e[0][1] must be bvuminus: e[0] = " + e[0].toString());
    int bvLength = d_theoryBitvector->BVSize(e);
    int e00Length = d_theoryBitvector->BVSize(e[0][0]);
    int e01Length = d_theoryBitvector->BVSize(e[0][1]);
    CHECK_SOUND(bvLength == e00Length && e00Length == e01Length,
		"Bitvectortheoremproducer::bvmultBVUminus: "
		"in input expression e = " + e.toString() +
		"\nLengths of all subexprs must be equal.");    
  }
  Expr output;
  int bvLength = d_theoryBitvector->BVSize(e);
  const Expr& coeff = e[0][0];
  Rational negatedcoeff = d_theoryBitvector->computeNegBVConst(coeff);
  const Expr& e010 = e[0][1][0]; 
  
  if(0 == negatedcoeff)
    //if ~c+1 == 0
    output = d_theoryBitvector->newBVZeroString(bvLength);
  else if (1 == negatedcoeff)
    //if ~c+1 == 1
    output = e010;
  else {
    //construct (~c+1)*t
    Expr newcoeff = d_theoryBitvector->newBVConstExpr(negatedcoeff, bvLength);
    output = d_theoryBitvector->newBVMultExpr(bvLength, newcoeff, e010);
  }
  
  Proof pf;
  if(withProof())
    pf = newPf("bvmult_bvuminus_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

//! -(c1*t1+...+cn*tn) <==> (-(c1*t1)+...+-(cn*tn))
Theorem 
BitvectorTheoremProducer::bvuminusBVPlus(const Expr& e) {
//   if(CHECK_PROOFS) {
//     CHECK_SOUND(BVUMINUS == e.getOpKind(),
// 		"BitvectorTheoremProducer::bvuminusBVPlus: "
// 		"e should be bvuminus: e =" + e.toString());    
//     CHECK_SOUND(BVPLUS == e[0].getOpKind(),
// 		"BitvectorTheoremProducer::bvuminusBVPlus: "
// 		"e[0] should be bvplus: e[0] =" + e[0].toString());    
//   }
//   int bvLength = d_theoryBitvector->BVSize(e);
//   const Expr& e0 = e[0];
//   Expr::iterator i = e0.begin();
//   Expr::iterator iend = e0.end();
//   std::vector<Expr> output;
//   for(; i!=iend; ++i) {
//     const Expr& s = *i;
//     Expr t = d_theoryBitvector->newBVUminusExpr(s);
//     output.push_back(t);
//   }
//   Expr outputPlus = 
//     d_theoryBitvector->newBVPlusExpr(bvLength, output);

//   Assumptions a;
//   Proof pf;
//   if(withProof())
//     pf = newPf("bvminus_bvplus_rule", e);
//   return newRWTheorem(e, outputPlus, a, pf);

  Proof pf;
  if(withProof())
    pf = newPf("bvminus_bvplus_rule", e);
  return newRWTheorem(e, e, Assumptions::emptyAssump(), pf);
}

Theorem
BitvectorTheoremProducer::extractBVMult(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && 
		e[0].getOpKind() == BVMULT &&
		e[0].arity() == 2,
		"BitvectorTheoremProducer::extractBVMult: " 
		"input must be an EXTRACT over BVMULT:\n e = "+e.toString());
  }
  const Expr& bvmult = e[0];
  int bvmultLen = d_theoryBitvector->BVSize(bvmult);
  int extractHi = d_theoryBitvector->getExtractHi(e);
  int extractLow = d_theoryBitvector->getExtractLow(e);

  if(CHECK_PROOFS) {
    CHECK_SOUND(bvmultLen > extractHi,
		"BitvectorTheoremProducer::extractBVMult: "
		"bvmult Length must be greater than extract Length:\n e = "
		+e.toString());
  }
  
  Expr output = d_theoryBitvector->newBVMultExpr(extractHi+1, bvmult[0],
						 bvmult[1]);
  if(extractLow > 0)
    output=d_theoryBitvector->newBVExtractExpr(output, extractHi, extractLow);

  Proof pf;
  if(withProof())
    pf = newPf("extract_bvmult_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}

Theorem
BitvectorTheoremProducer::extractBVPlus(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.getOpKind() == EXTRACT && e[0].getOpKind() == BVPLUS,
		"BitvectorTheoremProducer::extractBVPlus: " 
		"input must be an EXTRACT over BVPLUS:\n e = "+e.toString());
  }
  const Expr& bvplus = e[0];
  int bvplusLen = d_theoryBitvector->BVSize(bvplus);
  int extractHi = d_theoryBitvector->getExtractHi(e);
  int extractLow = d_theoryBitvector->getExtractLow(e);

  if(CHECK_PROOFS) {
    CHECK_SOUND(bvplusLen > extractHi,
		"BitvectorTheoremProducer::extractBVPlus: "
		"bvplus Length must be greater than extract bvLength:\n e = "
		+e.toString());
  }
  
  // Shortcut
  if(bvplusLen == extractHi+1)
    return d_theoryBitvector->reflexivityRule(e);

  // Shorten the result width of the bvplus term
  Expr output(d_theoryBitvector->newBVPlusExpr(extractHi+1, bvplus.getKids()));
  if(extractLow > 0)
    output=d_theoryBitvector->newBVExtractExpr(output, extractHi, extractLow);

  Proof pf;
  if(withProof())
    pf = newPf("extract_bvplus_rule", e);
  return newRWTheorem(e, output, Assumptions::emptyAssump(), pf);  
}


// |- t=0 OR t=1  for any 1-bit bitvector t
Theorem
BitvectorTheoremProducer::typePredBit(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(d_theoryBitvector->getBaseType(e).getExpr().getOpKind() == BITVECTOR,
		"BitvectorTheoremProducer::typePredBit: e = "+e.toString());
    CHECK_SOUND(d_theoryBitvector->BVSize(e) == 1,
		"BitvectorTheoremProducer::typePredBit: e = "+e.toString());
  }

  Proof pf;
  if(withProof())
    pf=newPf("type_pred_bit", e);
  return newTheorem(e.eqExpr(bvZero()) || e.eqExpr(bvOne()), Assumptions::emptyAssump(), pf);
}


//! Expand the type predicate wrapper (compute the actual type predicate)
Theorem
BitvectorTheoremProducer::expandTypePred(const Theorem& tp) {
  Expr tpExpr = tp.getExpr();
  if(CHECK_PROOFS) {
    CHECK_SOUND(tpExpr.getOpKind() == BVTYPEPRED || 
		(tpExpr.getKind() == NOT && tpExpr[0].getOpKind() == BVTYPEPRED),
		"BitvectorTheoremProducer::expandTypePred: "
		"Expected BV_TYPE_PRED wrapper:\n tp = "
		+tpExpr.toString());
  }
  Expr res;
  if(tpExpr.getKind() == NOT)
    res = d_theoryBitvector->falseExpr();
  else {
    Type t(d_theoryBitvector->getTypePredType(tpExpr));
    const Expr& e(d_theoryBitvector->getTypePredExpr(tpExpr));
    int size(d_theoryBitvector->getBitvectorTypeParam(t));
    //   DebugAssert(BVSize(e)==size, "TheoryBitvector::computeTypePred: e="
    // 	      +e.toString()+", t="+t.toString());
    if(size >= 2) {
      vector<Expr> kids;
      for(int i=0; i<size; i++) {
	Expr bit(d_theoryBitvector->newBVExtractExpr(e, i, i));
	kids.push_back(bit.eqExpr(bvZero()) || bit.eqExpr(bvOne()));
      }
      res = andExpr(kids);
    } else {
      res = (e.eqExpr(bvZero()) || e.eqExpr(bvOne()));
    }
  }
  Proof pf;
  if(withProof())
    pf = newPf("expand_type_pred", tp.getExpr(), tp.getProof());
  
  return newTheorem(res, tp.getAssumptionsRef(), pf);
}
