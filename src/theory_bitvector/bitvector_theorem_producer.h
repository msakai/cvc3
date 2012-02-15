/*****************************************************************************/
/*!
 * \file bitvector_theorem_producer.h
 * \brief TRUSTED implementation of bitvector proof rules
 * 
 * Author: Vijay Ganesh
 * 
 * Created: Wed May  5 16:10:28 PST 2004
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

#ifndef _cvc3__bitvector_theorem_producer_h_
#define _cvc3__bitvector_theorem_producer_h_

#include "bitvector_proof_rules.h"
#include "theorem_producer.h"

namespace CVC3 {

  class TheoryBitvector;

  /*! @brief This class implements proof rules for bitvector
   *  normalizers (concatenation normal form, bvplus normal form),
   *  bitblaster rules, other relevant rewrite rules for bv arithmetic
   *  and word-level operators
  */
  /*!
    Author: Vijay Ganesh, May-August, 2004
    
  */
  class BitvectorTheoremProducer: 
    public BitvectorProofRules, public TheoremProducer {
  private:
    TheoryBitvector* d_theoryBitvector; //! instance of bitvector DP
    //! Constant 1-bit bit-vector 0bin0
    Expr d_bvZero;
    //! Constant 1-bit bit-vector 0bin1
    Expr d_bvOne;
    //! Return cached constant 0bin0
    const Expr& bvZero() const { return d_bvZero; }
    //! Return cached constant 0bin1
    const Expr& bvOne() const { return d_bvOne; }

    //! Collect all of: a*x1+b*x1 + c*x2-x2 + d*x3 + ~x3 + ~x4 +e into
    //!  (a+b, x1) , (c-1 , x2), (d-1, x3), (-1, x4) and the constant e-2.
    //! The constant is calculated from the formula -x = ~x+1 (or -x-1=~x).
    void collectLikeTermsOfPlus(const Expr& e, 
				ExprMap<Rational> & likeTerms,
				Rational & plusConstant);
    
    //! Collect a single coefficient*var pair into likeTerms.
    //! Update the counter of likeTerms[var] += coefficient.
    //! Potentially update the constant additive plusConstant.
    void collectOneTermOfPlus(const Rational & coefficient,
			      const Expr& var,
			      ExprMap<Rational> & likeTerms,
			      Rational & plusConstant);

    //! Create a vector which will form the next PVPLUS.
    //! Use the colleciton of likeTerms, and the constant additive plusConstant
    void createNewPlusCollection(const Expr & e,
				 const ExprMap<Rational> & likeTerms,
				 Rational & plusConstant,
				 std::vector<Expr> & result);
    
    //! Create expression by applying plus to all elements.
    //! All elements should be normalized and ready.
    //! If there are too few elements, a non BVPLUS expression will be created.
    Expr sumNormalizedElements(int bvplusLength,
			       const std::vector<Expr>& elements);
  public:
    //! Constructor: constructs an instance of bitvector DP
    BitvectorTheoremProducer(TheoryBitvector* theoryBitvector);
    ~BitvectorTheoremProducer() {}

    //ExprMap<Expr> d_bvPlusCarryCacheLeftBV;
    //ExprMap<Expr> d_bvPlusCarryCacheRightBV;
    
    ////////////////////////////////////////////////////////////////////
    // Partial Canonization rules
    ////////////////////////////////////////////////////////////////////

    ////////////////////////////////////////////////////////////////////
    // Bitblasting rules for equations
    ////////////////////////////////////////////////////////////////////    
    
    /*! \param thm input theorem: (e1[i]<=>e2[i])<=>false
     *  
     *  \result (e1=e2)<=>false
     */
    Theorem bitvectorFalseRule(const Theorem& thm);

    /*! \param thm input theorem: (~e1[i]<=>e2[i])<=>true
     *  
     *  \result (e1!=e2)<=>true
     */
    Theorem bitvectorTrueRule(const Theorem& thm);

    /*! \param e input equation: e1=e2 over bitvector terms 
     *  \param f formula over the bits of bitvector variables in e:
     *           
     *  \result \f[\frac{e_1 = e_2}{\bigwedge_{i=1}^n (e_{1}[i]
     *  \iff e_{2}[i]) } \f] where each of \f[ e_{1}[i], e{2}[i] \f] denotes a
     *  formula over variables in \f[ e_{1}, e_{2} \f] respectively
     */
    Theorem bitBlastEqnRule(const Expr& e, const Expr& f);

    /*! \param e : input disequality: e1 != e2 over bitvector terms
     *  \param f : formula over the bits of bitvector variables in e:
     *           
     *  \result \f[\frac{e_1 \not = e_2}{\bigwedge_{i=1}^n ((\neg e_{1}[i])
     *  \iff e_{2}[i]) } \f] where each of \f[ e_{1}[i], e{2}[i] \f] denotes a
     *  formula over variables in \f[ e_{1}, e_{2} \f] respectively
     */
    Theorem bitBlastDisEqnRule(const Theorem& e, const Expr& f);


    ////////////////////////////////////////////////////////////////////
    // Bitblasting and rewrite rules for Inequations
    ////////////////////////////////////////////////////////////////////

    //! sign extend the input SX(e) appropriately
    Theorem signExtendRule(const Expr& e);
 
    //! Pad the kids of BVLT/BVLE to make their length equal
    Theorem padBVLTRule(const Expr& e, int len);
 
    //! Sign Extend the kids of SBVLT/SBVLE to make their length equal
    Theorem padSBVLTRule(const Expr& e, int len);

    /*! input: e0 <=(s) e1. output depends on whether the topbits(MSB) of
     *  e0 and e1 are constants. If they are constants then optimizations
     *  are done, otherwise the following rule is implemented.
     *
     *  e0 <=(s) e1 <==> (e0[n-1] AND NOT e1[n-1]) OR 
     *                   (e0[n-1] AND e1[n-1] AND e1[n-2:0] <= e0[n-2:0]) OR 
     *                   (NOT e0[n-1] AND NOT e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
     */
    Theorem signBVLTRule(const Expr& e, 
			 const Theorem& topBit0, 
			 const Theorem& topBit1);

    /*! NOT(e[0][0] < e[0][1]) <==> (e[0][1] <= e[0][0]), 
     *  NOT(e[0][0] <= e[0][1]) <==> (e[0][1] < e[0][0])
     */    
    Theorem notBVLTRule(const Expr& e, int Kind);

    //! if(lhs==rhs) then we have (lhs < rhs <==> false),(lhs <= rhs <==> true)
    Theorem lhsEqRhsIneqn(const Expr& e, int kind);

    Theorem zeroLeq(const Expr& e);
    Theorem bvConstIneqn(const Expr& e, int kind);

    Theorem generalIneqn(const Expr& e, 
			 const Theorem& lhs_i, 
			 const Theorem& rhs_i, int kind);

    ////////////////////////////////////////////////////////////////////
    // Bitblasting rules for terms
    ////////////////////////////////////////////////////////////////////

    //! t[i] ==> t[i:i] = 0bin1   or    NOT t[i] ==> t[i:i] = 0bin0
    Theorem bitExtractToExtract(const Theorem& thm);
    //! t[i] <=> t[i:i][0]   (to use rewriter for simplifying t[i:i])
    Theorem bitExtractRewrite(const Expr& x);

    /*! \param x : input1 is bitvector constant 
     *  \param i : input2 is extracted bitposition 
     *
     *  \result \f[ \frac{}{\mathrm{BOOLEXTRACT(x,i)} \iff
     *  \mathrm{TRUE}} \f], if bitposition has a 1; \f[
     *  \frac{}{\mathrm{BOOLEXTRACT(x,i)} \iff \mathrm{FALSE}} \f], if
     *  the bitposition has a 0
     */
    Theorem bitExtractConstant(const Expr & x, int i);

    /*! \param x : input1 is bitvector binary concatenation
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[m]}@q_{[n]})[i] \iff (q_{[n]})[i]}
     *  \f], where \f[ 0 \geq i \geq n-1 \f], another case of
     *  boolextract over concatenation is:
     *  \f[\frac{}{(t_{[m]}@q_{[n]})[i] \iff (t_{[m]})[i-n]} \f],
     *  where \f[ n \geq i \geq m+n-1 \f]
     */
    Theorem bitExtractConcatenation(const Expr & x, int i); 

    /*! \param t : input1 is bitvector binary BVMULT. x[0] must be BVCONST
     *  \param i : input2 is extracted bitposition
     *
     *  \result bitblast of BVMULT
     */
    Theorem bitExtractConstBVMult(const Expr& t, int i);

    /*! \param t : input1 is bitvector binary BVMULT. t[0] must not be BVCONST
     *  \param i : input2 is extracted bitposition
     *
     *  \result bitblast of BVMULT
     */
    Theorem bitExtractBVMult(const Expr& t, int i);

    /*! \param x : input1 is bitvector extraction [k:j]
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[n]}[k:j])[i] \iff (t_{[n]})[i+j]}
     *  \f], where \f[ 0 \geq j \geq k < n, 0 \geq i < k-j \f]
     */
    Theorem bitExtractExtraction(const Expr & x, int i);

    /*! \param t1 : input1 is vector of bitblasts of t, from bit i-1 to 0
     *  \param t2 : input2 is vector of bitblasts of q, from bit i-1 to 0
     *  \param bvPlusTerm : input3 is BVPLUS term: BVPLUS(n,t,q)
     *  \param i  : input4 is extracted bitposition
     *
     *  \result The base case is: \f[
     *  \frac{}{(\mathrm{BVPLUS}(n,t,q))[0] \iff t[0] \oplus q[0]}
     *  \f], when \f[ 0 < i \leq n-1 \f], we have \f[
     *  \frac{}{(\mathrm{BVPLUS}(n,t,q))[i] \iff t[i] \oplus q[i]
     *  \oplus c(t,q,i)} \f], where c(t,q,i) is the carry generated
     *  by the addition of bits from 0 to i-1
     */
    Theorem bitExtractBVPlus(const std::vector<Theorem>& t1, 
			     const std::vector<Theorem>& t2,
			     const Expr& bvPlusTerm, int i);

    Theorem bitExtractBVPlusPreComputed(const Theorem& t1_i, 
					const Theorem& t2_i,
					const Expr& bvPlusTerm, 
					int bitPos,
					int precomputed);

    /*! \param bvPlusTerm : input1 is bvPlusTerm, a BVPLUS term with
     *  arity > 2
     *
     *  \result : output is iff-Theorem: bvPlusTerm <==> outputTerm,
     *  where outputTerm is an equivalent BINARY bvplus.
     */
    Theorem bvPlusAssociativityRule(const Expr& bvPlusTerm);

    /*! \param x : input1 is bitwise NEGATION
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(\sim t_{[n]})[i] \iff \neg (t_{[n]}[i])}
     *  \f]
     */
    Theorem bitExtractNot(const Expr & x, int i);

    //! Auxiliary function for bitExtractAnd() and bitExtractOr()
    Theorem bitExtractBitwise(const Expr& x, int i, int kind);

    /*! \param x : input1 is bitwise AND
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[n]} \& q_{[n]})[i] \iff (t_{[n]}[i]
     *  \wedge q_{[n]}[i])} \f]
     */
    Theorem bitExtractAnd(const Expr & x, int i);   

    /*! \param x : input1 is bitwise OR
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[n]} \mid q_{[n]})[i] \iff (t_{[n]}[i]
     *  \vee q_{[n]}[i])} \f]
     */
    Theorem bitExtractOr(const Expr & x, int i);   

    /*! \param x : input1 is bitvector FIXED SHIFT \f[ e_{[n]} \ll k \f]
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[\frac{}{(e_{[n]} \ll k)[i] \iff \mathrm{FALSE}}
     *  \f], if 0 <= i < k. however, if k <= i < n then, result is
     *  \f[\frac{}{(e_{[n]} \ll k)[i] \iff e_{[n]}[i]} \f]
     */
    Theorem bitExtractFixedLeftShift(const Expr & x, int i);   

    Theorem bitExtractFixedRightShift(const Expr & x, int i);   
    /*! \param e : input1 is bitvector term
     *  \param r : input2 is extracted bitposition
     *
     *  \result we check if r > bvlength(e). if yes, then return
     *  BOOLEXTRACT(e,r) <==> FALSE; else raise soundness
     *  exception. (Note: this rule is used in BVPLUS bitblast
     *  function)
     */
    Theorem zeroPaddingRule(const Expr& e, int r);

    Theorem bitExtractSXRule(const Expr& e, int i);

    //! c1=c2 <=> TRUE/FALSE (equality of constant bitvectors)
    Theorem eqConst(const Expr& e);
    //! |- c1=c2 ==> |- AND(c1[i:i] = c2[i:i]) - expanding equalities into bits
    Theorem eqToBits(const Theorem& eq);
    //! t<<n = c @ 0bin00...00, takes e == (t<<n)
    Theorem leftShiftToConcat(const Expr& e);
    //! t<<n = c @ 0bin00...00, takes e == (t<<n)
    Theorem constWidthLeftShiftToConcat(const Expr& e);
    //! t>>m = 0bin00...00 @ t[bvlength-1:m], takes e == (t>>n)
    Theorem rightShiftToConcat(const Expr& e);
    //! k*t = BVPLUS(n, <sum of shifts of t>) -- translation of k*t to BVPLUS
    /*! If k = 2^m, return k*t = t\@0...0 */
    Theorem constMultToPlus(const Expr& e);
    //! 0bin0...0 @ BVPLUS(n, args) = BVPLUS(n+k, args)
    /*! where k is the size of the 0bin0...0 */
    Theorem bvplusZeroConcatRule(const Expr& e);


    ///////////////////////////////////////////////////////////////////
    /////  Bvplus Normal Form rules
    ///////////////////////////////////////////////////////////////////
    Theorem zeroCoeffBVMult(const Expr& e);
    Theorem oneCoeffBVMult(const Expr& e);
    Theorem flipBVMult(const Expr& e);
    //! converts e to a bitvector of length rat
    Expr pad(int rat, const Expr& e);
    Theorem padBVPlus(const Expr& e);
    Theorem padBVMult(const Expr& e);
    Theorem bvConstMultAssocRule(const Expr& e);
    Theorem bvMultAssocRule(const Expr& e);
    Theorem bvMultDistRule(const Expr& e);
    Theorem flattenBVPlus(const Expr& e);
    Theorem combineLikeTermsRule(const Expr& e);
    Theorem lhsMinusRhsRule(const Expr& e);
    Theorem extractBVMult(const Expr& e);
    Theorem extractBVPlus(const Expr& e);
    //! ite(c,t1,t2)[i:j] <=> ite(c,t1[i:j],t2[i:j])
    Theorem iteExtractRule(const Expr& e);
    //! ~ite(c,t1,t2) <=> ite(c,~t1,~t2)
    Theorem iteBVnegRule(const Expr& e);

    Theorem bvuminusBVConst(const Expr& e);
    Theorem bvuminusBVMult(const Expr& e);
    Theorem bvuminusBVUminus(const Expr& e);
    Theorem bvuminusVar(const Expr& e);
    Theorem bvmultBVUminus(const Expr& e);
    //! -t <==> ~t+1
    Theorem bvuminusToBVPlus(const Expr& e);
    //! -(c1*t1+...+cn*tn) <==> (-(c1*t1)+...+-(cn*tn))
    Theorem bvuminusBVPlus(const Expr& e);


    ///////////////////////////////////////////////////////////////////
    /////  Concatenation Normal Form rules
    ///////////////////////////////////////////////////////////////////

    // Extraction rules

    //! c1[i:j] = c  (extraction from a constant bitvector)
    Theorem extractConst(const Expr& e);
    //! t[n-1:0] = t  for n-bit t
    Theorem extractWhole(const Expr& e);
    //! t[i:j][k:l] = t[k+j:l+j]  (eliminate double extraction)
    Theorem extractExtract(const Expr& e);
    //! (t1 @ t2)[i:j] = t1[...] @ t2[...]  (push extraction through concat)
    Theorem extractConcat(const Expr& e);

    //! Auxiliary function: (t1 op t2)[i:j] = t1[i:j] op t2[i:j] 
    Theorem extractBitwise(const Expr& e, int kind, const std::string& name);
    //! (t1 & t2)[i:j] = t1[i:j] & t2[i:j]  (push extraction through OR)
    Theorem extractAnd(const Expr& e);
    //! (t1 | t2)[i:j] = t1[i:j] | t2[i:j]  (push extraction through AND)
    Theorem extractOr(const Expr& e);
    //! (~t)[i:j] = ~(t[i:j]) (push extraction through NEG)
    Theorem extractNeg(const Expr& e);

    // Negation rules

    //! ~c1 = c  (bit-wise negation of a constant bitvector)
    Theorem negConst(const Expr& e);
    //! ~(t1\@...\@tn) = (~t1)\@...\@(~tn) -- push negation through concat
    Theorem negConcat(const Expr& e);
    //! ~(~t) = t  -- eliminate double negation
    Theorem negNeg(const Expr& e);
    //! ~(t1 & t2) <=> ~t1 | ~t2 -- DeMorgan's Laws
    Theorem negBVand(const Expr& e);
    //! ~(t1 | t2) <=> ~t1 & ~t2 -- DeMorgan's Laws
    Theorem negBVor(const Expr& e);

    // Bit-wise AND rules
    //! Auxiliary method for andConst() and orConst()
    Theorem bitwiseConst(const Expr& e, const std::vector<int>& idxs,
			 bool isAnd);
    //! Auxiliary method for andConcat() and orConcat()
    Theorem bitwiseConcat(const Expr& e, int idx, bool isAnd);
    //! Auxiliary method for andFlatten() and orFlatten()
    Theorem bitwiseFlatten(const Expr& e, bool isAnd);

    //! c1&c2&t = c&t -- compute bit-wise AND of constant bitvector arguments
    /*!\param e is the bit-wise AND expression;
     *
     * \param idxs are the indices of the constant bitvectors.  There
     *  must be at least constant expressions in this rule.
     *
     * \return Theorem(e==e'), where e' is either a constant
     * bitvector, or is a bit-wise AND with a single constant
     * bitvector in e'[0].
     */
    Theorem andConst(const Expr& e, const std::vector<int>& idxs);
    //! 0bin0...0 & t = 0bin0...0  -- bit-wise AND with zero bitvector
    /*! \param e is the bit-wise AND expr
     *  \param idx is the index of the zero bitvector
     */
    Theorem andZero(const Expr& e, int idx);
    Theorem andOne(const Expr& e, const std::vector<int> idxs);
    //! ... & (t1\@...\@tk) & ... = (...& t1 &...)\@...\@(...& tk &...)
    /*!
     * Lifts concatenation to the top of bit-wise AND.  Takes the
     * bit-wise AND expression 'e' and the index 'i' of the
     * concatenation.
     */
    Theorem andConcat(const Expr& e, int idx);
    //! (t1 & (t2 & t3) & t4) = t1 & t2 & t3 & t4  -- flatten bit-wise AND
    /*! Also reorders the terms according to a fixed total ordering */
    Theorem andFlatten(const Expr& e);

    // Bit-wise OR rules

    //! c1|c2|t = c|t -- compute bit-wise OR of constant bitvector arguments
    /*!\param e is the bit-wise OR expression;
     *
     * \param idxs are the indices of the constant bitvectors.  There
     *  must be at least constant expressions in this rule.
     *
     * \return Theorem(e==e'), where e' is either a constant
     * bitvector, or is a bit-wise OR with a single constant
     * bitvector in e'[0].
     */
    Theorem orConst(const Expr& e, const std::vector<int>& idxs);
    //! 0bin1...1 | t = 0bin1...1  -- bit-wise OR with bitvector of 1's
    /*! \param e is the bit-wise OR expr
     *  \param idx is the index of the bitvector of 1's
     */
    Theorem orOne(const Expr& e, int idx);
    Theorem orZero(const Expr& e, const std::vector<int> idxs);
    //! ... | (t1\@...\@tk) | ... = (...| t1 |...)\@...\@(...| tk |...)
    /*!
     * Lifts concatenation to the top of bit-wise OR.  Takes the
     * bit-wise OR expression 'e' and the index 'i' of the
     * concatenation.
     */
    Theorem orConcat(const Expr& e, int idx);
    //! (t1 | (t2 | t3) | t4) = t1 | t2 | t3 | t4  -- flatten bit-wise OR
    /*! Also reorders the terms according to a fixed total ordering */
    Theorem orFlatten(const Expr& e);

    
    /*! checks if e is already present in likeTerms without conflicts. 
     *  if yes return 1, else{ if conflict return -1 else return 0 }
     *  we have conflict if 
     *          1. the kind of e is BVNEG, 
     *                 and e[0] is already present in likeTerms
     *          2. ~e is present in likeTerms already
     */
    int sameKidCheck(const Expr& e, ExprMap<int>& likeTerms);

    // Concatenation rules

    //! c1\@c2\@...\@cn = c  (concatenation of constant bitvectors)
    Theorem concatConst(const Expr& e);
    //! Flatten one level of nested concatenation, e.g.: x\@(y\@z)\@w = x\@y\@z\@w
    Theorem concatFlatten(const Expr& e);
    //! Merge n-ary concat. of adjacent extractions: x[15:8]\@x[7:0] = x[15:0]
    Theorem concatMergeExtract(const Expr& e);

    ///////////////////////////////////////////////////////////////////
    /////  Modulo arithmetic rules
    ///////////////////////////////////////////////////////////////////

    //! BVPLUS(n, c1,c2,...,cn) = c  (bit-vector plus of constant bitvectors)
    Theorem bvplusConst(const Expr& e);
    /*! @brief n*c1 = c, where n >= 0 (multiplication of a constant
     *  bitvector by a non-negative constant) */
    Theorem bvmultConst(const Expr& e);

    ///////////////////////////////////////////////////////////////////
    /////  Type predicate rules
    ///////////////////////////////////////////////////////////////////

    //! |- t=0 OR t=1  for any 1-bit bitvector t
    Theorem typePredBit(const Expr& e);

    //! Expand the type predicate wrapper (compute the actual type predicate)
    Theorem expandTypePred(const Theorem& tp);

    ////////////////////////////////////////////////////////////////////
    // Helper functions
    ////////////////////////////////////////////////////////////////////
    //! Create Expr from Rational (for convenience)
    Expr rat(const Rational& r) { return d_em->newRatExpr(r); }
    /*! \param t1BitExtractThms : input1 is vector of bitblasts of t1,
     *  from bit i-1 to 0
     *
     *  \param t2BitExtractThms : input2 is vector of bitblasts of t2,
     *  from bit i-1 to 0 
     *
     *  \param bitPos : input3 is extracted * bitposition
     *
     *  \result is the expression \f$t1[0] \wedge t2[0]\f$ if
     *  bitPos=0. this function is recursive; if bitPos > 0 then the
     *  output expression is
     *  \f[ (t1[i-1] \wedge t2[i-1])
     *     \vee (t1[i-1] \wedge computeCarry(t1,t2,i-1))
     *     \vee (t2[i-1] \wedge computeCarry(t1,t2,i-1))
     *  \f]
     */
    Expr computeCarry(const std::vector<Theorem>& t1BitExtractThms,
		      const std::vector<Theorem>& t2BitExtractThms,
		      int bitPos);

    Expr computeCarryPreComputed(const Theorem& t1_i,
				 const Theorem& t2_i,
				 int bitPos,
				 int precomputedFlag);

    //ExprMap<Expr> carryCache(void);
  }; // end of class BitvectorTheoremProducer
} // end of namespace CVC3

#endif
