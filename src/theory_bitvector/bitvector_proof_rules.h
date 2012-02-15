/*****************************************************************************/
/*!
 * \file bitvector_proof_rules.h
 * \brief Arithmetic proof rules
 *
 * Author: Vijay Ganesh.
 * 
 * Created:Wed May  5 15:47:28 PST 2004
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

#ifndef _cvc3__bitvector_proof_rules_h_
#define _cvc3__bitvector_proof_rules_h_

#include <string>
#include <vector>

namespace CVC3 {

  class Expr;
  class Theorem;

  class BitvectorProofRules {
  public:
    // Destructor
    virtual ~BitvectorProofRules() { }

    ////////////////////////////////////////////////////////////////////
    // Bitblasting rules for equations
    ////////////////////////////////////////////////////////////////////
    
    /*! \param thm input theorem: (e1[i]<=>e2[i])<=>false
     *  
     *  \result (e1=e2)<=>false
     */
    virtual Theorem bitvectorFalseRule(const Theorem& thm) = 0;

    /*! \param thm input theorem: (~e1[i]<=>e2[i])<=>true
     *  
     *  \result (e1!=e2)<=>true
     */
    virtual Theorem bitvectorTrueRule(const Theorem& thm) = 0;


    //! t1=t2 ==> AND_i(t1[i:i] = t2[i:i])
    /*!
     * \param e is a Expr(t1=t2)
     *
     * \param f is the resulting expression AND_i(t1[i:i] = t2[i:i])
     * is passed to the rule for efficiency.
     */
    virtual Theorem bitBlastEqnRule(const Expr& e, const Expr& f) = 0;
    //! t1/=t2 ==> OR_i(NOT t1[i]<=>t2[i])
    /*!
     * \param e is a Theorem(t1/=t2)
     *
     * \param f is the resulting expression OR_i(NOT t1[i]<=>t2[i]),
     * passed to the rule for efficiency.
     */
    virtual Theorem bitBlastDisEqnRule(const Theorem& e, const Expr& f) = 0;
    

    ////////////////////////////////////////////////////////////////////
    // Bitblasting and rewrite rules for Inequations
    ////////////////////////////////////////////////////////////////////    

    //! sign extend the input SX(e) appropriately
    virtual Theorem signExtendRule(const Expr& e) = 0;

    //! Pad the kids of BVLT/BVLE to make their length equal
    virtual Theorem padBVLTRule(const Expr& e, int len) = 0;

    //! Sign Extend the kids of BVSLT/BVSLE to make their length equal
    virtual Theorem padBVSLTRule(const Expr& e, int len) = 0; 
    
    /*! input: e0 <=(s) e1. output depends on whether the topbits(MSB) of
     *  e0 and e1 are constants. If they are constants then optimizations
     *  are done, otherwise the following rule is implemented.
     *
     *  e0 <=(s) e1 <==> (e0[n-1] AND NOT e1[n-1]) OR 
     *                   (e0[n-1] AND e1[n-1] AND e1[n-2:0] <= e0[n-2:0]) OR 
     *                   (NOT e0[n-1] AND NOT e1[n-1] AND e0[n-2:0] <= e1[n-2:0])
     */
    virtual Theorem signBVLTRule(const Expr& e, 
				 const Theorem& topBit0, 
				 const Theorem& topBit1) = 0;

    /*! NOT(e[0][0] = e[0][1]) <==> e[0][0] = ~e[0][1]
     */
    virtual Theorem notBVEQ1Rule(const Expr& e) = 0;

    /*! NOT(e[0][0] < e[0][1]) <==> (e[0][1] <= e[0][0]), 
     *  NOT(e[0][0] <= e[0][1]) <==> (e[0][1] < e[0][0])
     */    
    virtual Theorem notBVLTRule(const Expr& e) = 0;

    //! if(lhs==rhs) then we have (lhs < rhs <==> false),(lhs <= rhs <==> true)
    virtual Theorem lhsEqRhsIneqn(const Expr& e, int kind) = 0;


    virtual Theorem zeroLeq(const Expr& e) = 0;
    virtual Theorem bvConstIneqn(const Expr& e, int kind) = 0;

    virtual Theorem generalIneqn(const Expr& e, 
				 const Theorem& e0, 
				 const Theorem& e1, int kind) = 0;


    ////////////////////////////////////////////////////////////////////
    // Bitblast rules for terms
    ////////////////////////////////////////////////////////////////////

    // Input: |- BOOLEXTRACT(a,0) <=> bc_0, ... BOOLEXTRACT(a,n-1) <=> bc_(n-1)
    // where each bc_0 is TRUE or FALSE
    // Output: |- a = c
    // where c is an n-bit constant made from the values bc_0..bc_(n-1)
    virtual Theorem bitExtractAllToConstEq(std::vector<Theorem>& thms) = 0;

    //! t[i] ==> t[i:i] = 0bin1   or    NOT t[i] ==> t[i:i] = 0bin0
    /*! \param thm is a Theorem(t[i]) or Theorem(NOT t[i]), where t[i]
     * is BOOLEXTRACT(t, i).
     */
    virtual Theorem bitExtractToExtract(const Theorem& thm) = 0;

    //! t[i] <=> t[i:i][0]   (to use rewriter for simplifying t[i:i])
    virtual Theorem bitExtractRewrite(const Expr& x) = 0;

    /*! \param x is bitvector constant 
     *  \param i is extracted bitposition 
     *
     *  \result \f[ \frac{}{\mathrm{BOOLEXTRACT(x,i)} \iff
     *  \mathrm{TRUE}} \f], if bitposition has a 1; \f[
     *  \frac{}{\mathrm{BOOLEXTRACT(x,i)} \iff \mathrm{FALSE}} \f], if
     *  the bitposition has a 0
     */
    virtual Theorem bitExtractConstant(const Expr & x, int i)= 0;

    /*! \param x is bitvector binary concatenation
     *  \param i is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[m]}@q_{[n]})[i] \iff (q_{[n]})[i]}
     *  \f], where \f[ 0 \geq i \geq n-1 \f], another case of
     *  boolextract over concatenation is:
     *  \f[\frac{}{(t_{[m]}@q_{[n]})[i] \iff (t_{[m]})[i-n]} \f],
     *  where \f[ n \geq i \geq m+n-1 \f]
     */
    virtual Theorem bitExtractConcatenation(const Expr & x, 
					    int i)= 0; 

    /*! \param t is bitvector binary BVMULT. x[0] must be BVCONST
     *  \param i is extracted bitposition
     *
     *  \result bitblast of BVMULT
     */
    virtual Theorem bitExtractConstBVMult(const Expr& t, int i)= 0;

    /*! \param t : input1 is bitvector binary BVMULT. t[0] must not be BVCONST
     *  \param i : input2 is extracted bitposition
     *
     *  \result bitblast of BVMULT
     */
    virtual Theorem bitExtractBVMult(const Expr& t, int i) = 0;

    /*! \param x is bitvector extraction e[k:j]
     *  \param i is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[n]}[k:j])[i] \iff (t_{[n]})[i+j]}
     *  \f], where \f[ 0 \geq j \geq k < n, 0 \geq i < k-j \f]
     */
    virtual Theorem bitExtractExtraction(const Expr & x, int i)= 0;

    /*! \param t1 is vector of bitblasts of t, from bit i-1 to 0
     *  \param t2 is vector of bitblasts of q, from bit i-1 to 0
     *  \param bvPlusTerm is BVPLUS term: BVPLUS(n,t,q)
     *  \param i is extracted bitposition
     *
     *  \result The base case is: \f[
     *  \frac{}{(\mathrm{BVPLUS}(n,t,q))[0] \iff t[0] \oplus q[0]}
     *  \f], when \f[ 0 < i \leq n-1 \f], we have \f[
     *  \frac{}{(\mathrm{BVPLUS}(n,t,q))[i] \iff t[i] \oplus q[i]
     *  \oplus c(t,q,i)} \f], where c(t,q,i) is the carry generated
     *  by the addition of bits from 0 to i-1
     */
    virtual Theorem bitExtractBVPlus(const std::vector<Theorem>& t1, 
			     const std::vector<Theorem>& t2,
			     const Expr& bvPlusTerm, int i) = 0;


    virtual Theorem bitExtractBVPlusPreComputed(const Theorem& t1_i, 
						const Theorem& t2_i,
						const Expr& bvPlusTerm, 
						int bitPos,
						int precomputed) = 0;


    /*! \param bvPlusTerm : input1 is bvPlusTerm, a BVPLUS term with
     *  arity > 2
     *
     *  \result : output is iff-Theorem: bvPlusTerm <==> outputTerm,
     *  where outputTerm is an equivalent BINARY bvplus.
     */
    virtual Theorem bvPlusAssociativityRule(const Expr& bvPlusTerm)= 0;

    /*! \param x : input1 is bitwise NEGATION
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(\sim t_{[n]})[i] \iff \neg (t_{[n]}[i])}
     *  \f]
     */
    virtual Theorem bitExtractNot(const Expr & x, int i)= 0;

    /*! \param x : input1 is bitwise AND
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[n]} \& q_{[n]})[i] \iff (t_{[n]}[i]
     *  \wedge q_{[n]}[i])} \f]
     */
    virtual Theorem bitExtractAnd(const Expr & x, int i)= 0;   

    /*! \param x : input1 is bitwise OR
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[ \frac{}{(t_{[n]} \mid q_{[n]})[i] \iff (t_{[n]}[i]
     *  \vee q_{[n]}[i])} \f]
     */
    virtual Theorem bitExtractOr(const Expr & x, int i)= 0;   

    /*! \param x : input1 is bitvector FIXED SHIFT \f[ e_{[n]} \ll k \f]
     *  \param i : input2 is extracted bitposition
     *
     *  \result \f[\frac{}{(e_{[n]} \ll k)[i] \iff \mathrm{FALSE}}
     *  \f], if 0 <= i < k. however, if k <= i < n then, result is
     *  \f[\frac{}{(e_{[n]} \ll k)[i] \iff e_{[n]}[i]} \f]
     */
    virtual Theorem bitExtractFixedLeftShift(const Expr & x, 
					     int i)= 0;   

    virtual Theorem bitExtractFixedRightShift(const Expr & x, 
					      int i)= 0;   
    // BOOLEXTRACT(bvshl(t,s),i) <=> ((s = 0) AND BOOLEXTRACT(t,i)) OR
    //                               ((s = 1) AND BOOLEXTRACT(t,i-1)) OR ...
    //                               ((s = i) AND BOOLEXTRACT(t,0))
    virtual Theorem bitExtractBVSHL(const Expr & x, int i) = 0;
    
    // BOOLEXTRACT(bvlshr(t,s),i) <=> ((s = 0) AND BOOLEXTRACT(t,i)) OR
    //                                ((s = 1) AND BOOLEXTRACT(t,i+1)) OR ...
    //                                ((s = n-1-i) AND BOOLEXTRACT(t,n-1))
    virtual Theorem bitExtractBVLSHR(const Expr & x, int i) = 0;

    // BOOLEXTRACT(bvashr(t,s),i) <=> ((s = 0) AND BOOLEXTRACT(t,i)) OR
    //                                ((s = 1) AND BOOLEXTRACT(t,i+1)) OR ...
    //                                ((s >= n-1-i) AND BOOLEXTRACT(t,n-1))
    virtual Theorem bitExtractBVASHR(const Expr & x, int i) = 0;

    /*! \param e : input1 is bitvector term
     *  \param r : input2 is extracted bitposition
     *
     *  \result we check if r > bvlength(e). if yes, then return
     *  BOOLEXTRACT(e,r) <==> FALSE; else raise soundness
     *  exception. (Note: this rule is used in BVPLUS bitblast
     *  function)
     */
    virtual Theorem zeroPaddingRule(const Expr& e, int r)= 0;


    virtual Theorem bitExtractSXRule(const Expr& e, int i) = 0;

    ///////////////////////////////////////////////////////////////////
    /////  Special case rewrite rules
    ///////////////////////////////////////////////////////////////////

    //! c1=c2 <=> TRUE/FALSE (equality of constant bitvectors)
    virtual Theorem eqConst(const Expr& e) = 0;
    //! |- c1=c2 ==> |- AND(c1[i:i] = c2[i:i]) - expanding equalities into bits
    virtual Theorem eqToBits(const Theorem& eq) = 0;
    //! t<<n = c @ 0bin00...00, takes e == (t<<n)
    virtual Theorem leftShiftToConcat(const Expr& e) = 0;
    //! t<<n = c @ 0bin00...00, takes e == (t<<n)
    virtual Theorem constWidthLeftShiftToConcat(const Expr& e) = 0;
    //! t>>m = 0bin00...00 @ t[bvlength-1:m], takes e == (t>>n)
    virtual Theorem rightShiftToConcat(const Expr& e) = 0;
    //! BVSHL(t,c) = t[n-c,0] @ 0bin00...00
    virtual Theorem bvshlToConcat(const Expr& e) = 0;
    //! BVLSHR(t,c) = 0bin00...00 @ t[n-1,c]
    virtual Theorem bvlshrToConcat(const Expr& e) = 0;
    //! BVASHR(t,c) = SX(t[n-1,c], n-1)
    virtual Theorem bvashrToConcat(const Expr& e) = 0;
    //! a XOR b <=> (a & ~b) | (~a & b)
    virtual Theorem rewriteXOR(const Expr& e) = 0;
    //! a XNOR b <=> (~a & ~b) | (a & b)
    virtual Theorem rewriteXNOR(const Expr& e) = 0;
    //! a NAND b <=> ~(a & b)
    virtual Theorem rewriteNAND(const Expr& e) = 0;
    //! a NOR b <=> ~(a | b)
    virtual Theorem rewriteNOR(const Expr& e) = 0;
    //! BVCOMP(a,b) <=> ITE(a=b,0bin1,0bin0)
    virtual Theorem rewriteBVCOMP(const Expr& e) = 0;
    //! a - b <=> a + (-b)
    virtual Theorem rewriteBVSub(const Expr& e) = 0;
    //! k*t = BVPLUS(n, <sum of shifts of t>) -- translation of k*t to BVPLUS
    /*! If k = 2^m, return k*t = t\@0...0 */
    virtual Theorem constMultToPlus(const Expr& e) = 0;
    //! 0bin0...0 @ BVPLUS(n, args) = BVPLUS(n+k, args)
    /*! provided that m+ceil(log2(l)) <= n, where k is the size of the
     * 0bin0...0, m is the max. length of each argument, and l is the
     * number of arguments.
     */
    virtual Theorem bvplusZeroConcatRule(const Expr& e) = 0;


    ///////////////////////////////////////////////////////////////////
    /////  Bvplus Normal Form rules
    ///////////////////////////////////////////////////////////////////
    virtual Theorem zeroCoeffBVMult(const Expr& e)=0;
    virtual Theorem oneCoeffBVMult(const Expr& e)=0; 
    virtual Theorem flipBVMult(const Expr& e) = 0;
    //! Make args the same length as the result (zero-extend)
    virtual Theorem padBVPlus(const Expr& e) = 0;
    //! Make args the same length as the result (zero-extend)
    virtual Theorem padBVMult(const Expr& e) = 0;
    virtual Theorem bvConstMultAssocRule(const Expr& e) = 0;
    virtual Theorem bvMultAssocRule(const Expr& e) = 0;
    virtual Theorem bvMultDistRule(const Expr& e) = 0;
    virtual Theorem flattenBVPlus(const Expr& e) = 0;
    virtual Theorem combineLikeTermsRule(const Expr& e) = 0;
    virtual Theorem lhsMinusRhsRule(const Expr& e) = 0;
    //! (x *[n] y)[m:k] = (x *[m+1] y)[m:k], where m < n
    virtual Theorem extractBVMult(const Expr& e) = 0;
    //! (x +[n] y)[m:k] = (x +[m+1] y)[m:k], where m < n
    virtual Theorem extractBVPlus(const Expr& e) = 0;
    //! ite(c,t1,t2)[i:j] <=> ite(c,t1[i:j],t2[i:j])
    virtual Theorem iteExtractRule(const Expr& e) = 0;
    //! ~ite(c,t1,t2) <=> ite(c,~t1,~t2)
    virtual Theorem iteBVnegRule(const Expr& e) = 0;

    virtual Theorem bvuminusBVConst(const Expr& e) = 0;
    virtual Theorem bvuminusBVMult(const Expr& e) = 0;
    virtual Theorem bvuminusBVUminus(const Expr& e) = 0;
    virtual Theorem bvuminusVar(const Expr& e) = 0;
    virtual Theorem bvmultBVUminus(const Expr& e) = 0;
    //! -t <==> ~t+1
    virtual Theorem bvuminusToBVPlus(const Expr& e) = 0;
    //! -(c1*t1+...+cn*tn) <==> (-(c1*t1)+...+-(cn*tn))
    virtual Theorem bvuminusBVPlus(const Expr& e) = 0;



    ///////////////////////////////////////////////////////////////////
    /////  Concatenation Normal Form rules
    ///////////////////////////////////////////////////////////////////

    // Extraction rules

    //! c1[i:j] = c  (extraction from a constant bitvector)
    virtual Theorem extractConst(const Expr& e) = 0;
    //! t[n-1:0] = t  for n-bit t
    virtual Theorem extractWhole(const Expr& e) = 0;
    //! t[i:j][k:l] = t[k+j:l+j]  (eliminate double extraction)
    virtual Theorem extractExtract(const Expr& e) = 0;
    //! (t1 @ t2)[i:j] = t1[...] @ t2[...]  (push extraction through concat)
    virtual Theorem extractConcat(const Expr& e) = 0;
    //! (t1 & t2)[i:j] = t1[i:j] & t2[i:j]  (push extraction through OR)
    virtual Theorem extractAnd(const Expr& e) = 0;
    //! (t1 | t2)[i:j] = t1[i:j] | t2[i:j]  (push extraction through AND)
    virtual Theorem extractOr(const Expr& e) = 0;
    //! (~t)[i:j] = ~(t[i:j]) (push extraction through NEG)
    virtual Theorem extractNeg(const Expr& e) = 0;
    //! Auxiliary function: (t1 op t2)[i:j] = t1[i:j] op t2[i:j] 
    virtual Theorem extractBitwise(const Expr& e, 
				   int kind, const std::string& name) = 0;

    // Negation rules

    //! ~c1 = c  (bit-wise negation of a constant bitvector)
    virtual Theorem negConst(const Expr& e) = 0;
    //! ~(t1\@...\@tn) = (~t1)\@...\@(~tn) -- push negation through concat
    virtual Theorem negConcat(const Expr& e) = 0;
    //! ~(~t) = t  -- eliminate double negation
    virtual Theorem negNeg(const Expr& e) = 0;
    //! ~t = -1*t + 1 -- eliminate negation
    virtual Theorem negElim(const Expr& e) = 0;
    //! ~(t1 & t2) <=> ~t1 | ~t2 -- DeMorgan's Laws
    virtual Theorem negBVand(const Expr& e) = 0;
    //! ~(t1 | t2) <=> ~t1 & ~t2 -- DeMorgan's Laws
    virtual Theorem negBVor(const Expr& e) = 0;
    //! ~(t1 xor t2) = ~t1 xor t2
    virtual Theorem negBVxor(const Expr& e) = 0;
    //! ~(t1 xnor t2) = t1 xor t2
    virtual Theorem negBVxnor(const Expr& e) = 0;

    // Bit-wise AND rules
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
    virtual Theorem andConst(const Expr& e, const std::vector<int>& idxs) = 0;
    //! 0bin0...0 & t = 0bin0...0  -- bit-wise AND with zero bitvector
    /*! \param e is the bit-wise AND expr
     *  \param idx is the index of the zero bitvector
     */
    virtual Theorem andZero(const Expr& e, int idx) = 0;
    //! 0bin1...1 & t = t  -- bit-wise AND with bitvector of 1's
    /*! \param e is the bit-wise AND expr
     *  \param idxs is a vector of indices of the bitvectors of 1's
     *  which will be dropped
     */
    virtual Theorem andOne(const Expr& e, const std::vector<int> idxs) = 0;
    //! ... & (t1\@...\@tk) & ... = (...& t1 &...)\@...\@(...& tk &...)
    /*!
     * Lifts concatenation to the top of bit-wise AND.  Takes the
     * bit-wise AND expression 'e' and the index 'i' of the
     * concatenation.
     */
    virtual Theorem andConcat(const Expr& e, int idx) = 0;
    //! (t1 & (t2 & t3) & t4) = t1 & t2 & t3 & t4  -- flatten bit-wise AND
    /*! Also reorders the terms according to a fixed total ordering */
    virtual Theorem andFlatten(const Expr& e) = 0;

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
    virtual Theorem orConst(const Expr& e, const std::vector<int>& idxs) = 0;
    //! 0bin1...1 | t = 0bin1...1  -- bit-wise OR with bitvector of 1's
    /*! \param e is the bit-wise OR expr
     *  \param idx is the index of the bitvector of 1's
     */
    virtual Theorem orOne(const Expr& e, int idx) = 0;
    //! 0bin0...0 | t = t  -- bit-wise OR with bitvector of 0's
    /*! \param e is the bit-wise OR expr
     *  \param idxs is a vector of indices of the bitvectors of 0's
     *  which will be dropped
     */
    virtual Theorem orZero(const Expr& e, const std::vector<int> idxs) = 0;
    //! ... | (t1\@...\@tk) | ... = (...| t1 |...)\@...\@(...| tk |...)
    /*!
     * Lifts concatenation to the top of bit-wise OR.  Takes the
     * bit-wise OR expression 'e' and the index 'i' of the
     * concatenation.
     */
    virtual Theorem orConcat(const Expr& e, int idx) = 0;
    //! (t1 | (t2 | t3) | t4) = t1 | t2 | t3 | t4  -- flatten bit-wise OR
    /*! Also reorders the terms according to a fixed total ordering */
    virtual Theorem orFlatten(const Expr& e) = 0;

    // Concatenation rules

    //! c1\@c2\@...\@cn = c  (concatenation of constant bitvectors)
    virtual Theorem concatConst(const Expr& e) = 0;
    //! Flatten one level of nested concatenation, e.g.: x\@(y\@z)\@w = x\@y\@z\@w
    virtual Theorem concatFlatten(const Expr& e) = 0;
    //! Merge n-ary concat. of adjacent extractions: x[15:8]\@x[7:0] = x[15:0]
    virtual Theorem concatMergeExtract(const Expr& e) = 0;

    ///////////////////////////////////////////////////////////////////
    /////  Modulo arithmetic rules
    ///////////////////////////////////////////////////////////////////

    //! BVPLUS(n, c1,c2,...,cn) = c  (bit-vector plus of constant bitvectors)
    virtual Theorem bvplusConst(const Expr& e) = 0;
    /*! @brief n*c1 = c, where n >= 0 (multiplication of a constant
     *  bitvector by a non-negative constant) */
    virtual Theorem bvmultConst(const Expr& e) = 0;

    ///////////////////////////////////////////////////////////////////
    /////  Type predicate rules
    ///////////////////////////////////////////////////////////////////

    //! |- t=0 OR t=1  for any 1-bit bitvector t
    virtual Theorem typePredBit(const Expr& e) = 0;
    //! Expand the type predicate wrapper (compute the actual type predicate)
    virtual Theorem expandTypePred(const Theorem& tp) = 0;

    /*Beginning of Lorenzo PLatania's methods*/
    
    //    virtual Theorem multiply_coeff( Rational mult_inv, const Expr& e)=0;

    //! isolate a variable with coefficient = 1 on the Lhs of an
    //equality expression
    virtual Theorem isolate_var(const Expr& e)=0;

    // BVPLUS(N, a@b, y) = BVPLUS(N-n,a,BVPLUS(N,b,y)[N-1:n])@BVPLUS(n,b,y)
    // where n = BVSize(b), a != 0
    virtual Theorem liftConcatBVMult(const Expr& e)=0;

    //! canonize BVMult expressions in order to get one coefficient
    //multiplying the variable(s) in the expression
    virtual Theorem canonBVMult( const Expr& e )=0;

    // BVPLUS(N, a@b, y) = BVPLUS(N-n,a,BVPLUS(N,b,y)[N-1:n])@BVPLUS(n,b,y)
    // where n = BVSize(b)
    virtual Theorem liftConcatBVPlus(const Expr& e)=0;

    //! canonize BVPlus expressions in order to get just one
    //coefficient multiplying each variable in the expression
    virtual Theorem canonBVPlus( const Expr& e )=0;
    virtual Theorem canonBVUMinus( const Expr& e )=0;
    // puts the equation in the form \sum a_i*x_i = c
    virtual Theorem canonBVEQ( const Expr& e )=0;

    //! apply the distributive rule on the BVMULT expression e
    virtual Theorem distributive_rule( const Expr& e )=0;
    //    virtual Theorem BVMultConstTerm( const Expr& e1, const Expr& e2)=0;
    // recursively reorder subterms in a BVMULT term
    virtual Theorem BVMult_order_subterms( const Expr& e ) = 0;
    // rewrites the equation in the form 0 = Expr
    // this is needed for TheoryBitvector::solve
    virtual Theorem MarkNonSolvableEq( const Expr& e) = 0;
    /*End of Lorenzo PLatania's methods*/

    // rewrite BVZEROEXTEND into CONCAT
    virtual Theorem zeroExtendRule(const Expr& e) = 0;
    // rewrite BVREPEAT into CONCAT
    virtual Theorem repeatRule(const Expr& e) = 0;
    // rewrite BVROTL into CONCAT
    virtual Theorem rotlRule(const Expr& e) = 0;
    // rewrite BVROTR into CONCAT
    virtual Theorem rotrRule(const Expr& e) = 0;

  }; // end of class BitvectorProofRules
} // end of namespace CVC3

#endif
