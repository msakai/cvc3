/*****************************************************************************/
/*!
 * \file theory_bitvector.h
 * 
 * Author: Vijay Ganesh
 * 
 * Created: Wed May 05 18:34:55 PDT 2004
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

#ifndef _cvc3__include__theory_bitvector_h_
#define _cvc3__include__theory_bitvector_h_

#include "theory_core.h"
#include "statistics.h"

namespace CVC3 {

  class VCL;
  class BitvectorProofRules;
  
  typedef enum { //some new BV kinds
    BITVECTOR = 8000,
    BVCONST,
    HEXBVCONST,
    CONCAT,
    BVOR,
    BVAND,
    BVNEG,
    BVXOR,
    BVNAND,
    BVNOR,
    BVXNOR,
    EXTRACT,
    LEFTSHIFT,
    CONST_WIDTH_LEFTSHIFT,
    RIGHTSHIFT,
    VARSHIFT,
    BVPLUS,
    BVSUB,
    BVUMINUS,
    BVMULT,
    BOOLEXTRACT,
    BVLT,
    BVLE,
    BVGT,
    BVGE,
    SBVLT,
    SBVLE,
    SBVGT,
    SBVGE,
    SX,
    SRIGHTSHIFT,
    INTTOBV,
    BVTOINT,
    // A wrapper for delaying the construction of type predicates
    BVTYPEPRED,
    // Internal kind for a bitvector operator
    BVPARAMOP
  } BVKinds;

/*****************************************************************************/
/*!
 *\class TheoryBitvector
 *\ingroup Theories
 *\brief Theory of bitvectors of known length \
 * (operations include: @,[i:j],[i],+,.,BVAND,BVNEG)
 *
 * Author: Vijay Ganesh
 *
 * Created:Wed May  5 15:35:07 PDT 2004
 */
/*****************************************************************************/
class TheoryBitvector :public Theory {
  BitvectorProofRules* d_rules;
  //! MemoryManager index for BVConstExpr subclass
  size_t d_bvConstExprIndex;
  size_t d_bvPlusExprIndex;
  size_t d_bvParameterExprIndex;
  size_t d_bvTypePredExprIndex;

  //! counts delayed asserted equalities
  StatCounter d_bvDelayEq;
  //! counts asserted equalities
  StatCounter d_bvAssertEq;
  //! counts delayed asserted disequalities
  StatCounter d_bvDelayDiseq;
  //! counts asserted disequalities
  StatCounter d_bvAssertDiseq;
  //! counts type predicates
  StatCounter d_bvTypePreds;
  //! counts delayed type predicates
  StatCounter d_bvDelayTypePreds;
  //! counts bitblasted equalities
  StatCounter d_bvBitBlastEq;
  //! counts bitblasted disequalities
  StatCounter d_bvBitBlastDiseq;


  //! boolean on the fly rewrite flag
  const bool* d_booleanRWFlag;
  //! bool extract cache flag
  const bool* d_boolExtractCacheFlag;
  //! flag which indicates that all arithmetic is 32 bit with no overflow
  const bool* d_bv32Flag;
  //! Command line flag: rewrite bitvector expressions
  const bool* d_rewriteFlag;
  //! Command line flag: concatenation normal form rewrite bitvector expressions
  const bool* d_concatRewriteFlag;
  //! Command line flag: bvplus normal form rewrite bitvector expressions
  const bool* d_bvplusRewriteFlag;
  //! Commant line flag: rewrite while bit-blasting
  const bool* d_rwBitBlastFlag;
  //! Commant line flag: bit-blast equalities in CNF converter
  const bool* d_cnfBitBlastFlag;
  //! Command line flag: enable lhs-minus-rhs-rule for lhs=rhs
  const bool* d_lhsMinusRhsFlag;
  //! Command line flag: enable pushnegation
  const bool* d_pushNegationFlag;

  //! Cache for storing the results of the bitBlastTerm function
  CDMap<Expr,Theorem> d_bitvecCache;

  //! Cache for pushNegation(). it is ok that this is cache is
  //ExprMap. it is cleared for each call of pushNegation. Does not add
  //value across calls of pushNegation
  ExprMap<Theorem> d_pushNegCache;

  //! Backtracking queue for equalities (to delay them till checkSat() call)
  CDList<Theorem> d_eq;
  //! Pointer to the next unasserted equality in d_eq
  CDO<size_t> d_eqIdx;
  //! Pointer to the next equality in d_eq which is not bit-blasted yet
  CDO<size_t> d_eqBlastIdx;
  //! Backtracking queue for disequalities (to delay them till checkSat() call)
  CDList<Theorem> d_diseq;
  //! Pointer to the next unasserted disequality in d_diseq
  CDO<size_t> d_diseqIdx;
  //! Database of stale bit-expansions for update()
  CDMap<Expr,bool> d_staleDB;
  //! Backtracking queue for TCCs on individual bits
  CDList<Theorem> d_tccs;
  //! Pointer to the next unasserted TCC in d_tccs
  CDO<size_t> d_tccsIdx;
  //! Backtracking database of subterms of shared terms
  CDMap<Expr,Expr> d_sharedSubterms;
  //! Backtracking database of subterms of shared terms
  CDList<Expr> d_sharedSubtermsList;
  //! Cache for typePredicates of non shared terms
  CDMap<Expr, Theorem> d_typePredsCache;
  //! cache for rewriteBoolean
  //CDMap<Expr, Theorem> d_rewriteBooleanCache;
  
  //! Constant 1-bit bit-vector 0bin0
  Expr d_bvZero;
  //! Constant 1-bit bit-vector 0bin0
  Expr d_bvOne;
  //! Return cached constant 0bin0
  const Expr& bvZero() const { return d_bvZero; }
  //! Return cached constant 0bin1
  const Expr& bvOne() const { return d_bvOne; }

  //! Max size of any bitvector we've seen
  int d_maxLength;

  //! Used in checkSat
  CDO<unsigned> d_index1;

  //! functions which implement the DP strategy for bitblasting
  Theorem bitBlastEqn(const Expr& e);
  //! functions which implement the DP strategy for bitblasting
  Theorem bitBlastDisEqn(const Theorem& e);
  public:
  //! functions which implement the DP strategy for bitblasting
  Theorem bitBlastTerm(const Expr& t, int bitPosition);
  private:
  //! function which implements the DP strtagey to bitblast Inequations
  Theorem bitBlastIneqn(const Expr& e);

  //! strategy fucntions for BVPLUS NORMAL FORM
  Theorem padBVPlus(const Expr& e);
  //! strategy fucntions for BVPLUS NORMAL FORM
  Theorem flattenBVPlus(const Expr& e);
  
  //! Implementation of the concatenation normal form
  Theorem normalizeConcat(const Expr& e, bool useFind);
  //! Implementation of the n-bit arithmetic normal form
  Theorem normalizeBVArith(const Expr& e, bool useFind);
  //! Helper method for composing normalizations
  Theorem normalizeConcat(const Theorem& t, bool useFind) {
    return transitivityRule(t, normalizeConcat(t.getRHS(), useFind));
  }
  //! Helper method for composing normalizations
  Theorem normalizeBVArith(const Theorem& t, bool useFind) {
    return transitivityRule(t, normalizeBVArith(t.getRHS(), useFind));
  }

  Theorem signExtendBVLT(const Expr& e, int len, bool useFind);

  Theorem pushNegationRec(const Theorem& thm, bool neg);
  Theorem pushNegation(const Expr& e);

  //! Top down simplifier
  virtual Theorem simplifyOp(const Expr& e);


  //! Internal rewrite method for constants
  Theorem rewriteConst(const Expr& e);
  //! Internal rewrite method
  Theorem rewriteBV(const Expr& e, bool useFind);
  //! Rewrite children 'n' levels down (n==1 means "only the top level")
  Theorem rewriteBV(const Expr& e, int n, bool useFind);
  //! Rewrite children 'n' levels down (n==1 means "only the top level")
  Theorem rewriteBV(const Theorem& t, int n, bool useFind) {
    return transitivityRule(t, rewriteBV(t.getRHS(), n, useFind));
  }
  //! Internal rewrite method (implements the actual rewrites)
  Theorem rewriteBV(const Expr& e, ExprMap<Theorem>& cache, bool useFind);
  //! Rewrite children 'n' levels down (n==1 means "only the top level")
  Theorem rewriteBV(const Expr& e, ExprMap<Theorem>& cache, int n,
		    bool useFind);
  //! Rewrite children 'n' levels down (n==1 means "only the top level")
  Theorem rewriteBV(const Theorem& t, ExprMap<Theorem>& cache, int n,
		    bool useFind) {
    return transitivityRule(t, rewriteBV(t.getRHS(), cache, n, useFind));
  }

  //! rewrite input boolean expression e to a simpler form
  Theorem rewriteBoolean(const Expr& e);
  
  //! Setup the NotifyList mechanism for the Expr e
  void setupExpr(const Expr& e);
public:
  TheoryBitvector(TheoryCore* core);
  ~TheoryBitvector();


  ExprMap<Expr> d_bvPlusCarryCacheLeftBV;
  ExprMap<Expr> d_bvPlusCarryCacheRightBV;

  // Trusted method that creates the proof rules class (used in constructor).
  // Implemented in bitvector_theorem_producer.cpp
  BitvectorProofRules* createProofRules();
  Theorem pushNegationRec(const Expr& e, bool neg);

  // Theory interface
  void addSharedTerm(const Expr& e);
  void assertFact(const Theorem& e);
  void assertTypePred(const Expr& e, const Theorem& pred);
  void checkSat(bool fullEffort);
  Theorem rewrite(const Expr& e);
  Theorem rewriteAtomic(const Expr& e);
  void setup(const Expr& e);
  void update(const Theorem& e, const Expr& d);
  Theorem solve(const Theorem& e);
  void checkType(const Expr& e);
  void computeType(const Expr& e);
  void computeModelTerm(const Expr& e, std::vector<Expr>& v);
  void computeModel(const Expr& e, std::vector<Expr>& vars);
  Expr computeTypePred(const Type& t, const Expr& e);
  Expr computeTCC(const Expr& e);
  ExprStream& print(ExprStream& os, const Expr& e);
  Expr parseExprOp(const Expr& e);

  //helper functions
  Expr rat(const Rational& r) { return getEM()->newRatExpr(r); }
  //!pads e to be of length len
  Expr pad(int len, const Expr& e);

  bool comparebv(const Expr& e1, const Expr& e2);

  //! Return the number of bits in the bitvector expression
  int BVSize(const Expr& e);

  //helper functions: functions to construct exprs
  Type newBitvectorType(int i) 
    { return newBitvectorTypeExpr(i); }
  Expr newBitvectorTypePred(const Type& t, const Expr& e);
  Expr newBitvectorTypeExpr(int i);

  Expr newBVAndExpr(const Expr& t1, const Expr& t2);
  Expr newBVAndExpr(const std::vector<Expr>& kids);
  Expr newBVNandExpr(const Expr& t1, const Expr& t2);
  Expr newBVNandExpr(const std::vector<Expr>& kids);

  Expr newBVOrExpr(const Expr& t1, const Expr& t2);
  Expr newBVOrExpr(const std::vector<Expr>& kids);
  Expr newBVNorExpr(const Expr& t1, const Expr& t2);
  Expr newBVNorExpr(const std::vector<Expr>& kids);

  Expr newBVXorExpr(const Expr& t1, const Expr& t2);
  Expr newBVXorExpr(const std::vector<Expr>& kids);
  Expr newBVXnorExpr(const Expr& t1, const Expr& t2);
  Expr newBVXnorExpr(const std::vector<Expr>& kids);
  
  Expr newBVLTExpr(const Expr& t1, const Expr& t2);
  Expr newBVLEExpr(const Expr& t1, const Expr& t2);  
  Expr newSXExpr(const Expr& t1, int len);
  Expr newSBVLTExpr(const Expr& t1, const Expr& t2);
  Expr newSBVLEExpr(const Expr& t1, const Expr& t2);

  Expr newBVNegExpr(const Expr& t1);
  Expr newBVUminusExpr(const Expr& t1);
  Expr newBoolExtractExpr(const Expr& t1, int r);
  Expr newFixedLeftShiftExpr(const Expr& t1, int r);
  Expr newFixedConstWidthLeftShiftExpr(const Expr& t1, int r);
  Expr newFixedRightShiftExpr(const Expr& t1, int r);
  Expr newConcatExpr(const Expr& t1, const Expr& t2);
  Expr newConcatExpr(const Expr& t1, const Expr& t2, const Expr& t3);
  Expr newConcatExpr(const std::vector<Expr>& kids);
  Expr newBVConstExpr(const std::string& s, int base = 2);
  Expr newBVConstExpr(const std::vector<bool>& bits);
  // Construct BVCONST of length 'len', or the min. needed length when len=0.
  Expr newBVConstExpr(const Rational& r, int len = 0);
  Expr newBVZeroString(int r);
  Expr newBVOneString(int r);
  //! hi and low are bit indices
  Expr newBVExtractExpr(const Expr& e, 
			int hi, int low);
  //! 'numbits' is the number of bits in the result
  Expr newBVPlusExpr(int numbits, const std::vector<Expr>& k);
  //! accepts an integer, r, and bitvector, t1, and returns r.t1
  Expr newBVMultExpr(int bvLength,
		     const Expr& t1, const Expr& t2);

  // Accessors for expression parameters
  int getBitvectorTypeParam(const Expr& e);
  int getBitvectorTypeParam(const Type& t) 
    { return getBitvectorTypeParam(t.getExpr()); }
  Type getTypePredType(const Expr& tp);
  const Expr& getTypePredExpr(const Expr& tp);
  int getSXIndex(const Expr& e);
  int getBoolExtractIndex(const Expr& e);
  int getFixedLeftShiftParam(const Expr& e);
  int getFixedRightShiftParam(const Expr& e);
  int getExtractHi(const Expr& e);
  int getExtractLow(const Expr& e);
  int getBVPlusParam(const Expr& e);
  int getBVMultParam(const Expr& e);

  unsigned getBVConstSize(const Expr& e);
  bool getBVConstValue(const Expr& e, int i);
  //!computes the integer value of a bitvector constant
  Rational computeBVConst(const Expr& e);
  //!computes the integer value of ~c+1 or BVUMINUS(c)
  Rational computeNegBVConst(const Expr& e);
 
  //FIXME: do the same for INTTOBV, BVTOINT

  int getMaxSize() { return d_maxLength; }

}; //end of class TheoryBitvector

  //!computes the integer value of a bitvector constant
  Rational computeBVConst(const Expr& e);

}//end of namespace CVC3
#endif
