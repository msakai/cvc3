/*****************************************************************************/
/*!
 * \file theory_arith.h
 * 
 * Author: Clark Barrett
 * 
 * Created: Fri Jan 17 18:34:55 2003
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

#ifndef _cvc3__include__theory_arith_h_
#define _cvc3__include__theory_arith_h_

#include "theory.h"
#include "cdmap.h"

namespace CVC3 {

  class ArithProofRules;

  typedef enum {
    REAL = 3000,
    INT,
    SUBRANGE,

    UMINUS,
    PLUS,
    MINUS,
    MULT,
    DIVIDE,
    POW,
    INTDIV,
    MOD,
    LT,
    LE,
    GT,
    GE,
    IS_INTEGER,
    NEGINF,
    POSINF,
    DARK_SHADOW,
    GRAY_SHADOW,

    REAL_CONST // wrapper around constants to indicate that they should be real
  } ArithKinds;

/*****************************************************************************/
/*!
 *\class TheoryArith
 *\ingroup Theories
 *\brief This theory handles basic linear arithmetic.
 *
 * Author: Clark Barrett
 *
 * Created: Sat Feb  8 14:44:32 2003
 */
/*****************************************************************************/
class TheoryArith :public Theory {
  Type d_realType;
  Type d_intType;
  CDList<Theorem> d_diseq;  // For concrete model generation
  CDO<size_t> d_diseqIdx; // Index to the next unprocessed disequality
  ArithProofRules* d_rules;
  CDO<bool> d_inModelCreation;

  //! Data class for the strongest free constant in separation inqualities
  class FreeConst {
  private:
    Rational d_r;
    bool d_strict;
  public:
    FreeConst() { }
    FreeConst(const Rational& r, bool strict): d_r(r), d_strict(strict) { }
    const Rational& getConst() const { return d_r; }
    bool strict() const { return d_strict; }
  };
  //! Printing
  friend std::ostream& operator<<(std::ostream& os, const FreeConst& fc);
  //! Private class for an inequality in the Fourier-Motzkin database
  class Ineq {
  private:
    Theorem d_ineq; //!< The inequality
    bool d_rhs; //!< Var is isolated on the RHS
    const FreeConst* d_const; //!< The max/min const for subsumption check
    //! Default constructor is disabled
    Ineq() { }
  public:
    //! Initial constructor.  'r' is taken from the subsumption database.
    Ineq(const Theorem& ineq, bool varOnRHS, const FreeConst& c):
      d_ineq(ineq), d_rhs(varOnRHS), d_const(&c) { }
    //! Get the inequality
    const Theorem& ineq() const { return d_ineq; }
    //! Get the max/min constant
    const FreeConst& getConst() const { return *d_const; }
    //! Flag whether var is isolated on the RHS
    bool varOnRHS() const { return d_rhs; }
    //! Flag whether var is isolated on the LHS
    bool varOnLHS() const { return !d_rhs; }
    //! Auto-cast to Theorem
    operator Theorem() const { return d_ineq; }
  };
  //! Printing
  friend std::ostream& operator<<(std::ostream& os, const Ineq& ineq);
  //! Database of inequalities with a variable isolated on the right
  ExprMap<CDList<Ineq> *> d_inequalitiesRightDB;
  //! Database of inequalities with a variable isolated on the left
  ExprMap<CDList<Ineq> *> d_inequalitiesLeftDB;
  //! Mapping of inequalities to the largest/smallest free constant
  /*! The Expr is the original inequality with the free constant
   * removed and inequality converted to non-strict (for indexing
   * purposes).  I.e. ax<c+t becomes ax<=t.  This inequality is mapped
   * to a pair<c,strict>, the smallest (largest for c+t<ax) constant
   * among inequalities with the same 'a', 'x', and 't', and a boolean
   * flag indicating whether the strongest inequality is strict.
   */
  CDMap<Expr, FreeConst> d_freeConstDB;
  // Input buffer to store the incoming inequalities
  CDList<Theorem> d_buffer; //!< Buffer of input inequalities
  CDO<size_t> d_bufferIdx; //!< Buffer index of the next unprocessed inequality
  const int* d_bufferThres; //!< Threshold when the buffer must be processed
  // Statistics for the variables
  /*! @brief Mapping of a variable to the number of inequalities where
    the variable would be isolated on the right */
  CDMap<Expr, int> d_countRight;
  /*! @brief Mapping of a variable to the number of inequalities where
    the variable would be isolated on the left */
  CDMap<Expr, int> d_countLeft;
  //! Set of shared terms (for counterexample generation)
  CDMap<Expr, bool> d_sharedTerms;
  //! Set of shared integer variables (i-leaves)
  CDMap<Expr, bool> d_sharedVars;
  //Directed Acyclic Graph representing partial variable ordering for
  //variable projection over inequalities.
  class VarOrderGraph {
    ExprMap<std::vector<Expr> > d_edges;
    ExprMap<bool> d_cache;
    bool dfs(const Expr& e1, const Expr& e2);
  public:
    void addEdge(const Expr& e1, const Expr& e2);
    //returns true if e1 < e2, false otherwise.
    bool lessThan(const Expr& e1, const Expr& e2);
    //selects those variables which are largest and incomparable among
    //v1 and puts it into v2
    void selectLargest(const std::vector<Expr>& v1, std::vector<Expr>& v2);
    //selects those variables which are smallest and incomparable among
    //v1, removes them from v1 and  puts them into v2. 
    void selectSmallest( std::vector<Expr>& v1, std::vector<Expr>& v2);

  };
  
  VarOrderGraph d_graph;

  // Private methods
  //! Check the term t for integrality.  
  /*! \return a theorem of IS_INTEGER(t) or Null. */
  Theorem isIntegerThm(const Expr& e);
  //! A helper method for isIntegerThm()
  /*! Check if IS_INTEGER(e) is easily derivable from the given 'thm' */
  Theorem isIntegerDerive(const Expr& isIntE, const Theorem& thm);
  //! Check the term t for integrality (return bool)
  bool isInteger(const Expr& e) { return !(isIntegerThm(e).isNull()); }
  //! Extract the free constant from an inequality
  const Rational& freeConstIneq(const Expr& ineq, bool varOnRHS);
  //! Update the free constant subsumption database with new inequality
  /*! \return a reference to the max/min constant.
   *
   * Also, sets 'subsumed' argument to true if the inequality is
   * subsumed by an existing inequality.
   */
  const FreeConst& updateSubsumptionDB(const Expr& ineq, bool varOnRHS,
				      bool& subsumed);
  //! Check if the kids of e are fully simplified and canonized (for debugging)
  bool kidsCanonical(const Expr& e);
  //! Canonize the expression e, assuming all children are canonical
  Theorem canon(const Expr& e);
  //! Canonize the expression e recursively
  Theorem canonRec(const Expr& e);
  /*! @brief Composition of canon(const Expr&) by transitivity: take e0 = e1,
   * canonize e1 to e2, return e0 = e2. */
  Theorem canon(const Theorem& thm) {
    return transitivityRule(thm, canon(thm.getRHS()));
  }
  /*! @brief Canonize and reduce e w.r.t. union-find database; assume
   * all children are canonical */
  Theorem canonSimplify(const Expr& e);
  /*! @brief Composition of canonSimplify(const Expr&) by
   * transitivity: take e0 = e1, canonize and simplify e1 to e2,
   * return e0 = e2. */
  Theorem canonSimplify(const Theorem& thm) {
    return transitivityRule(thm, canonSimplify(thm.getRHS()));
  }
  //! Canonize predicate (x = y, x < y, etc.)
  Theorem canonPred(const Theorem& thm);
  //! Canonize predicate like canonPred except that the input theorem
  //! is an equivalent transformation.
  Theorem canonPredEquiv(const Theorem& thm);
  //! Solve an equation and return an equivalent Theorem in the solved form
  Theorem doSolve(const Theorem& e);
  //! takes in a conjunction equivalence Thm and canonizes it.
  Theorem canonConjunctionEquiv(const Theorem& thm);
  //! picks the monomial with the smallest abs(coeff) from the input
  //integer equation.
  Expr pickIntEqMonomial(const Expr& right);
  //! processes equalities with 1 or more vars of type REAL
  Theorem processRealEq(const Theorem& eqn);
  //! processes equalities whose vars are all of type INT
  Theorem processIntEq(const Theorem& eqn);
  //! One step of INT equality processing (aux. method for processIntEq())
  Theorem processSimpleIntEq(const Theorem& eqn);
  //! Process inequalities in the buffer
  void processBuffer();
  //! Take an inequality and isolate a variable
  Theorem isolateVariable(const Theorem& inputThm, bool& e1);
  //! Update the statistics counters for the variable with a coeff. c
  void updateStats(const Rational& c, const Expr& var);
  //! Update the statistics counters for the monomial
  void updateStats(const Expr& monomial);
  //! Add an inequality to the input buffer.  See also d_buffer
  void addToBuffer(const Theorem& thm);
  /*! @brief Given a canonized term, compute a factor to make all
    coefficients integer and relatively prime */
  Expr computeNormalFactor(const Expr& rhs);
  //! Normalize an equation (make all coefficients rel. prime integers)
  Theorem normalize(const Expr& e);
  //! Normalize an equation (make all coefficients rel. prime integers)
  /*! accepts a rewrite theorem over eqn|ineqn and normalizes it
   *  and returns a theorem to that effect.
   */
  Theorem normalize(const Theorem& thm);
  Expr pickMonomial(const Expr& right);
 public: // ArithTheoremProducer needs this function, so make it public
  //! Separate monomial e = c*p1*...*pn into c and 1*p1*...*pn
  void separateMonomial(const Expr& e, Expr& c, Expr& var);
 private:
  bool lessThanVar(const Expr& isolatedVar, const Expr& var2);
  //! Check if the term expression is "stale"
  bool isStale(const Expr& e);
  //! Check if the inequality is "stale" or subsumed
  bool isStale(const Ineq& ineq);
  void projectInequalities(const Theorem& theInequality,bool isolatedVarOnRHS);
  void assignVariables(std::vector<Expr>&v);
  void findRationalBound(const Expr& varSide, const Expr& ratSide, 
			 const Expr& var,
			 Rational &r);
  bool findBounds(const Expr& e, Rational& lub, Rational&  glb);

  Theorem normalizeProjectIneqs(const Theorem& ineqThm1,
				const Theorem& ineqThm2);
  //! Take a system of equations and turn it into a solved form
  Theorem solvedForm(const std::vector<Theorem>& solvedEqs);
  /*! @brief Substitute all vars in term 't' according to the
   * substitution 'subst' and canonize the result.
   */
  Theorem substAndCanonize(const Expr& t, ExprMap<Theorem>& subst);
  /*! @brief Substitute all vars in the RHS of the equation 'eq' of
   * the form (x = t) according to the substitution 'subst', and
   * canonize the result.
   */
  Theorem substAndCanonize(const Theorem& eq, ExprMap<Theorem>& subst);
  //! Traverse 'e' and push all the i-leaves into 'vars' vector
  void collectVars(const Expr& e, std::vector<Expr>& vars,
		   std::set<Expr>& cache);
  /*! @brief Check if alpha <= ax & bx <= beta is a finite interval
   *  for integer var 'x', and assert the corresponding constraint
   */
  void processFiniteInterval(const Theorem& alphaLEax,
			     const Theorem& bxLEbeta);
  //! For an integer var 'x', find and process all constraints A <= ax <= A+c 
  void processFiniteIntervals(const Expr& x);
  //! Recursive setup for isolated inequalities (and other new expressions)
  void setupRec(const Expr& e);

  //! Print a rational in SMT-LIB format
  void printRational(ExprStream& os, const Rational& r, bool printAsReal = false);
  //! Whether any ite's appear in the arithmetic part of the term e
  bool isAtomicArithTerm(const Expr& e);
  //! simplify leaves and then canonize
  Theorem canonSimp(const Expr& e);
  //! helper for checkAssertEqInvariant
  bool recursiveCanonSimpCheck(const Expr& e);

public:
  TheoryArith(TheoryCore* core);
  ~TheoryArith();

  //! Return whether e is syntactically identical to a rational constant
  bool isSyntacticRational(const Expr& e, Rational& r);
  //! Rewrite an atom to look like x - y op c if possible--for smtlib translation
  Expr rewriteToDiff(const Expr& e);
  //! Whether any ite's appear in the arithmetic part of the formula e
  bool isAtomicArithFormula(const Expr& e);

  // Trusted method that creates the proof rules class (used in constructor).
  // Implemented in arith_theorem_producer.cpp
  ArithProofRules* createProofRules();

  // Theory interface
  void addSharedTerm(const Expr& e);
  void assertFact(const Theorem& e);
  void refineCounterExample();
  void computeModelBasic(const std::vector<Expr>& v);
  void computeModel(const Expr& e, std::vector<Expr>& vars);
  void checkSat(bool fullEffort);
  Theorem rewrite(const Expr& e);
  void setup(const Expr& e);
  void update(const Theorem& e, const Expr& d);
  Theorem solve(const Theorem& e);
  void checkAssertEqInvariant(const Theorem& e);
  void checkType(const Expr& e);
  void computeType(const Expr& e);
  Type computeBaseType(const Type& t);
  void computeModelTerm(const Expr& e, std::vector<Expr>& v);
  Expr computeTypePred(const Type& t, const Expr& e);
  Expr computeTCC(const Expr& e);
  ExprStream& print(ExprStream& os, const Expr& e);
  virtual Expr parseExprOp(const Expr& e);

  // Arith constructors
  Type realType() { return d_realType; }
  Type intType() { return d_intType;}
  Type subrangeType(const Expr& l, const Expr& r)
    { return Type(Expr(SUBRANGE, l, r)); }
  Expr rat(Rational r) { return getEM()->newRatExpr(r); }
  // Dark and Gray shadows (for internal use only)
  //! Construct the dark shadow expression representing lhs <= rhs
  Expr darkShadow(const Expr& lhs, const Expr& rhs) {
    return Expr(DARK_SHADOW, lhs, rhs);
  }
  //! Construct the gray shadow expression representing c1 <= v - e <= c2
  /*! Alternatively, v = e + i for some i s.t. c1 <= i <= c2
   */
  Expr grayShadow(const Expr& v, const Expr& e,
		  const Rational& c1, const Rational& c2) {
    return Expr(GRAY_SHADOW, v, e, rat(c1), rat(c2));
  }
};

// Arith testers
inline bool isReal(Type t) { return t.getExpr().getKind() == REAL; }
inline bool isInt(Type t) { return t.getExpr().getKind() == INT; }

// Static arith testers
inline bool isRational(const Expr& e) { return e.isRational(); }
inline bool isIntegerConst(const Expr& e)
  { return e.isRational() && e.getRational().isInteger(); }
inline bool isUMinus(const Expr& e) { return e.getKind() == UMINUS; }
inline bool isPlus(const Expr& e) { return e.getKind() == PLUS; }
inline bool isMinus(const Expr& e) { return e.getKind() == MINUS; }
inline bool isMult(const Expr& e) { return e.getKind() == MULT; }
inline bool isDivide(const Expr& e) { return e.getKind() == DIVIDE; }
inline bool isPow(const Expr& e) { return e.getKind() == POW; }
inline bool isLT(const Expr& e) { return e.getKind() == LT; }
inline bool isLE(const Expr& e) { return e.getKind() == LE; }
inline bool isGT(const Expr& e) { return e.getKind() == GT; }
inline bool isGE(const Expr& e) { return e.getKind() == GE; }
inline bool isDarkShadow(const Expr& e) { return e.getKind() == DARK_SHADOW;}
inline bool isGrayShadow(const Expr& e) { return e.getKind() == GRAY_SHADOW;}
inline bool isIneq(const Expr& e)
  { return isLT(e) || isLE(e) || isGT(e) || isGE(e); }
inline bool isIntPred(const Expr& e) { return e.getKind() == IS_INTEGER; }

// Static arith constructors
inline Expr uminusExpr(const Expr& child)
  { return Expr(UMINUS, child); }
inline Expr plusExpr(const Expr& left, const Expr& right)
  { return Expr(PLUS, left, right); }
inline Expr plusExpr(const std::vector<Expr>& children) {
  DebugAssert(children.size() > 0, "plusExpr()");
  return Expr(PLUS, children);
}
inline Expr minusExpr(const Expr& left, const Expr& right)
  { return Expr(MINUS, left, right); }
inline Expr multExpr(const Expr& left, const Expr& right)
  { return Expr(MULT, left, right); }
// Begin Deepak: 
//! a Mult expr with two or more children
inline Expr multExpr(const std::vector<Expr>& children) {
  DebugAssert(children.size() > 0, "multExpr()");
  return Expr(MULT, children);
}
//! Power (x^n, or base^{pow}) expressions
inline Expr powExpr(const Expr& pow, const Expr & base)
  { return Expr(POW, pow, base);}
// End Deepak
inline Expr divideExpr(const Expr& left, const Expr& right)
  { return Expr(DIVIDE, left, right); }
inline Expr ltExpr(const Expr& left, const Expr& right)
  { return Expr(LT, left, right); }
inline Expr leExpr(const Expr& left, const Expr& right)
  { return Expr(LE, left, right); }
inline Expr gtExpr(const Expr& left, const Expr& right)
  { return Expr(GT, left, right); }
inline Expr geExpr(const Expr& left, const Expr& right)
  { return Expr(GE, left, right); }

inline Expr operator-(const Expr& child)
  { return uminusExpr(child); }
inline Expr operator+(const Expr& left, const Expr& right)
  { return plusExpr(left, right); }
inline Expr operator-(const Expr& left, const Expr& right)
  { return minusExpr(left, right); }
inline Expr operator*(const Expr& left, const Expr& right)
  { return multExpr(left, right); }
inline Expr operator/(const Expr& left, const Expr& right)
  { return divideExpr(left, right); }

}

#endif
