/*****************************************************************************/
/*!
 * \file theorem_value.h
 * 
 * Author: Sergey Berezin
 * 
 * Created: Dec 10 01:03:34 GMT 2002
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
// CLASS: TheoremValue
//
// AUTHOR: Sergey Berezin, 07/05/02
//
// Abstract:
//
// A class representing a proven fact in CVC.  It stores the theorem
// as a CVC expression, and in the appropriate modes also the set of
// assumptions and the proof.
//
// The idea is to allow only a few trusted classes to create values of
// this class.  If all the critical computations in the decision
// procedures are done through the use of Theorems, then soundness of
// these decision procedures will rely only on the soundness of the
// methods in the trusted classes (the inference rules).
//
// Thus, proof checking can effectively be done at run-time on the
// fly.  Or the soundness may be potentially proven by static analysis
// and many run-time checks can then be optimized away.
//
// This theorem_value.h file should NOT be used by the decision
// procedures.  Use theorem.h instead.
//
////////////////////////////////////////////////////////////////////////

#ifndef _cvc3__theorem_value_h_
#define _cvc3__theorem_value_h_

#include "theorem.h"
#include "theorem_manager.h"
//#include "vcl.h"

//#include "theory_core.h"


namespace CVC3 {

  //  extern VCL* myvcl;

  class TheoremValue
  {
    // These are the only classes that can create new TheoremValue classes
    friend class Theorem;
    friend class RegTheoremValue;
    friend class RWTheoremValue;

  protected:
    //! Theorem Manager
    TheoremManager* d_tm;

    //! The expression representing a theorem
    Expr d_thm;

    //! Proof of the theorem
    Proof d_proof;

    //! How many pointers to this theorem value
    unsigned d_refcount;

    //! Largest scope level of the assumptions
    int d_scopeLevel;

    //! Quantification level of this theorem
    unsigned d_quantLevel;

    //! Temporary flag used during traversals
    unsigned d_flag;

    //! Temporary cache used during traversals
    int d_cachedValue : 29;

    bool d_isAssump : 1;
    bool d_expand : 1; //!< whether it should this be expanded in graph traversal
    bool d_clauselit : 1;  //!< whether it belongs to the conflict clause


  private:
    // Constructor.   
    /*!
     * NOTE: it is private; only friend classes can call it.
     *
     * If the assumptions refer to only one theorem, grab the
     * assumptions of that theorem instead.
     */
    TheoremValue(TheoremManager* tm, const Expr &thm,
		 const Proof& pf, bool isAssump) :
      d_tm(tm), d_thm(thm), d_proof(pf), d_refcount(0),
      d_scopeLevel(0), d_quantLevel(0), d_flag(0), d_isAssump(isAssump) {}

    // Disable copy constructor and assignment
    TheoremValue(const TheoremValue& t) {
      FatalAssert(false, "TheoremValue() copy constructor called");
    }
    TheoremValue& operator=(const TheoremValue& t) {
      FatalAssert(false, "TheoremValue assignment operator called");
      return *this;
    }

    bool isFlagged() const {
      return d_flag == d_tm->getFlag();
    }

    void clearAllFlags() {
      d_tm->clearAllFlags();
    }
    
    void setFlag() {
      d_flag = d_tm->getFlag();
    }

    void setCachedValue(int value) {
      d_cachedValue = value;
    }

    int getCachedValue() const {
      return d_cachedValue;
    }

    void setExpandFlag(bool val) {
      d_expand = val;
    }

    bool getExpandFlag() {
      return d_expand;
    }
    
    void setLitFlag(bool val) {
      d_clauselit = val;
    }

    bool getLitFlag() {
      return d_clauselit;
    }

    int getScope() {
      return d_scopeLevel;
    }

    unsigned getQuantLevel() { return d_quantLevel; }
    void setQuantLevel(unsigned level) { d_quantLevel = level; }

//     virtual bool isRewrite() const { return d_thm.isEq() || d_thm.isIff(); }
    virtual bool isRewrite() const { return false; }

    virtual const Expr& getExpr() const { return d_thm; }
    virtual const Expr& getLHS() const {
      //      TRACE("getExpr","TheoremValue::getLHS called (",d_thm,")");
      DebugAssert(isRewrite(),
		  "TheoremValue::getLHS() called on non-rewrite theorem:\n"
		  +toString());
      return d_thm[0];
    }
    virtual const Expr& getRHS() const {
      //      TRACE("getExpr","TheoremValue::getRHS called (",d_thm,")");
      DebugAssert(isRewrite(),
		  "TheoremValue::getRHS() called on non-rewrite theorem:\n"
		  +toString());
      return d_thm[1];
    }

    virtual const Assumptions& getAssumptionsRef() const = 0;

    bool isAssump() const { return d_isAssump; }
    const Proof& getProof() { return d_proof; }

  public:
    // Destructor
    virtual ~TheoremValue() { 
      IF_DEBUG(FatalAssert(d_refcount == 0,
                           "Thm::TheoremValue::~TheoremValue(): refcount != 0."));
    }

    std::string toString() const {
      return getAssumptionsRef().toString() + " |- " + getExpr().toString();
    }

    // Memory management
    virtual MemoryManager* getMM() = 0;

  }; // end of class TheoremValue

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Class: RegTheoremValue                                                    //
// Author: Clark Barrett                                                     //
// Created: Fri May  2 12:51:55 2003                                         //
// Description: A special subclass for non-rewrite theorems.  Assumptions are//
//              embedded in the object for easy reference.                   //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
  class RegTheoremValue :public TheoremValue
  {
    friend class Theorem;

  protected:
    //! The assumptions for the theorem
    Assumptions d_assump;

  private:
    // Constructor.   NOTE: it is private; only friend classes can call it.
    RegTheoremValue(TheoremManager* tm, const Expr& thm,
                    const Assumptions& assump, const Proof& pf, bool isAssump,
                    int scope = -1)
      : TheoremValue(tm, thm, pf, isAssump), d_assump(assump)
    {
      DebugAssert(d_tm->isActive(), "TheoremValue()");
      if (isAssump) {
        DebugAssert(assump.empty(), "Expected empty assumptions");
        // refcount tricks are because a loop is created with Assumptions
        d_refcount = 1;
        {
          Theorem t(this);
          d_assump.add1(t);
        }
        d_refcount = 0;
        if (scope == -1) d_scopeLevel = tm->getCM()->scopeLevel();
        else d_scopeLevel = scope;
      }
      else {
        if (!d_assump.empty()) {
          const Assumptions::iterator iend = d_assump.end();
          for (Assumptions::iterator i = d_assump.begin(); 
               i != iend; ++i) {
            if (i->getScope() > d_scopeLevel)
              d_scopeLevel = i->getScope();
            if (i->getQuantLevel() > d_quantLevel)
              d_quantLevel = i->getQuantLevel();
          }
        }
      }
      TRACE("quantlevel", d_quantLevel, " theorem get_1 ", thm.toString()); 
      TRACE("quantlevel", d_quantLevel, " theorem get_1 ", thm.getIndex()); 
    }

  public:
    // Destructor
    ~RegTheoremValue() {
      if (d_isAssump) {
        IF_DEBUG(FatalAssert(d_assump.size() == 1, "Expected size 1"));
        IF_DEBUG(FatalAssert(d_assump.getFirst().thm() == this, "Expected loop"));
        d_assump.getFirst().d_thm = 0;
      }
    }

    const Assumptions& getAssumptionsRef() const { return d_assump; }

    // Memory management
    MemoryManager* getMM() { return d_tm->getMM(); }

    void* operator new(size_t size, MemoryManager* mm) {
      return mm->newData(size);
    }
    void operator delete(void* pMem, MemoryManager* mm) {
      mm->deleteData(pMem);
    }

    void operator delete(void* d) { }

  }; // end of class RegTheoremValue

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
// Class: RWTheoremValue                                                     //
// Author: Clark Barrett                                                     //
// Created: Fri May  2 12:51:55 2003                                         //
// Description: A special subclass for theorems of the form A |- t=t' or     //
//              A |- phi iff phi'.  The actual Expr is only created on       //
//              demand.  The idea is that getLHS and getRHS should be used   //
//              whenever possible, avoiding creating unnecessary Expr's.     //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
  class RWTheoremValue :public TheoremValue
  {
    friend class Theorem;

  protected:
    // d_thm in the base class contains the full expression, which is
    // only constructed on demand.
    Expr d_lhs;
    Expr d_rhs;
    Assumptions* d_assump;

  private:
    void init(const Assumptions& assump, int scope)
    {
      DebugAssert(d_tm->isActive(), "TheoremValue()");
      if (d_isAssump) {
        DebugAssert(assump.empty(), "Expected empty assumptions");
        // refcount tricks are because a loop is created with Assumptions
        d_refcount = 1;
        {
          Theorem t(this);
          d_assump = new Assumptions(t);
        }
        d_refcount = 0;
        if (scope == -1) d_scopeLevel = d_tm->getCM()->scopeLevel();
        else d_scopeLevel = scope;
      }
      else {
        if (!assump.empty()) {
          d_assump = new Assumptions(assump);
          const Assumptions::iterator iend = assump.end();
          for (Assumptions::iterator i = assump.begin(); 
               i != iend; ++i) {
            if (i->getScope() > d_scopeLevel)
              d_scopeLevel = i->getScope();
            if (i->getQuantLevel() > d_quantLevel)
              d_quantLevel = i->getQuantLevel();
          }
        }
      }
      TRACE("quantlevel", d_quantLevel, " theorem get ", d_thm.toString());
    }

    // Constructor.   NOTE: it is private; only friend classes can call it.
    RWTheoremValue(TheoremManager* tm, const Expr& lhs, const Expr& rhs,
		   const Assumptions& assump, const Proof& pf, bool isAssump,
                   int scope = -1)
      : TheoremValue(tm, Expr(), pf, isAssump), d_lhs(lhs), d_rhs(rhs), d_assump(NULL)
    { init(assump, scope); }

    // Sometimes we have the full expression already created
    RWTheoremValue(TheoremManager* tm, const Expr& thm,
                   const Assumptions& assump, const Proof& pf, bool isAssump,
                   int scope = -1)
      : TheoremValue(tm, thm, pf, isAssump), d_lhs(thm[0]), d_rhs(thm[1]), d_assump(NULL)
    { init(assump, scope); }

    const Expr& getExpr() const {
      if (d_thm.isNull()) {
	bool isBool = d_lhs.getType().isBool();
	// have to fake out the const qualifier
	Expr* pexpr = const_cast<Expr*>(&d_thm);
	*pexpr = isBool ? d_lhs.iffExpr(d_rhs) : d_lhs.eqExpr(d_rhs);
	//	TRACE("getExpr", "getExpr called on RWTheorem (", d_thm, ")");
      }
      return d_thm;
    }

    const Expr& getLHS() const { return d_lhs; }
    const Expr& getRHS() const { return d_rhs; }

  public:
    // Destructor
    ~RWTheoremValue() {
      if (d_isAssump) {
        IF_DEBUG(FatalAssert(d_assump && d_assump->size() == 1, "Expected size 1"));
        IF_DEBUG(FatalAssert(d_assump->getFirst().thm() == this, "Expected loop"));
        d_assump->getFirst().d_thm = 0;
      }
      if (d_assump) delete d_assump;
    }

    bool isRewrite() const { return true; }
    const Assumptions& getAssumptionsRef() const {
      if (d_assump) return *d_assump;
      else return Assumptions::emptyAssump();
    }

    // Memory management
    MemoryManager* getMM() { return d_tm->getRWMM(); }

    void* operator new(size_t size, MemoryManager* mm) {
      return mm->newData(size);
    }
    void operator delete(void* pMem, MemoryManager* mm) {
      mm->deleteData(pMem);
    }

    void operator delete(void* d) { }

  }; // end of class RWTheoremValue

}; // end of namespace CVC3

#endif
