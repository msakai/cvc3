/*****************************************************************************/
/*!
 * \file theorem.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Dec 10 00:37:49 GMT 2002
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
// CLASS: Theorem
//
// AUTHOR: Sergey Berezin, 07/05/02
//
// See theorem.h file for more information.
///////////////////////////////////////////////////////////////////////////////

#include "theorem.h"
#include "theorem_value.h"
#include "command_line_flags.h"

namespace CVC3 {
  using namespace std;

  //! Compare Theorems by their expressions.  Return -1, 0, or 1.
  /*!
   *  This is an arbitrary total ordering on Theorems.  For
   *  simplicity, we define rewrite theorems (e1 = e2 or e1 <=> e2) to
   *  be smaller than other theorems.
   */
  /*
  int compare(const Theorem& t1, const Theorem& t2) {
    return compare(t1.getExpr(), t2.getExpr());
  }
  */
  int compare(const Theorem& t1, const Theorem& t2) {
    if(t1.d_thm == t2.d_thm) return 0;
    if(t1.isNull()) return -1; // Null Theorem is less than other theorems
    if(t2.isNull()) return 1;

    bool rw1(t1.isRewrite()), rw2(t2.isRewrite());

    if(!rw2) return compare(t1, t2.getExpr());
    else if(!rw1) return -compare(t2, t1.getExpr());
    else {
      int res(compare(t1.getLHS(), t2.getLHS()));
      if(res==0) res = compare(t1.getRHS(), t2.getRHS());
      return res;
    }
  }
  /*
  int compare(const Theorem& t1, const Expr& e2) {
    return compare(t1.getExpr(), e2);
  }
  */
  int compare(const Theorem& t1, const Expr& e2) {
    bool rw1(t1.isRewrite()), rw2(e2.isEq() || e2.isIff());
    if(!rw1) {
      const Expr& e1 = t1.getExpr();
      rw1 = (e1.isEq() || e1.isIff());
    }
    if(rw1) {
      if(rw2) {
	int res(compare(t1.getLHS(), e2[0]));
	if(res==0) res = compare(t1.getRHS(), e2[1]);
	return res;
      } else return -1;
    } else {
      if(rw2) return 1;
      else return compare(t1.getExpr(), e2);
    }
  }
  
  int compareByPtr(const Theorem& t1, const Theorem& t2) {
    if(t1.d_thm == t2.d_thm) return 0;
    else if(t1.d_thm < t2.d_thm) return -1;
    else return 1;
  }

  // Assignment operator
  Theorem& Theorem::operator=(const Theorem& th) {
    // Handle self-assignment
    if(this == &th) return *this;
    long tmp = th.d_thm;

    if (th.isRefl()) {
      th.exprValue()->incRefcount();
    }
    else {
      TheoremValue* tv = th.thm();
      DebugAssert(th.isNull() || tv->d_refcount > 0,
                  "Theorem::operator=: NEW refcount = "
                  + int2string(tv->d_refcount)
                  + " in " + th.toString());
      if (tv) ++(tv->d_refcount);
    }

    if (isRefl()) {
      exprValue()->decRefcount();
    }
    else {
      TheoremValue* tv = thm();
      DebugAssert(isNull() || tv->d_refcount > 0,
                  "Theorem::operator=: OLD refcount = "
                  + int2string(tv->d_refcount));

      //      IF_DEBUG(if((!isNull()) && tv->d_refcount == 1)
      //               TRACE("theorem", "Delete ", *this, ""));
      if((!isNull()) && --(tv->d_refcount) == 0) {
        MemoryManager* mm = tv->getMM();
        delete tv;
        mm->deleteData(tv);
      }
    }

    d_thm = tmp;

    return *this;
  }

  // Constructors
  Theorem::Theorem(TheoremManager* tm, const Expr &thm,
		   const Assumptions& assump, const Proof& pf, 
		   bool isAssump, int scope) {
    TheoremValue* tv;
    if(thm.isEq() || thm.isIff())
      tv = new(tm->getRWMM()) RWTheoremValue(tm, thm, assump, pf, isAssump, scope);
    else
      tv = new(tm->getMM()) RegTheoremValue(tm, thm, assump, pf, isAssump, scope);
    tv->d_refcount++;
    d_thm = ((long)tv)|0x1;
    //    TRACE("theorem", "Theorem(e) => ", *this, "");
    DebugAssert(!withProof() || !pf.isNull(),
		"Null proof in theorem:\n"+toString());
  }

  Theorem::Theorem(TheoremManager* tm, const Expr& lhs, const Expr& rhs,
		   const Assumptions& assump, const Proof& pf, bool isAssump,
                   int scope) {
    TheoremValue* tv = new(tm->getRWMM())
      RWTheoremValue(tm, lhs, rhs, assump, pf, isAssump, scope);
    tv->d_refcount++;
    d_thm = ((long)tv)|0x1;

    // record that rhs was simplified from lhs, provided that both are
    // atomic and rhs is a fresh expression, following SVC. We try to
    // approximate this by seeing if the rhs was the last created
    // expression (i.e. it has the last index handed out by the
    // expression manager), but that's not reliable since the
    // expressions may have been created in a different order than
    // they are passed into Theorem().

//     if (rhs.hasLastIndex() // FIXME: is this OK to comment out?
// 	// && tm->getVCL()->theoryCore()->isAtomicFormula(rhs)
// 	// && tm->getVCL()->theoryCore()->isAtomicFormula(lhs)
// 	)
//       ((Expr &)rhs).setSimpFrom(lhs.hasSimpFrom() ?
// 				lhs.getSimpFrom() :
// 				lhs);
//    TRACE("theorem", "Theorem(lhs,rhs) => ", *this, "");
    DebugAssert(!withProof() || !pf.isNull(),
		"Null proof in theorem:\n"+toString());
  }


  // Copy constructor
  Theorem::Theorem(const Theorem &th) : d_thm(th.d_thm) {
    if (d_thm & 0x1) {
      DebugAssert(thm()->d_refcount > 0,
		  "Theorem(const Theorem&): refcount = "
		  + int2string(thm()->d_refcount));
      thm()->d_refcount++;
      //      TRACE("theorem", "Theorem(Theorem&) => ", *this, "");
    } else if (d_thm != 0) {
      exprValue()->incRefcount();
    }
  }

  Theorem::Theorem(const Expr& e) : d_expr(e.d_expr)
  {
    d_expr->incRefcount();
  }

  // Destructor
  Theorem::~Theorem() {
    if (d_thm & 0x1) {
      TheoremValue* tv = thm();
      //      TRACE("theorem", "~Theorem(", *this, ") {");
      IF_DEBUG(FatalAssert(tv->d_refcount > 0,
                           "~Theorem(): refcount = "
                           + int2string(tv->d_refcount)));
      if((--tv->d_refcount) == 0) {
        //        TRACE_MSG("theorem", "~Theorem(): deleting");
        MemoryManager* mm = tv->getMM();
        delete tv;
        mm->deleteData(tv);
      }
    }
    else if (d_thm != 0) {
      exprValue()->decRefcount();
    }
  }

  void Theorem::printx() const { getExpr().print(); }
  void Theorem::printxnodag() const { getExpr().printnodag(); }
  void Theorem::pprintx() const { getExpr().pprint(); }
  void Theorem::pprintxnodag() const { getExpr().pprintnodag(); }
  void Theorem::print() const { cout << toString() << endl; }

  // Test if we are running in a proof production mode and with assumptions
  bool Theorem::withProof() const {
    if (isRefl()) return exprValue()->d_em->getTM()->withProof();
    return thm()->d_tm->withProof();
  }

  bool Theorem::withAssumptions() const {
    if (isRefl()) return exprValue()->d_em->getTM()->withAssumptions();
    return thm()->d_tm->withAssumptions();
  }
  
  bool Theorem::isRewrite() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isRewrite(): we are Null");
    return isRefl() || thm()->isRewrite();
  }

  // Return the theorem value as an Expr
  Expr Theorem::getExpr() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getExpr(): we are Null");
    if (isRefl()) {
      Expr e(exprValue());
      if (e.isTerm()) return e.eqExpr(e);
      else return e.iffExpr(e);
    }
    else return thm()->getExpr();
  }

  const Expr& Theorem::getLHS() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getLHS: we are Null");
    if (isRefl()) return *((Expr*)(&d_expr));
    else return thm()->getLHS();
  }

  const Expr& Theorem::getRHS() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getRHS: we are Null");
    if (isRefl()) return *((Expr*)(&d_expr));
    else return thm()->getRHS();
  }

// Return the assumptions.
// void Theorem::getAssumptions(Assumptions& a) const
// {
//   a = getAssumptionsRef();
// }


void Theorem::getAssumptionsRec(set<Expr>& assumptions) const
{
  if (isRefl() || isFlagged()) return;
  setFlag();
  if(isAssump()) {
    assumptions.insert(getExpr());
  }
  else {
    const Assumptions& a = getAssumptionsRef();
    for(Assumptions::iterator i=a.begin(), iend=a.end(); i!=iend; ++i)
      (*i).getAssumptionsRec(assumptions);
  }
}


void Theorem::getLeafAssumptions(vector<Expr>& assumptions,
                                 bool negate) const
{
  if (isNull() || isRefl()) return;
  set<Expr> assumpSet;
  clearAllFlags();
  getAssumptionsRec(assumpSet);
  // Order assumptions by their creation time
  for(set<Expr>::iterator i=assumpSet.begin(), iend=assumpSet.end();
      i!=iend; ++i)
    assumptions.push_back(negate ? (*i).negate() : *i);
}


const Assumptions& Theorem::getAssumptionsRef() const
{
  DebugAssert(!isNull(), "CVC3::Theorem::getAssumptionsRef: we are Null");
  if (!isRefl()) {
    return thm()->getAssumptionsRef();
  }
  else return Assumptions::emptyAssump();
}


  bool Theorem::isAssump() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isAssump: we are Null");
    return isRefl() ? false : thm()->isAssump();
  }

  // Return the proof of the theorem.  If running without proofs,
  // return the Null proof.
  Proof Theorem::getProof() const {
    static Proof null;
    DebugAssert(!isNull(), "CVC3::Theorem::getProof: we are Null");
    if (isRefl()) {
      return Proof(Expr(PF_APPLY,
                        exprValue()->d_em->newVarExpr("refl"),
                        Expr(exprValue())));
    }
    else if (withProof() == true)
      return thm()->getProof();
    else
      return null;
  }

  bool Theorem::isFlagged() const {
    DebugAssert(!isNull(), "CVC3::Theorem::isFlagged: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->isFlagged((long)d_expr);
    else return thm()->isFlagged();
  }

  void Theorem::clearAllFlags() const {
    DebugAssert(!isNull(), "CVC3::Theorem::clearAllFlags: we are Null");
    if (isRefl()) {
      exprValue()->d_em->getTM()->clearAllFlags();
    } else thm()->clearAllFlags();
  }

  void Theorem::setFlag() const {
    DebugAssert(!isNull(), "CVC3::Theorem::setFlag: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setFlag((long)d_expr);
    else thm()->setFlag();
  }

  void Theorem::setCachedValue(int value) const {
    DebugAssert(!isNull(), "CVC3::Theorem::setCachedValue: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setCachedValue((long)d_expr, value);
    else thm()->setCachedValue(value);
  }
  
  int Theorem::getCachedValue() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getCachedValue: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->getCachedValue((long)d_expr);
    return thm()->getCachedValue();
  }
  
  void Theorem::setExpandFlag(bool val) const {
    DebugAssert(!isNull(), "CVC3::Theorem::setExpandFlag: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setExpandFlag((long)d_expr, val);
    thm()->setExpandFlag(val);
  }

  bool Theorem::getExpandFlag() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getExpandFlag: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->getExpandFlag((long)d_expr);
    return thm()->getExpandFlag();
  }

  void Theorem::setLitFlag(bool val) const {
    DebugAssert(!isNull(), "CVC3::Theorem::setLitFlag: we are Null");
    if (isRefl()) exprValue()->d_em->getTM()->setLitFlag((long)d_expr, val);
    thm()->setLitFlag(val);
  }

  bool Theorem::getLitFlag() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getLitFlag: we are Null");
    if (isRefl()) return exprValue()->d_em->getTM()->getLitFlag((long)d_expr);
    return thm()->getLitFlag();
  }

  bool Theorem::isAbsLiteral() const {
    return getExpr().isAbsLiteral();
  }

  int Theorem::getScope() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getScope: we are Null");
    return isRefl() ? 0 : thm()->getScope();
  }

  unsigned Theorem::getQuantLevel() const {
    DebugAssert(!isNull(), "CVC3::Theorem::getQuantLevel: we are Null");
    return isRefl() ? 0 : thm()->getQuantLevel();
  }

  void Theorem::setQuantLevel(unsigned level) {
    DebugAssert(!isNull(), "CVC3::Theorem::setQuantLevel: we are Null");
    DebugAssert(!isRefl(), "CVC3::Theorem::setQuantLevel: we are Refl");
    thm()->setQuantLevel(level);
  }

  size_t Theorem::hash() const {
    static std::hash<long int> h;
    return h(d_thm);
  }

  void Theorem::recursivePrint(int& i) const {
    cout << "[" << getCachedValue()
	 << "]@" << getScope() << "\tTheorem: {";

    if (isAssump()) {
      cout << "assump";
    }
    else if (getAssumptionsRef().empty()) {
      cout << "empty";
    }
    else {
      const Assumptions::iterator iend = getAssumptionsRef().end();
      for (Assumptions::iterator it = getAssumptionsRef().begin();
	   it != iend; ++it) {
	if (!it->isFlagged()) it->setCachedValue(i++);
	cout << "[" << it->getCachedValue() << "], " ;
      }
      cout << "}" << endl << "\t\t|- " << getExpr() << endl;
      for (Assumptions::iterator it = getAssumptionsRef().begin();
	   it != iend; ++it) {
	if (it->isFlagged()) continue;
	it->recursivePrint(i);
	it->setFlag();
      }
      return;
    }
    cout << "}" << endl << "\t\t|- " << getExpr() << endl;
  }


  // Return the scope level at which this theorem was created
//   int Theorem::getScope() const {
//     DebugAssert(!isNull(), "CVC3::Theorem::getScope: we are Null");
//     return thm()->getScope();
//   }

//   Assumptions Theorem::getUserAssumptions() const {
//     ExprMap<Theorem> em;
//     Assumptions a = getAssumptionsCopy();

//     collectAssumptions(a, em);
    
//     return a;
//   }

//   void collectAssumptions(Assumptions &a, ExprMap<Theorem> em ) const {
//     if (isAssump()) {
//       // cache?
//       return;
//     }
    
//     const Assumptions a2 = thm()->getAssumptions();
//     a.add(a2);
//     Assumptions::iterator a2begin = a2.begin();
//     const Assumptions::iterator a2end = a2.end();


//   }


  // Printing Theorem
  ostream& Theorem::print(ostream& os, const string& name) const {
    if(isNull()) return os << name << "(Null)";
    ExprManager *em = getExpr().getEM();
    if (isRefl()) os << getExpr();
    else if (withAssumptions()) {
      em->incIndent(name.size()+2);
      os << name << "([" << thm() << "#" << thm()->d_refcount << "]@"
	 << getScope() << "\n[";
      if(isAssump()) os << "Assump";
      else {
	if(thm()->d_tm->getFlags()["print-assump"].getBool()
	   && em->isActive())
	  os << getAssumptionsRef();
	else
	  os << "<assumptions>";
      }
      os << "]\n  |--- ";
      em->indent(7);
      if(em->isActive()) os << getExpr();
      else os << "(being destructed)";
      if(withProof())
	os << "\n Proof = " << getProof();
      return os << ")";
    }
    else {
      em->incIndent(name.size()+1);
      os << name << "(";
      if(em->isActive()) os << getExpr();
      else os << "being destructed";
      return os << ")";
    }
    return os;
  }


} // end of namespace CVC3
