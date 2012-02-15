/*****************************************************************************/
/*!
 * \file expr.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Thu Dec  5 11:35:55 2002
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


#include <algorithm>


#include "expr.h"
#include "pretty_printer.h"
#include "expr_stream.h"
#include "notifylist.h"
#include "exception.h"


using namespace std;


namespace CVC3 {


Expr Expr::s_null;

///////////////////////////////////////////////////////////////////////
// Class Expr methods                                                //
///////////////////////////////////////////////////////////////////////


Expr Expr::recursiveSubst(const ExprHashMap<Expr>& subst,
                          ExprHashMap<Expr>& visited) const {
  // Check the cache.
  // INVARIANT: visited contains all the flagged expressions, and only those
  if(getFlag()) return visited[*this];

  ExprIndex minIndex = 0;
  for(ExprHashMap<Expr>::iterator i = subst.begin(),iend=subst.end();i!=iend;++i) {
    if(minIndex > (i->first).getIndex())
      minIndex = (i->first).getIndex();
  }

  Expr replaced;

  if(isClosure()) {
    const vector<Expr> & vars = getVars();
    vector<Expr> common; // Bound vars which occur in subst

    for(vector<Expr>::const_iterator i = vars.begin(), iend=vars.end();
	i!=iend; ++i) {
      if(subst.count(*i) > 0) common.push_back(*i);
    }

    if(common.size() > 0) {
      IF_DEBUG(debugger.counter("substExpr: bound var clashes")++);
      // Reduced substitution (without the common vars)
      ExprHashMap<Expr> newSubst(subst);
      // Remove variables in "common" from the substitution
      for(vector<Expr>::iterator i=common.begin(), iend=common.end();
	  i!=iend; ++i)
	newSubst.erase(*i);

      // Clear all the caches (important!)
      visited.clear();
      clearFlags();
      visited = newSubst;

      ExprHashMap<Expr>::iterator j = newSubst.begin();
      for (; j != newSubst.end(); ++j) { // old vars bound in e
	j->first.setFlag();
      }
    
      replaced = 
	getEM()->newClosureExpr(getKind(), vars,
                                getBody().recursiveSubst(newSubst, visited));

      // Clear the flags again, as we restore the substitution
      visited.clear();
      clearFlags();
      visited = subst;
      // Restore the flags on the original substitutions
      for (ExprHashMap<Expr>::iterator i = subst.begin(), iend=subst.end();
	   i != iend; ++i)
	i->first.setFlag();
    } else {
      replaced =
        getEM()->newClosureExpr(getKind(), vars,
                                getBody().recursiveSubst(subst, visited));
    }
  } else { // Not a Closure
      int changed=0;
      vector<Expr> children;      
      for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i){	
	Expr repChild = *i;
	if(repChild.getIndex() >= minIndex)
	  repChild = (*i).recursiveSubst(subst, visited);
	if(repChild != *i)
	  changed++;
	children.push_back(repChild);
      }
      if(changed > 0)
	replaced = Expr(getOp(), children);
      else
	replaced = *this;
  }
  visited.insert(*this, replaced);
  setFlag();
  return replaced;
}


static bool subExprRec(const Expr& e1, const Expr& e2) {
  if(e1 == e2) return true;
  if(e2.getFlag()) return false;
  // e1 is created after e2, so e1 cannot be a subexpr of e2
  if(e1 > e2) return false;
  e2.setFlag();
  bool res(false);
  for(Expr::iterator i=e2.begin(), iend=e2.end(); !res && i!=iend; ++i)
    res = subExprRec(e1, *i);
  return res;
}


bool 
Expr::subExprOf(const Expr& e) const {
  if(*this == e) return true;
  // "this" is created after e, so it cannot be e's subexpression
  if(*this > e) return false;
  clearFlags();
  return subExprRec(*this, e);
}


Expr Expr::substExpr(const vector<Expr>& oldTerms,
                     const vector<Expr>& newTerms) const
{
  DebugAssert(oldTerms.size() == newTerms.size(), "substExpr: vectors"
	      "don't match in size");
  // Catch the vacuous case
  if(oldTerms.size() == 0) return *this;

  ExprHashMap<Expr> oldToNew(10);
  clearFlags();
  for(unsigned int i=0; i<oldTerms.size(); i++) {
    oldToNew.insert(oldTerms[i], newTerms[i]);
    oldTerms[i].setFlag();
  }
  // For cache, initialized by the substitution
  ExprHashMap<Expr> visited(oldToNew);
  return recursiveSubst(oldToNew, visited);

}


Expr Expr::substExpr(const ExprHashMap<Expr>& oldToNew) const
{
  // Catch the vacuous case
  if(oldToNew.size() == 0) return *this;
  // Rebuild the map: we'll be using it as a cache
  ExprHashMap<Expr> visited(oldToNew);
  clearFlags();
  // Flag all the LHS expressions in oldToNew map.  We'll be checking
  // all flagged expressions (and only those) for substitution.
  for(ExprHashMap<Expr>::iterator i=oldToNew.begin(), iend=oldToNew.end();
      i!=iend; ++i) {
    (*i).first.setFlag();
  }
  return recursiveSubst(oldToNew, visited);
}


string Expr::toString() const {
  return toString(PRESENTATION_LANG);
//   if(isNull()) return "Null";
//   ostringstream ss;
//   ss << (*this);
//   return ss.str();
}

string Expr::toString(InputLanguage lang) const {
  if(isNull()) return "Null";
  ostringstream ss;
  ExprStream os(getEM());
  os.lang(lang);
  os.os(ss);
  os << (*this);
  return ss.str();
}

void Expr::print(InputLanguage lang, bool dagify) const {
  if(isNull()) {
    cout << "Null" << endl; return;
  }
  ExprStream os(getEM());
  os.lang(lang);
  os.dagFlag(dagify);
  os << *this << endl;
}


void Expr::pprint() const
{
  if(isNull()) {
    cout << "Null" << endl; return;
  }
  ExprStream os(getEM());
  os << *this << endl;
}


void Expr::pprintnodag() const
{
  if(isNull()) {
    cout << "Null" << endl; return;
  }
  ExprStream os(getEM());
  os.dagFlag(false);
  os << *this << endl;
}


void Expr::printnodag() const
{
  print(AST_LANG, false);
}


ExprStream& Expr::printAST(ExprStream& os) const {
  if(isNull()) return os << "Null" << endl;
  bool isLetDecl(getKind() == LETDECL);
  os << "(" << push;
  os << getEM()->getKindName(getKind());
  if (isApply()) {
    os << space << "{" << getOp().getExpr() << push << "}";
  }
  else if (isSymbol()) {
    os << space << "{Symbol: " << getName() << "}";
  }
  else if (isClosure()) {
    os << space << "{" << space << "(" << push;
    const vector<Expr>& vars = getVars();
    vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
    if(i!=iend) { os << *i; ++i; }
    for(; i!=iend; ++i) os << space << *i;
    os << push << ") " << pop << pop;
    os << getBody() << push << "}";
  }
  else {
    switch(getKind()) {
      case STRING_EXPR:
        DebugAssert(isString(), "Expected String");
        os << space << "{" << '"'+ getString() + '"' << "}";
        break;
      case SKOLEM_VAR:
        getExistential();
        os << space << "{SKOLEM_" << (int)getIndex() << "}";
        break;
      case RATIONAL_EXPR:
        os << space << "{" << getRational() << "}";
        break;
      case UCONST: 
        DebugAssert(isVar(), "Expected Var");
        os << space << "{" << getName() << "}";
        break;
      case BOUND_VAR:
        DebugAssert(isVar(), "Expected Var");
        os << space << "{"+getName()+"_"+getUid()+"}";
        break;
      case THEOREM_KIND:
        DebugAssert(isTheorem(), "Expected Theorem");
        os << space << "{Theorem: " << getTheorem().toString() << "}";
      default: ; // Don't do anything
    }
  }

  for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i) {
    if(isLetDecl) os << nodag;
    os << space << *i;
  }
  os << push << ")";
  os.resetIndent();
  return os;
}


ExprStream& Expr::print(ExprStream& os) const {
  if(isNull()) return os << "Null" << endl;
  DebugAssert(arity() == 0, "Expected arity 0");
  if (isSymbol()) return os << getName();
  switch(getKind()) {
    case TRUE_EXPR: return os << "TRUE";
    case FALSE_EXPR: return os << "FALSE";
    case NULL_KIND: return os << "Null";
    case STRING_EXPR: return os << '"'+ getString() + '"';
    case RATIONAL_EXPR: return os << getRational();
    case SKOLEM_VAR: return os << "SKOLEM_" <<  hash();
    case UCONST: return os << getName();
    case BOUND_VAR: return os << "(BOUND_VAR "+getName()+"_"+getUid()+")";
    case RAW_LIST: {
      os << "(" << push;
      bool firstTime(true);
      for(Expr::iterator i=begin(), iend=end(); i!=iend; ++i) {
        if(firstTime) firstTime = false;
        else os << space;
        os << *i;
      }
      return os << push << ")";
    }
    case FORALL:
    case EXISTS: 
      if(isQuantifier()) {
        os << "(" << push << getEM()->getKindName(getKind())
           << space << "(" << push;
        const vector<Expr>& vars = getVars();
        vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
        if(i!=iend) { os << *i; ++i; }
        for(; i!=iend; ++i) os << space << *i;
        os << push << ") " << pop << pop;
        return os << getBody() << push << ")";
      }
      // If not an internal representation of quantifiers, it'll be
      // printed as "normal" Expr with a kind and children
    default:
      //    os << "(" << push;
      os << getEM()->getKindName(getKind());
      //    os << push << ")";
  }
  os.resetIndent();
  return os;
}


//! Set initial indentation to n.
/*! The indentation will be reset to default unless the second
    argument is true.  This setting only takes effect when printing to
    std::ostream.  When printing to ExprStream, the indentation can be
    set directly in the ExprStream. */
Expr& Expr::indent(int n, bool permanent) {
  DebugAssert(!isNull(), "Expr::indent called on Null Expr");
  getEM()->indent(n, permanent);
  return *this;
}


void Expr::addToNotify(Theory* i, const Expr& e) const {
  DebugAssert(!isNull(), "Expr::addToNotify() on Null expr");
  if(getNotify() == NULL)
    d_expr->d_notifyList = new NotifyList(getEM()->getCurrentContext());
  getNotify()->add(i, e);
}


bool Expr::isAtomic() const
{
  //  TRACE("isAtomic", "isAtomic(", *this, ") {");
  if (validIsAtomicFlag()) {
    //    TRACE("isAtomic", "isAtomic[cached] => ",
    //	  getIsAtomicFlag()? "true" : "false", " }");
    return getIsAtomicFlag();
  }
  if (getType().isBool() && !isBoolConst()) {
    setIsAtomicFlag(false);
    //    TRACE_MSG("isAtomic", "isAtomic[bool] => false }");
    return false;
  }
  for (int k = 0; k < arity(); ++k) {
    if (!(*this)[k].isAtomic()) {
      setIsAtomicFlag(false);
      //      TRACE_MSG("isAtomic", "isAtomic[kid] => false }");
      return false;
    }
  }
  setIsAtomicFlag(true);
  //  TRACE_MSG("isAtomic", "isAtomic[kid] => true }");
  return true;
}


bool Expr::isAtomicFormula() const
{
  //  TRACE("isAtomic", "isAtomicFormula(", *this, ") {");
  if (!getType().isBool()) {
    //    TRACE_MSG("isAtomic", "isAtomicFormula[kid] => false }");
    return false;
  }
  switch(getKind()) {
    case FORALL: case EXISTS: case XOR:
    case NOT: case AND: case OR: case ITE: case IFF: case IMPLIES:
      //      TRACE_MSG("isAtomic", "isAtomicFormula[connective] => false }");
      return false;
  }
  for (Expr::iterator k = begin(), kend=end(); k != kend; ++k) {
    if (!(*k).isAtomic()) {
      //      TRACE_MSG("isAtomic", "isAtomicFormula[kid] => false }");
      return false;
    }
  }
  //  TRACE_MSG("isAtomic", "isAtomicFormula => true }");
  return true;
}


  // This is one of the most friequently called routines.  Make it as
  // efficient as possible.
int compare(const Expr& e1, const Expr& e2) {
  // Quick equality check (operator== is implemented independently
  // and more efficiently)
  if(e1 == e2) return 0;
    
  if(e1.d_expr == NULL) return -1;
  if(e2.d_expr == NULL) return 1;
  // Both are non-Null.  Compare the indices.
  return (e1.getIndex() < e2.getIndex())? -1 : 1;
}


///////////////////////////////////////////////////////////////////////
// Class Expr::iterator methods                                      //
///////////////////////////////////////////////////////////////////////


ostream& operator<<(ostream& os, const Expr& e) {
  if(e.isNull()) return os << "Null";
  ExprStream es(e.getEM());
  es.os(os);
  es << e;
  e.getEM()->restoreIndent();
  return os;
}


// Functions from class Type


Type::Type(Expr expr) : d_expr(expr)
{
  if (expr.isNull()) return;
  expr.getEM()->checkType(expr);
}


Type Type::funType(const std::vector<Type>& typeDom, const Type& typeRan) {
  vector<Expr> tmp;
  for(vector<Type>::const_iterator i=typeDom.begin(), iend=typeDom.end();
      i!=iend; ++i)
    tmp.push_back(i->getExpr());
  tmp.push_back(typeRan.getExpr());
  return Type(Expr(ARROW, tmp));
}


} // end of namespace CVC3
