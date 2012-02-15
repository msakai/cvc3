/*****************************************************************************/
/*!
 * \file theory_array.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Thu Feb 27 00:38:55 2003
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


#include "theory_array.h"
#include "array_proof_rules.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "theory_core.h"
#include "command_line_flags.h"
#include "translator.h"


using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// TheoryArray Private Methods                                               //
///////////////////////////////////////////////////////////////////////////////

Theorem TheoryArray::renameExpr(const Expr& e) {
  Theorem thm = getCommonRules()->varIntroSkolem(e);
  DebugAssert(thm.isRewrite() && thm.getRHS().isSkolem(),
              "thm = "+thm.toString());
  theoryCore()->addToVarDB(thm.getRHS());
  return thm;
}


///////////////////////////////////////////////////////////////////////////////
// TheoryArray Public Methods                                                //
///////////////////////////////////////////////////////////////////////////////


TheoryArray::TheoryArray(TheoryCore* core)
  : Theory(core, "Arrays"), d_reads(core->getCM()->getCurrentContext()),
    d_applicationsInModel(core->getFlags()["applications"].getBool()),
    d_liftReadIte(core->getFlags()["liftReadIte"].getBool())
{
  d_rules = createProofRules();

  // Register new local kinds with ExprManager
  getEM()->newKind(ARRAY, "_ARRAY", true);
  getEM()->newKind(READ, "_READ");
  getEM()->newKind(WRITE, "_WRITE");
  getEM()->newKind(ARRAY_LITERAL, "_ARRAY_LITERAL");

  vector<int> kinds;
  kinds.push_back(ARRAY);
  kinds.push_back(READ);
  kinds.push_back(WRITE);

  kinds.push_back(ARRAY_LITERAL);

  registerTheory(this, kinds);
}


// Destructor: delete the proof rules class if it's present
TheoryArray::~TheoryArray() {
  if(d_rules != NULL) delete d_rules;
}


Theorem TheoryArray::rewrite(const Expr& e)
{
  Theorem thm;
  if (isRead(e)) {
    switch(e[0].getKind()) {
      case WRITE:
	thm = d_rules->rewriteReadWrite(e);
	return transitivityRule(thm, simplify(thm.getRHS()));
      case ARRAY_LITERAL: {
	IF_DEBUG(debugger.counter("Read array literals")++);
	thm = d_rules->readArrayLiteral(e);
	return transitivityRule(thm, simplify(thm.getRHS()));
      }
      case ITE: {
        if (d_liftReadIte) {
          thm = d_rules->liftReadIte(e);
          return transitivityRule(thm, simplify(thm.getRHS()));
        }
      }
      default: {
	const Theorem& rep = e.getRep();
	if (rep.isNull()) return reflexivityRule(e);
	else return symmetryRule(rep);
      }
    }
  }
  else if (!e.isTerm()) {
    if (e.isEq() && e[0].isAtomic() && e[1].isAtomic() && isWrite(e[0])) {
      Expr left = e[0], right = e[1];
      int leftWrites = 1, rightWrites = 0;

      // Count nested writes
      Expr e1 = left[0];
      while (isWrite(e1)) { leftWrites++; e1 = e1[0]; }

      Expr e2 = right;
      while (isWrite(e2)) { rightWrites++; e2 = e2[0]; }

      if (rightWrites == 0) {
	if (e1 == e2) {
	  thm = d_rules->rewriteSameStore(e, leftWrites);
	  return transitivityRule(thm, simplify(thm.getRHS()));
	}
	else {
	  e.setRewriteNormal();
	  return reflexivityRule(e);
	}
      }

      if (leftWrites > rightWrites) {
	thm = getCommonRules()->rewriteUsingSymmetry(e);
	thm = transitivityRule(thm, d_rules->rewriteWriteWrite(thm.getRHS()));
      }
      else thm = d_rules->rewriteWriteWrite(e);
      return transitivityRule(thm, simplify(thm.getRHS()));
    }
    e.setRewriteNormal();
    return reflexivityRule(e);
  }
  else if (!e.isAtomic()) {
    e.setRewriteNormal();
    return reflexivityRule(e);
  }
  else if (isWrite(e)) {
    Expr store = e[0];
    while (isWrite(store)) store = store[0];
    DebugAssert(findExpr(e[2]) == e[2], "Expected own find");
    thm = simplify(Expr(READ, store, e[1]));
    if (thm.getRHS() == e[2]) {
      thm = d_rules->rewriteRedundantWrite1(thm, e);
      return transitivityRule(thm, simplify(thm.getRHS()));
    }
    if (isWrite(e[0])) {
      if (e[0][1] == e[1]) {
	return d_rules->rewriteRedundantWrite2(e);
      }
      if (e[0][1] > e[1]) {
	thm = d_rules->interchangeIndices(e);
	return transitivityRule(thm, simplify(thm.getRHS()));
      }
    }
    return reflexivityRule(e);
  }
  return reflexivityRule(e);
}


void TheoryArray::setup(const Expr& e)
{
  if (e.isNot() || e.isEq()) return;
  DebugAssert(e.isAtomic(), "e should be atomic");
  for (int k = 0; k < e.arity(); ++k) {
    e[k].addToNotify(this, e);
  }
  if (isRead(e)) {
    Theorem thm = reflexivityRule(e);
    e.setSig(thm);
    e.setRep(thm);
    // Record the read operator for concrete models
    TRACE("model", "TheoryArray: add array read ", e, "");
    d_reads.push_back(e);
  }
  else if (isWrite(e)) {
    // there is a hidden dependency of write(a,i,v) on read(a,i)
    Expr store = e[0];
    while (isWrite(store)) store = store[0];
    Expr r = simplifyExpr(Expr(READ, store, e[1]));
    theoryCore()->setupTerm(r, this, theoryCore()->getTheoremForTerm(e));
    DebugAssert(r.isAtomic(), "Should be atomic");
    DebugAssert(r != e[2], "Should have been rewritten");
    r.addToNotify(this, e);
  }
}


void TheoryArray::update(const Theorem& e, const Expr& d)
{
  int k, ar(d.arity());

  if (isRead(d)) {
    const Theorem& dEQdsig = d.getSig();
    if (!dEQdsig.isNull()) {
      Expr dsig = dEQdsig.getRHS();
      Theorem thm = updateHelper(d);
      Expr sigNew = thm.getRHS();
      if (sigNew == dsig) return;
      dsig.setRep(Theorem());
      if (isWrite(sigNew[0])) {
	thm = transitivityRule(thm, d_rules->rewriteReadWrite(sigNew));
	Theorem renameTheorem = renameExpr(d);
	enqueueFact(transitivityRule(symmetryRule(renameTheorem), thm));
	d.setSig(Theorem());
	enqueueFact(renameTheorem);
      }
      else {
	const Theorem& repEQsigNew = sigNew.getRep();
	if (!repEQsigNew.isNull()) {
	  d.setSig(Theorem());
	  enqueueFact(transitivityRule(repEQsigNew, symmetryRule(thm)));
	}
	else {
	  for (k = 0; k < ar; ++k) {
	    if (sigNew[k] != dsig[k]) {
	      sigNew[k].addToNotify(this, d);
	    }
	  }
	  d.setSig(thm);
	  sigNew.setRep(thm);
	}
      }
    }
  }
  else {
    DebugAssert(isWrite(d), "Expected write: d = "+d.toString());
    if (find(d).getRHS() == d) {
      Theorem thm = updateHelper(d);
      Expr sigNew = thm.getRHS();

      Expr store = sigNew[0];
      while (isWrite(store)) store = store[0];

      // TODO: calling simplify from update is generally bad
      Theorem thm2 = simplify(Expr(READ, store, sigNew[1]));
      if (thm2.getRHS() == sigNew[2]) {
        thm = transitivityRule(thm,
                               d_rules->rewriteRedundantWrite1(thm2, sigNew));
        sigNew = thm.getRHS();
      }
      else if (isWrite(sigNew[0])) {
        if (sigNew[0][1] == sigNew[1]) {
          thm = transitivityRule(thm, d_rules->rewriteRedundantWrite2(sigNew));
          sigNew = thm.getRHS();
        }
        else if (sigNew[0][1] > sigNew[1]) {
          thm = transitivityRule(thm, d_rules->interchangeIndices(sigNew));
          sigNew = thm.getRHS();
        }
      }

      if (d == sigNew) {
	// Hidden dependency must have changed.  Update notify list.
        DebugAssert(!e.isNull(), "Shouldn't be possible");
	e.getRHS().addToNotify(this, d);
      }
      else if (sigNew.isAtomic()) {
 	assertEqualities(thm);
      }
      else {
 	Theorem renameTheorem = renameExpr(d);
 	enqueueFact(transitivityRule(symmetryRule(renameTheorem), thm));
 	assertEqualities(renameTheorem);
      }
    }
  }
}


Theorem TheoryArray::solve(const Theorem& eThm)
{
  const Expr& e = eThm.getExpr();
  DebugAssert(e.isEq(), "TheoryArray::solve("+e.toString()+")");
  if (isWrite(e[0])) {
    DebugAssert(!isWrite(e[1]), "Should have been rewritten: e = "
		+e.toString());
    return symmetryRule(eThm);
  }
  return eThm;
}


void TheoryArray::checkType(const Expr& e)
{
  switch (e.getKind()) {
    case ARRAY: {
      if (e.arity() != 2) throw Exception
          ("ARRAY type should have two arguments");
      Type t1(e[0]);
      if (t1.isBool()) throw Exception
          ("Array index types must be non-Boolean");
      if (t1.isFunction()) throw Exception
          ("Array index types cannot be functions");
      Type t2(e[1]);
      if (t2.isBool()) throw Exception
          ("Array value types must be non-Boolean");
      if (t2.isFunction()) throw Exception
          ("Array value types cannot be functions");
      break;
    }
    default:
      DebugAssert(false, "Unexpected kind in TheoryArray::checkType"
                  +getEM()->getKindName(e.getKind()));
  }

}


void TheoryArray::computeType(const Expr& e)
{
  switch (e.getKind()) {
    case READ: {
      DebugAssert(e.arity() == 2,"");
      Type arrType = e[0].getType();
      if (!isArray(arrType)) {
        arrType = getBaseType(arrType);
      }
      if (!isArray(arrType))
	throw TypecheckException
	  ("Expected an ARRAY type in\n\n  "
	   +e[0].toString()+"\n\nBut received this:\n\n  "
	   +arrType.toString()+"\n\nIn the expression:\n\n  "
	   +e.toString());
      Type idxType = getBaseType(e[1]);
      if(getBaseType(arrType[0]) != idxType && idxType != Type::anyType(getEM())) {
	throw TypecheckException
	  ("The type of index expression:\n\n  "
	   +idxType.toString()
	   +"\n\nDoes not match the ARRAY index type:\n\n  "
	   +arrType[0].toString()
	   +"\n\nIn the expression: "+e.toString());
      }
      e.setType(arrType[1]);
      break;
    }
    case WRITE: {
      DebugAssert(e.arity() == 3,"");
      Type arrType = e[0].getType();
      if (!isArray(arrType)) {
        arrType = getBaseType(arrType);
      }
      Type idxType = getBaseType(e[1]);
      Type valType = getBaseType(e[2]);
      if (!isArray(arrType))
	throw TypecheckException
	  ("Expected an ARRAY type in\n\n  "
	   +e[0].toString()+"\n\nBut received this:\n\n  "
	   +arrType.toString()+"\n\nIn the expression:\n\n  "
	   +e.toString());
      bool idxCorrect = getBaseType(arrType[0]) == idxType || idxType == Type::anyType(getEM());
      bool valCorrect = getBaseType(arrType[1]) == valType || valType == Type::anyType(getEM());;
      if(!idxCorrect) {
	throw TypecheckException
	  ("The type of index expression:\n\n  "
	   +idxType.toString()
	   +"\n\nDoes not match the ARRAY's type index:\n\n  "
	   +arrType[0].toString()
	   +"\n\nIn the expression: "+e.toString());
      }
      if(!valCorrect) {
	throw TypecheckException
	  ("The type of value expression:\n\n  "
	   +valType.toString()
	   +"\n\nDoes not match the ARRAY's value type:\n\n  "
	   +arrType[1].toString()
	   +"\n\nIn the expression: "+e.toString());
      }
      e.setType(arrType);
      break;
    }
    case ARRAY_LITERAL: {
      DebugAssert(e.isClosure(), "TheoryArray::computeType("+e.toString()+")");
      DebugAssert(e.getVars().size()==1,
		  "TheoryArray::computeType("+e.toString()+")");
      Type ind(e.getVars()[0].getType());
      e.setType(arrayType(ind, e.getBody().getType()));
      break;
    }
    default:
      DebugAssert(false,"Unexpected type");
      break;
  }
}


Type TheoryArray::computeBaseType(const Type& t) {
  const Expr& e = t.getExpr();
  DebugAssert(e.getKind()==ARRAY && e.arity() == 2,
	      "TheoryArray::computeBaseType("+t.toString()+")");
  vector<Expr> kids;
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {
    kids.push_back(getBaseType(Type(*i)).getExpr());
  }
  return Type(Expr(e.getOp(), kids));
}


void TheoryArray::computeModelTerm(const Expr& e, std::vector<Expr>& v) {
  switch(e.getKind()) {
  case WRITE:
    // a WITH [i] := v -- report a, i and v as the model terms.
//     getModelTerm(e[1], v);
//     getModelTerm(e[2], v);
    v.push_back(e[0]);
    v.push_back(e[1]);
    v.push_back(e[2]);
    break;
  case READ:
    // For a[i], add the index i
    // getModelTerm(e[1], v);
    v.push_back(e[1]);
    // And continue to collect the reads a[i][j] (remember, e is of
    // ARRAY type)
  default:
    // For array terms, find all their reads
    if(e.getType().getExpr().getKind() == ARRAY) {
      for(CDList<Expr>::const_iterator i=d_reads.begin(), iend=d_reads.end();
	  i!=iend; ++i) {
	DebugAssert(isRead(*i) && (*i).arity()==2, "Bad array read: "
		    +(*i).toString());
	if((*i)[0] == e) {
	  // Add both the read operator a[i]
	  // getModelTerm(*i, v);
	  v.push_back(*i);
      // and the index 'i' to the model terms.  Reason: the index to
      // the array should better be a concrete value, and it might not
      // necessarily be in the current list of model terms.
	  // getModelTerm((*i)[1], v);
	  v.push_back((*i)[1]);
	}
      }
    }
    break;
  }
}


void TheoryArray::computeModel(const Expr& e, std::vector<Expr>& v) {
  static unsigned count(0); // For bound vars

  switch(e.getKind()) {
  case WRITE: {
    // We should already have a value for the original array
    Expr res(getModelValue(e[0]).getRHS());
    Expr ind(getEM()->newBoundVarExpr("arr_var", int2string(count++)));
    Type tp(e.getType());
    DebugAssert(isArray(tp) && tp.arity()==2,
		"TheoryArray::computeModel(WRITE)");
    ind.setType(tp[0]);
    res = rewrite(Expr(READ, res, ind)).getRHS();
    Expr indVal(getModelValue(e[1]).getRHS());
    Expr updVal(getModelValue(e[2]).getRHS());
    res = (ind.eqExpr(indVal)).iteExpr(updVal, res);
    res = arrayLiteral(ind, res);
    assignValue(e, res);
    v.push_back(e);
    break;
  }
//   case READ: {
//     // Get the assignment for the index
//     Expr idx(getModelValue(e[1]).getRHS());
//     // And the assignment for the 
//     var = read(idxThm.getRHS(), e[0]);
//   }
    // And continue to collect the reads a[i][j] (remember, e is of
    // ARRAY type)
  default: {
    // Assign 'e' a value later.
    v.push_back(e);
    // Map of e[i] to val for concrete values of i and val
    ExprHashMap<Expr> reads;
    // For array terms, find all their reads
    DebugAssert(getBaseType(e).getExpr().getKind() == ARRAY, "");

    for(CDList<Expr>::const_iterator i=d_reads.begin(), iend=d_reads.end();
	i!=iend; ++i) {
      TRACE("model", "TheoryArray::computeModel: read = ", *i, "");
      DebugAssert(isRead(*i) && (*i).arity()==2, "Bad array read: "
		  +(*i).toString());
      if((*i)[0] == e) {
	// Get the value of the index
	Theorem asst(getModelValue((*i)[1]));
	Expr var;
	if(asst.getLHS()!=asst.getRHS()) {
	  vector<Theorem> thms;
	  vector<unsigned> changed;
	  thms.push_back(asst);
	  changed.push_back(1);
	  Theorem subst(substitutivityRule(*i, changed, thms));
	  assignValue(transitivityRule(symmetryRule(subst),
				       getModelValue(*i)));
	  var = subst.getRHS();
	} else
	  var = *i;
	if(d_applicationsInModel) v.push_back(var);
	// Record it in the map
	Expr val(getModelValue(var).getRHS());
	DebugAssert(!val.isNull(), "TheoryArray::computeModel(): Variable "
		    +var.toString()+" has a Null value");
	reads[var] = val;
      }
    }
    // Create an array literal
    if(reads.size()==0) { // Leave the array uninterpreted
      assignValue(reflexivityRule(e));
    } else {
      // Bound var for the index
      Expr ind(getEM()->newBoundVarExpr("arr_var", int2string(count++)));
      Type tp(e.getType());
      DebugAssert(isArray(tp) && tp.arity()==2,
		  "TheoryArray::computeModel(WRITE)");
      ind.setType(tp[0]);
      ExprHashMap<Expr>::iterator i=reads.begin(), iend=reads.end();
      DebugAssert(i!=iend,
		  "TheoryArray::computeModel(): expected the reads "
		  "table be non-empty");
      // Use one of the concrete values as a default
      Expr res((*i).second);
      ++i;
      DebugAssert(!res.isNull(), "TheoryArray::computeModel()");
      for(; i!=iend; ++i) {
	// Optimization: if the current value is the same as that of the
	// next application, skip this case; i.e. keep 'res' instead of
	// building ite(cond, res, res).
	if((*i).second == res) continue;
	// ITE condition
	Expr cond = ind.eqExpr((*i).first[1]);
	res = cond.iteExpr((*i).second, res);
      }
      // Construct the array literal
      res = arrayLiteral(ind, res);
      assignValue(e, res);
    }
    break;
  }
  }
}


Expr TheoryArray::computeTCC(const Expr& e)
{
  Expr tcc(Theory::computeTCC(e));
  switch (e.getKind()) {
    case READ:
      DebugAssert(e.arity() == 2,"");
      return tcc.andExpr(getTypePred(e[0].getType()[0], e[1]));
    case WRITE: {
      DebugAssert(e.arity() == 3,"");
      Type arrType = e[0].getType();
      return rewriteAnd(getTypePred(arrType[0], e[1]).andExpr
                        (getTypePred(arrType[1], e[2])).andExpr(tcc)).getRHS();
    }
    case ARRAY_LITERAL: {
      return tcc;
    }
    default:
      DebugAssert(false,"TheoryArray::computeTCC: Unexpected expression: "
		  +e.toString());
      return tcc;
  }
}


///////////////////////////////////////////////////////////////////////////////
// Pretty-printing			                                     //
///////////////////////////////////////////////////////////////////////////////


ExprStream& TheoryArray::print(ExprStream& os, const Expr& e)
{
  d_theoryUsed = true;
  if (theoryCore()->getTranslator()->printArrayExpr(os, e)) return os;
  switch(os.lang()) {
  case PRESENTATION_LANG:
    switch(e.getKind()) {
    case READ:
      if(e.arity() == 1)
	os << "[" << push << e[0] << push << "]";
      else
	os << e[0] << "[" << push << e[1] << push << "]";
      break;
    case WRITE:
      os << "(" << push << e[0] << space << "WITH [" 
	 << push << e[1] << "] := " << push << e[2] << push << ")";
      break;
    case ARRAY:
      os << "ARRAY" << space << e[0] << space << "OF" << space << e[1];
      break;
    case ARRAY_LITERAL:
      if(e.isClosure()) {
	const vector<Expr>& vars = e.getVars();
	const Expr& body = e.getBody();
	os << "(" << push << "ARRAY" << space << "(" << push;
	bool first(true);
	for(size_t i=0; i<vars.size(); ++i) {
	  if(first) first=false;
	  else os << push << "," << pop << space;
	  os << vars[i];
	  if(vars[i].isVar())
	    os << ":" << space << pushdag << vars[i].getType() << popdag;
	}
	os << push << "):" << pop << pop << space << body << push << ")";
      } else
	e.printAST(os);
      break;
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case PRESENTATION_LANGUAGE
  case SMTLIB_LANG:
    switch(e.getKind()) {
    case READ:
      if(e.arity() == 2)
	os << "(" << push << "select" << space << e[0]
	   << space << e[1] << push << ")";
      else
	e.printAST(os);
      break;
    case WRITE:
      if(e.arity() == 3)
	os << "(" << push << "store" << space << e[0]
	   << space << e[1] << space << e[2] << push << ")";
      else
	e.printAST(os);
      break;
    case ARRAY:
      throw SmtlibException("ARRAY should be handled by printArrayExpr");
      break;      
    default:
      throw SmtlibException("TheoryArray::print: default not supported");
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case LISP_LANGUAGE
  case LISP_LANG:
    switch(e.getKind()) {
    case READ:
      if(e.arity() == 2)
	os << "(" << push << "READ" << space << e[0]
	   << space << e[1] << push << ")";
      else
	e.printAST(os);
      break;
    case WRITE:
      if(e.arity() == 3)
	os << "(" << push << "WRITE" << space << e[0]
	   << space << e[1] << space << e[2] << push << ")";
      else
	e.printAST(os);
      break;
    case ARRAY:
      os << "(" << push << "ARRAY" << space << e[0]
	 << space << e[1] << push << ")";
      break;      
    default:
      // Print the top node in the default LISP format, continue with
      // pretty-printing for children.
      e.printAST(os);
    }
    break; // end of case LISP_LANGUAGE
  default:
    // Print the top node in the default LISP format, continue with
    // pretty-printing for children.
    e.printAST(os);
  }
  return os;
}

//////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryArray::parseExprOp(const Expr& e) {
  //  TRACE("parser", "TheoryArray::parseExprOp(", e, ")");
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryArray::parseExprOp:\n e = "+e.toString());
  
  const Expr& c1 = e[0][0];
  int kind = getEM()->getKind(c1.getString());
  switch(kind) {
    case READ: 
      if(!(e.arity() == 3))
	throw ParserException("Bad array access expression: "+e.toString());
      return Expr(READ, parseExpr(e[1]), parseExpr(e[2]));
    case WRITE: 
      if(!(e.arity() == 4))
	throw ParserException("Bad array update expression: "+e.toString());
      return Expr(WRITE, parseExpr(e[1]), parseExpr(e[2]), parseExpr(e[3]));
    case ARRAY: { 
      vector<Expr> k;
      Expr::iterator i = e.begin(), iend=e.end();
      // Skip first element of the vector of kids in 'e'.
      // The first element is the operator.
      ++i; 
      // Parse the kids of e and push them into the vector 'k'
      for(; i!=iend; ++i) 
        k.push_back(parseExpr(*i));
      return Expr(kind, k, e.getEM());
      break;
    }
    case ARRAY_LITERAL: { // (ARRAY (v tp1) body)
      if(!(e.arity() == 3 && e[1].getKind() == RAW_LIST && e[1].arity() == 2))
	throw ParserException("Bad ARRAY literal expression: "+e.toString());
      const Expr& varPair = e[1];
      if(varPair.getKind() != RAW_LIST)
	throw ParserException("Bad variable declaration block in ARRAY "
			      "literal expression: "+varPair.toString()+
			      "\n e = "+e.toString());
      if(varPair[0].getKind() != ID)
	throw ParserException("Bad variable declaration in ARRAY"
			      "literal expression: "+varPair.toString()+
			      "\n e = "+e.toString());
      Type varTp(parseExpr(varPair[1]));
      vector<Expr> var;
      var.push_back(addBoundVar(varPair[0][0].getString(), varTp));
      Expr body(parseExpr(e[2]));
      // Build the resulting Expr as (LAMBDA (vars) body)
      return getEM()->newClosureExpr(ARRAY_LITERAL, var, body);
      break;
    }
    default:
      DebugAssert(false,
	  	  "TheoryArray::parseExprOp: wrong type: "
		  + e.toString());
    break;
  }
  return e;
}

namespace CVC3 {

Expr arrayLiteral(const Expr& ind, const Expr& body) {
  vector<Expr> vars;
  vars.push_back(ind);
  return body.getEM()->newClosureExpr(ARRAY_LITERAL, vars, body);
}

} // end of namespace CVC3
