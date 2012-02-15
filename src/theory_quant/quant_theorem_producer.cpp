/*****************************************************************************/
/*!
 * \file quant_theorem_producer.cpp
 * 
 * Author: Daniel Wichs
 * 
 * Created: Jul 07 22:22:38 GMT 2003
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
 * CLASS: QuantProofRules
 * 
 * 
 * Description: TRUSTED implementation of arithmetic proof rules.
 * 
 */
/*****************************************************************************/

// This code is trusted
#define _CVC3_TRUSTED_


#include "quant_theorem_producer.h"
#include "theory_quant.h"
#include "theory_core.h"


using namespace std;
using namespace CVC3;


QuantProofRules* TheoryQuant::createProofRules() {
  return new QuantTheoremProducer(theoryCore()->getTM(), this);
}
  

#define CLASS_NAME "CVC3::QuantTheoremProducer"


//! ==> NOT FORALL (vars): e  IFF EXISTS (vars) NOT e
Theorem
QuantTheoremProducer::rewriteNotForall(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isForall(),
		"rewriteNotForall: expr must be NOT FORALL:\n"
		+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_forall", e);
  return newRWTheorem(e, e.getEM()->newClosureExpr(EXISTS, e[0].getVars(),
                                                   !e[0].getBody()),
                      Assumptions::emptyAssump(), pf);
}

Theorem
QuantTheoremProducer::addNewConst(const Expr& e) {
  Proof pf;
  if(withProof())
    pf = newPf("add_new_const", e);
  return newTheorem(e, Assumptions::emptyAssump(), pf);
}


//! ==> NOT EXISTS (vars): e  IFF FORALL (vars) NOT e
Theorem
QuantTheoremProducer::rewriteNotExists(const Expr& e) {
  if(CHECK_PROOFS) {
    CHECK_SOUND(e.isNot() && e[0].isExists(),
		"rewriteNotExists: expr must be NOT FORALL:\n"
		+e.toString());
  }
  Proof pf;
  if(withProof())
    pf = newPf("rewrite_not_exists", e);
  return newRWTheorem(e, e.getEM()->newClosureExpr(FORALL, e[0].getVars(),
                                                   !e[0].getBody()),
                      Assumptions::emptyAssump(), pf);
}

//! Instantiate a  universally quantified formula
/*! From T|-FORALL(var): e generate T|-psi => e' where e' is obtained
 * from e by instantiating bound variables with terms in
 * vector<Expr>& terms.  The vector of terms should be the same
 * size as the vector of bound variables in e. Also elements in
 * each position i need to have matching base types. psi is the conjunction of 
 * subtype predicates for the bound variables of the quanitfied expression.
 * \param t1 is the quantifier (a Theorem)
 * \param terms are the terms to instantiate.
 */
Theorem QuantTheoremProducer::universalInst(const Theorem& t1, const  vector<Expr>& terms, int quantLevel){

  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();
  if(CHECK_PROOFS) {
    if(boundVars.size() != terms.size()){
      char * a;
      a[100000]='a';
    }
    CHECK_SOUND(boundVars.size() == terms.size(), 
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());
    for(unsigned int i=0; i<terms.size(); i++)
      CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
                  d_theoryQuant->getBaseType(terms[i]),
	      "Universal instantiation: type mismatch");
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  unsigned qlevel, qlevelMax = 0;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
    qlevel = d_theoryQuant->theoryCore()->getQuantLevelForTerm(terms[i]);
    if (qlevel > qlevelMax) qlevel = qlevelMax;
  }
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.insert(es.end(), terms.begin(), terms.end());
    pf= newPf("universal_elimination", es, pfs);
  }
   Expr inst = e.getBody().substExpr(e.getVars(), terms);
   Expr imp;
   if(typePred == tr)
     imp = inst;
   else
     imp = typePred.impExpr(inst); 
   Theorem ret = newTheorem(imp, t1.getAssumptionsRef(), pf);
   //   ret.setQuantLevel(qlevel+1);
   ret.setQuantLevel(quantLevel+1);
   return ret;
}

Theorem QuantTheoremProducer::universalInst(const Theorem& t1, const  vector<Expr>& terms){

  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();
  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size() == terms.size(), 
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());
    for(unsigned int i=0; i<terms.size(); i++)
      CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
                  d_theoryQuant->getBaseType(terms[i]),
	      "Universal instantiation: type mismatch");
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  unsigned qlevel, qlevelMax = 0;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
    qlevel = d_theoryQuant->theoryCore()->getQuantLevelForTerm(terms[i]);
    if (qlevel > qlevelMax) qlevel = qlevelMax;
  }
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.insert(es.end(), terms.begin(), terms.end());
    pf= newPf("universal_elimination", es, pfs);
  }
   Expr inst = e.getBody().substExpr(e.getVars(), terms);
   Expr imp;
   if(typePred == tr)
     imp = inst;
   else
     imp = typePred.impExpr(inst); 
   Theorem ret = newTheorem(imp, t1.getAssumptionsRef(), pf);
   ret.setQuantLevel(qlevel+1);
   return ret;
}


//! Instantiate a  universally quantified formula
Theorem QuantTheoremProducer::partialUniversalInst(const Theorem& t1, const
						   vector<Expr>& terms){
  Expr e = t1.getExpr();
  const vector<Expr>& boundVars = e.getVars();
  if(CHECK_PROOFS) {
    CHECK_SOUND(boundVars.size() >= terms.size(), 
		"Universal instantiation: size of terms array does "
		"not match quanitfied variables array size");
    CHECK_SOUND(e.isForall(),
		"universal instantiation: expr must be FORALL:\n"
		+e.toString());
    for(unsigned int i=0; i<terms.size(); i++){
      //      cout<<"bounVar:"<<boundVars[i].toString()<<":"<<d_theoryQuant->getBaseType(boundVars[i]).toString()<<endl;
      //      cout<<"term:"<<terms[i].toString()<<":"<<d_theoryQuant->getBaseType(terms[i]).toString()<<endl;
      CHECK_SOUND(d_theoryQuant->getBaseType(boundVars[i]) ==
                  d_theoryQuant->getBaseType(terms[i]),
	      "partial Universal instantiation: type mismatch");
    }
  }

  //build up a conjunction of type predicates for expression
  Expr tr = e.getEM()->trueExpr();
  Expr typePred = tr;
  for(unsigned int i=0; i<terms.size(); i++) {
    Expr p = d_theoryQuant->getTypePred(boundVars[i].getType(),terms[i]);
    if(p!=tr) {
      if(typePred==tr)
	typePred = p;
      else
	typePred = typePred.andExpr(p);
    }
  }
  Proof pf;
  if(withProof()) {
    vector<Proof> pfs;
    vector<Expr> es;
    pfs.push_back(t1.getProof());
    es.push_back(e);
    es.insert(es.end(), terms.begin(), terms.end());
    pf= newPf("partial_universal_instantiation", es, pfs);
  }
   

  if(terms.size() == boundVars.size()){
    Expr inst = e.getBody().substExpr(e.getVars(), terms);
    Expr imp;
    if(typePred == tr)
      imp = inst;
    else
      imp = typePred.impExpr(inst); 
    return(newTheorem(imp, t1.getAssumptionsRef(), pf));
  }
  else{
    vector<Expr> newBoundVars;
    for(size_t i=0; i<terms.size(); i++) {
      newBoundVars.push_back(boundVars[i]);
    }
    
    vector<Expr>leftBoundVars;
    for(size_t i=terms.size(); i<boundVars.size(); i++) {
      leftBoundVars.push_back(boundVars[i]);
    }
    
    Expr tempinst = e.getBody().substExpr(newBoundVars, terms);
    Expr inst = d_theoryQuant->getEM()->newClosureExpr(FORALL, leftBoundVars, tempinst);

    Expr imp;
    if(typePred == tr)
      imp = inst;
    else
      imp = typePred.impExpr(inst); 
    return(newTheorem(imp, t1.getAssumptionsRef(), pf));
    
  }
}

//! find all bound variables in e and maps them to true in boundVars
void QuantTheoremProducer::recFindBoundVars(const Expr& e, 
		           ExprMap<bool> & boundVars, ExprMap<bool> &visited) 
{
  if(visited.count(e)>0)
    return;
  else
    visited[e] = true;
  if(e.getKind() == BOUND_VAR)
    boundVars[e] = true;
  if(e.getKind() == EXISTS || e.getKind() == FORALL)
    recFindBoundVars(e.getBody(), boundVars, visited);
  for(Expr::iterator it = e.begin(); it!=e.end(); ++it)
    recFindBoundVars(*it, boundVars, visited);
  
}

//!adjust the order of bound vars, newBvs begin first
Theorem QuantTheoremProducer::adjustVarUniv(const Theorem& t1, const std::vector<Expr>& newBvs){
  const Expr e=t1.getExpr();
  const Expr body = e.getBody();
  if(CHECK_PROOFS) {
      CHECK_SOUND(e.isForall(),
		"adjustVarUniv: "
		+e.toString());
  }

  const vector<Expr>& origVars = e.getVars();

 
  ExprMap<bool> oldmap; 
  for(vector<Expr>::const_iterator it = origVars.begin(), 
	iend=origVars.end(); it!=iend; ++it)    {
    oldmap[*it]=true;
  }
  
  vector<Expr> quantVars;
  for(vector<Expr>::const_iterator it = newBvs.begin(), 
	iend=newBvs.end(); it!=iend; ++it)    {
    if(oldmap.count(*it) > 0)
      quantVars.push_back(*it);
  }
  
  if(quantVars.size() == origVars.size())
    return t1;

  ExprMap<bool> newmap; 
  for(vector<Expr>::const_iterator it = newBvs.begin(), 
	iend=newBvs.end(); it!=iend; ++it)    {
    newmap[*it]=true;
  }

  for(vector<Expr>::const_iterator it = origVars.begin(), 
	iend=origVars.end(); it!=iend; ++it)    {
    if(newmap.count(*it)<=0){
      quantVars.push_back(*it);
    };
  }

  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e);
    es.insert(es.end(), quantVars.begin(), quantVars.end());
    pfs.push_back(t1.getProof());
    pf= newPf("adjustVarUniv", es, pfs);
  }
  
  Expr newQuantExpr;
  newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, quantVars, body);

  return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
}

//!pack (forall (x) forall (y)) into (forall (x y))
Theorem QuantTheoremProducer::packVar(const Theorem& t1){
  const Expr e=t1.getExpr();

  if(CHECK_PROOFS) {
      CHECK_SOUND(e.isForall(),
		"packVar: "
		+e.toString());
  }

  vector<Expr> bVars = e.getVars();
  
  if(!e.getBody().isForall()){
    return t1;
  } 
  
  const Expr body=e.getBody().getBody();
  
  vector<Expr> bVarsLeft = e.getBody().getVars();
  for(vector<Expr>::iterator i=bVarsLeft.begin(), iend=bVarsLeft.end(); i!=iend; i++){
    bVars.push_back(*i);
  }
  
  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e);
    es.insert(es.end(), bVars.begin(), bVars.end());
    pfs.push_back(t1.getProof());
    pf= newPf("packVar", es, pfs);
  }
  
  Expr newQuantExpr;
  newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, bVars, body);

  return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
}

//!pack (forall (x) ... forall (y)) into (forall (x y)...)
Theorem QuantTheoremProducer::pullVarOut(const Theorem& t1){
  const Expr outForall=t1.getExpr();

  if(CHECK_PROOFS) {
      CHECK_SOUND(outForall.isForall(),
		"pullVarOut: "
		+outForall.toString());
  }

  const Expr outBody = outForall.getBody();
  
  if(!((outBody.isAnd() && outBody[1].isForall()) || 
       (outBody.isImpl() && outBody[1].isForall()) ||
       (outBody.isNot() && outBody[0].isAnd() && outBody[0][1].isExists()) )){
    return t1;
  }
  
  if((outBody.isNot() && outBody[0].isAnd() && outBody[0][1].isExists())){

    vector<Expr> bVarsOut = outForall.getVars();
    
    const Expr innerExists =outBody[0][1];
    const Expr innerBody = innerExists.getBody();
    vector<Expr> bVarsIn = innerExists.getVars();
        
    for(vector<Expr>::iterator i=bVarsIn.begin(), iend=bVarsIn.end(); i!=iend; i++){
      bVarsOut.push_back(*i);
    }
    
    Proof pf;
    if(withProof()) {
      vector<Expr> es;
      vector<Proof> pfs;
      es.push_back(outForall);
      es.insert(es.end(), bVarsIn.begin(), bVarsIn.end());
      pfs.push_back(t1.getProof());
      pf= newPf("pullVarOut", es, pfs);
    }
    
    Expr newbody;
    
    
    newbody=(outBody[0][0].notExpr()).orExpr(innerBody.notExpr());
        
    Expr newQuantExpr;
    newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, bVarsOut, newbody);

    //    cout<<"org thm|"<<t1.toString()<<endl;
    //    cout<<"new thm|"<<newQuantExpr.toString()<<endl;
    return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
  }
  else if ((outBody.isAnd() && outBody[1].isForall()) || 
	   (outBody.isImpl() && outBody[1].isForall())){
    
    vector<Expr> bVarsOut = outForall.getVars();
    
    const Expr innerForall=outBody[1];
    const Expr innerBody = innerForall.getBody();
    vector<Expr> bVarsIn = innerForall.getVars();
    
    for(vector<Expr>::iterator i=bVarsIn.begin(), iend=bVarsIn.end(); i!=iend; i++){
      bVarsOut.push_back(*i);
    }
    
    Proof pf;
    if(withProof()) {
      vector<Expr> es;
      vector<Proof> pfs;
      es.push_back(outForall);
      es.insert(es.end(), bVarsIn.begin(), bVarsIn.end());
      pfs.push_back(t1.getProof());
      pf= newPf("pullVarOut", es, pfs);
    }
    
    Expr newbody;
    if(outBody.isAnd()){
      newbody=outBody[0].andExpr(innerBody);
    }
    else if(outBody.isImpl()){
      newbody=outBody[0].impExpr(innerBody);
    }
    
    
    Expr newQuantExpr;
    newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, bVarsOut, newbody);
    
    return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
  }
  FatalAssert(false, "Should be unreachable");
  return Theorem(); // to disable compiler warning
}



/*! @brief From T|- QUANTIFIER (vars): e we get T|-QUANTIFIER(vars') e
 * where vars' is obtained from vars by removing all bound variables
 *  not used in e. If vars' is empty the produced theorem is just T|-e
 */
Theorem QuantTheoremProducer::boundVarElim(const Theorem& t1)
{
  const Expr e=t1.getExpr();
  const Expr body = e.getBody();
  if(CHECK_PROOFS) {
      CHECK_SOUND(e.isForall() || e.isExists(),
		"bound var elimination: "
		+e.toString());
  }
  ExprMap<bool> boundVars; //a mapping of bound variables in the body to true
  ExprMap<bool> visited; //to make sure expressions aren't traversed
			  //multiple times
  recFindBoundVars(body, boundVars, visited);
  vector<Expr> quantVars;
  const vector<Expr>& origVars = e.getVars();
  for(vector<Expr>::const_iterator it = origVars.begin(), 
	iend=origVars.end(); it!=iend; ++it)
    {
    if(boundVars.count(*it) > 0)
      quantVars.push_back(*it);
    }

  // If all variables are used, just return the original theorem
  if(quantVars.size() == origVars.size())
    return t1;

  Proof pf;
  if(withProof()) {
    vector<Expr> es;
    vector<Proof> pfs;
    es.push_back(e);
    es.insert(es.end(), quantVars.begin(), quantVars.end());
    pfs.push_back(t1.getProof());
    pf= newPf("bound_variable_elimination", es, pfs);
  }
  if(quantVars.size() == 0)
    return(newTheorem(e.getBody(), t1.getAssumptionsRef(), pf));
  
  Expr newQuantExpr;
  if(e.isForall())
    newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(FORALL, quantVars, body);
  else
    newQuantExpr = d_theoryQuant->getEM()->newClosureExpr(EXISTS, quantVars, body);

  return(newTheorem(newQuantExpr, t1.getAssumptionsRef(), pf));
}
