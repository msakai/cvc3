/*****************************************************************************/
/*! 
 * \file theory_quant.cpp
 * 
 * Author: Daniel Wichs, Yeting Ge
 * 
 * Created: Wednesday July 2, 2003
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
#include "theory_quant.h"
#include "theory_arith.h"
#include "theory_array.h"
#include "typecheck_exception.h"
#include "parser_exception.h"
#include "smtlib_exception.h"
#include "quant_proof_rules.h"
#include "theory_core.h"
#include "command_line_flags.h"
#include "vcl.h"
#include<string>
#include<string.h>
#include <algorithm>
using namespace std;
using namespace CVC3;

///////////////////////////////////////////////////////////////////////////////
// TheoryQuant Public Methods                                                 //
///////////////////////////////////////////////////////////////////////////////

static const Expr null_expr;
const int FOUND_FALSE = 1;

Trigger::Trigger(TheoryCore* core, Expr e, Polarity pol, std::set<Expr> boundVars){
  trig=e ;
  polarity=pol;
  head=null_expr;
  hasRWOp=false;
  hasTrans=false;
  hasT2=false;
  isSimple=false;
  isSuperSimple=false;
  isMulti=false;
  multiIndex = 99999;
  multiId = 99999;
  for(std::set<Expr>::const_iterator i=boundVars.begin(),iend=boundVars.end(); i!=iend; ++i)
    bvs.push_back(*i);
}

bool Trigger::isPos(){
  return (Pos==polarity||PosNeg==polarity);
}

bool Trigger::isNeg(){
  return (Neg==polarity || PosNeg==polarity);
}

std::vector<Expr> Trigger::getBVs(){
  return bvs;
}

Expr Trigger::getEx(){
  return trig;
}

void Trigger::setHead(Expr h){
  head=h; 
}

Expr Trigger::getHead(){
  return head;
}

void Trigger::setRWOp(bool b){
  hasRWOp =b ; 
}

bool Trigger::hasRW(){
  return hasRWOp;
}

void Trigger::setTrans(bool b){
  hasTrans =b ; 
}

bool Trigger::hasTr(){
  return hasTrans;
}

void Trigger::setTrans2(bool b){
  hasT2 =b ; 
}

bool Trigger::hasTr2(){
  return hasT2;
}

void Trigger::setSimp(){
  isSimple =true ; 
}

bool Trigger::isSimp(){
  return isSimple;
}

void Trigger::setSuperSimp(){
  isSuperSimple =true ; 
}

bool Trigger::isSuperSimp(){
  return isSuperSimple;
}

void Trigger::setMultiTrig(){
  isMulti = true ; 
}

bool Trigger::isMultiTrig(){
  return isMulti;
}


dynTrig::dynTrig(Trigger t, ExprMap<Expr> b, size_t id)
  :trig(t),
   univ_id(id),
   binds(b)
{}

TheoryQuant::TheoryQuant(TheoryCore* core) //!< Constructor
  : Theory(core, "Quantified Expressions"),
    d_univs(core->getCM()->getCurrentContext()),    
    d_rawUnivs(core->getCM()->getCurrentContext()),    
    d_arrayTrigs(core->getCM()->getCurrentContext()),    
    d_lastArrayPos(core->getCM()->getCurrentContext(), 0 , 0),    
    d_lastPredsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastTermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastPartPredsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastPartTermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_univsPartSavedPos(core->getCM()->getCurrentContext(), 0, 0),
    d_lastPartLevel(core->getCM()->getCurrentContext(), 0, 0),
    d_usefulGterms(core->getCM()->getCurrentContext()),
    d_lastUsefulGtermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_savedTermsPos(core->getCM()->getCurrentContext(), 0, 0),
    d_univsSavedPos(core->getCM()->getCurrentContext(), 0, 0),
    d_rawUnivsSavedPos(core->getCM()->getCurrentContext(), 0, 0),
    d_univsPosFull(core->getCM()->getCurrentContext(), 0, 0),
    d_univsContextPos(core->getCM()->getCurrentContext(), 0, 0),
    d_instCount(core->getCM()->getCurrentContext(), 0,0),
    d_contextTerms(core->getCM()->getCurrentContext()),
    d_contextCache(core->getCM()->getCurrentContext()),
    d_maxQuantInst(&(core->getFlags()["max-quant-inst"].getInt())),
    d_useNew(&(core->getFlags()["quant-new"].getBool())),
    d_useLazyInst(&(core->getFlags()["quant-lazy"].getBool())),
    d_useSemMatch(&(core->getFlags()["quant-sem-match"].getBool())),
    d_useAtomSem(&(core->getFlags()["quant-const-match"].getBool())),
    d_translate(&(core->getFlags()["translate"].getBool())),
    d_useTrigNew(&(core->getFlags()["quant-trig-new"].getBool())),
    d_usePart(&(core->getFlags()["quant-inst-part"].getBool())),
    d_useMult(&(core->getFlags()["quant-inst-mult"].getBool())),
    d_useInstEnd(&(core->getFlags()["quant-inst-end"].getBool())),
    d_useInstLCache(&(core->getFlags()["quant-inst-lcache"].getBool())),
    d_useInstGCache(&(core->getFlags()["quant-inst-gcache"].getBool())),
    d_useInstTrue(&(core->getFlags()["quant-inst-true"].getBool())),
    d_usePullVar(&(core->getFlags()["quant-pullvar"].getBool())),
    d_useExprScore(&(core->getFlags()["quant-score"].getBool())),
    d_useTrigLoop(&(core->getFlags()["quant-trig-loop"].getInt())),
    d_maxInst(&(core->getFlags()["quant-max-inst"].getInt())),
    d_useTrans(&(core->getFlags()["quant-trans3"].getBool())),
    d_useTrans2(&(core->getFlags()["quant-trans2"].getBool())),
    d_useInstAll(&(core->getFlags()["quant-inst-all"].getBool())),
    d_usePolarity(&(core->getFlags()["quant-polarity"].getBool())),
    d_useEqu(&(core->getFlags()["quant-equ"].getBool())),
    d_maxNaiveCall(&(core->getFlags()["quant-naive-num"].getInt())),
    d_curMaxExprScore(core->getCM()->getCurrentContext(), (core->getFlags()["quant-max-score"].getInt()),0),
    d_arrayIndic(core->getCM()->getCurrentContext()),
    d_exprLastUpdatedPos(core->getCM()->getCurrentContext(),0 ,0),
    d_trans_found(core->getCM()->getCurrentContext()),
    d_trans2_found(core->getCM()->getCurrentContext()),
    null_cdlist(core->getCM()->getCurrentContext()),
    d_eqs(core->getCM()->getCurrentContext()),
    d_eqs_pos(core->getCM()->getCurrentContext(), 0, 0),
    d_allInstCount(core->getStatistics().counter("quantifier instantiations")),
    d_partCalled(core->getCM()->getCurrentContext(),false,0),
    d_instHistory(core->getCM()->getCurrentContext()),
    d_alltrig_list(core->getCM()->getCurrentContext())
{
  IF_DEBUG(d_univs.setName("CDList[TheoryQuant::d_univs]"));
  vector<int> kinds;
  d_instCount = 0;
  d_cacheThmPos=0;
  d_trans_num=0;
  d_trans2_num=0;
  d_rules=createProofRules();
  kinds.push_back(EXISTS);
  kinds.push_back(FORALL);
  registerTheory(this, kinds);
  d_partCalled=false;
  d_offset_multi_trig=2;
  d_initMaxScore=(theoryCore()->getFlags()["quant-max-score"].getInt());
  for(size_t i=0; i<MAX_TRIG_BVS; i++){
    d_mybvs[i] = getEM()->newBoundVarExpr("_genbv", int2string(i), Type::anyType(getEM()));
  }
}

//! Destructor
TheoryQuant::~TheoryQuant() {
  if(d_rules != NULL) delete d_rules;
  for(std::map<Type, CDList<size_t>* ,TypeComp>::iterator 
	it = d_contextMap.begin(), iend = d_contextMap.end(); 
      it!= iend; ++it) {
    delete it->second;
     free(it->second);
  }
}

int TheoryQuant::getExprScore(const Expr& e){
  return theoryCore()->getQuantLevelForTerm(e);
}

bool isSysPred(const Expr& e){
  return ( isLE(e) || isLT(e) || isGE(e) || isGT(e) || e.isEq());
}

bool canGetHead(const Expr& e){ 
  return (e.getKind() == APPLY || e.getKind() == READ || e.getKind() == WRITE); 
} 

bool isSimpleTrig(const Expr& t){
  if(!canGetHead(t)) return false; 
  for(int i = 0; i < t.arity(); i++){
    if (t[i].arity()>0 && t[i].containsBoundVar()) return false;
    if (BOUND_VAR == t[i].getKind()){
      for(int j = 0; j < i; j++){
	if(t[i] == t[j]) return false;
      }
    } 
  }
  return true;
}

bool isSuperSimpleTrig(const Expr& t){
  if(!isSimpleTrig(t)) return false; 
  for(int i = 0; i < t.arity(); i++){
    if (t[i].arity()>0 ) return false;
    if (BOUND_VAR != t[i].getKind()){
      return false;
    }
  } 
  return true;
}


bool usefulInMatch(const Expr& e){
  if(e.arity() == 0){
    TRACE("usefulInMatch", e.toString()+": ",e.arity(), "");
    TRACE("usefulInMatch", e.isRational(), "", "");
  }
  return ( canGetHead(e) || (isSysPred(e) && (!e.isEq()) ) );
} 

void TheoryQuant::setup(const Expr& e) {}

void TheoryQuant::update(const Theorem& t, const Expr& e) {
}

std::string vectorExpr2string(const std::vector<Expr> & vec){
  std::string buf;
  for(size_t i=0; i<vec.size(); i++){
    buf.append(vec[i].toString());
    buf.append(" # ");
  }
  return buf;
}

static void recursiveGetSubTrig(const Expr& e, std::vector<Expr> & res) {
  if(e.getFlag())
   return;

  if(e.isClosure())
    return recursiveGetSubTrig(e.getBody(),res); 

  if (e.isApply()|| isSysPred(e)){
    res.push_back(e);
  }
  else
    if ( e.isTerm() && (!e.isVar()) && (e.getKind()!=RATIONAL_EXPR) ) {
	res.push_back(e);
      }

  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)    {	
      recursiveGetSubTrig(*i,res);
    }
  
  e.setFlag();
  return ;
}

std::vector<Expr> getSubTrig(const Expr& e){
  e.clearFlags();
  std::vector<Expr> res;
  recursiveGetSubTrig(e,res);
  e.clearFlags();
  TRACE("getsub","e is ", e.toString(),"");
  TRACE("getsub","have ", res.size()," subterms");
  return res;
}

static void recGetSubTerms(const Expr& e, std::vector<Expr> & res) {
  if(e.getFlag())
   return;

  if(e.isClosure())
    return recGetSubTerms(e.getBody(),res); 

  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)  {	
    recGetSubTerms(*i,res);
  }

  res.push_back(e);

  e.setFlag();
  return ;
}

const std::vector<Expr>& TheoryQuant::getSubTerms(const Expr& e){
  //the last item in res is e itself
  ExprMap<std::vector<Expr> >::iterator iter= d_subTermsMap.find(e);
  if( d_subTermsMap.end() == iter){
    e.clearFlags();
    std::vector<Expr> res;
    recGetSubTerms(e,res);
    e.clearFlags();

    TRACE("getsubs", "getsubs, e is: ", e, "");
    TRACE("getsubs", "e has ", res.size(), " subterms");

    d_subTermsMap[e] = res;
    return d_subTermsMap[e];
  }
  else{
    return (*iter).second;
  }
}

void TheoryQuant::enqueueInst(const Theorem& univ, const vector<Expr>& bind, const Expr& gterm){
  static int max_score =-1;

  bool partInst=false;
  if(bind.size() < univ.getExpr().getVars().size()){
    partInst=false;
    TRACE("sendinst","partinst",partInst,"");
  }
  
  Expr bind_expr(RAW_LIST, bind, getEM());
  
  if (*d_useInstLCache){
    const Expr& e = univ.getExpr();
    ExprMap<CDMap<Expr,bool>*>::iterator iterCache = d_bindHistory.find(e);
    if (iterCache != d_bindHistory.end()){
      CDMap<Expr,bool>* cache = (*iterCache).second; 
      if(cache->find(bind_expr) !=cache->end()){
	return ;
      }
      else{
	(*cache)[bind_expr] = true;
      }
    }
    else{
      CDMap<Expr,bool>* new_cache = new(true) CDMap<Expr,bool> (theoryCore()->getCM()->getCurrentContext());
      (*new_cache)[bind_expr] = true;
    }
  }
  
  Theorem thm ;
  if(null_expr == gterm ){//it is from naive instantiation or multi-inst
    TRACE("sendinst","gterm",gterm,"");
    if(partInst) {
      thm = d_rules->partialUniversalInst(univ, bind, 0);
    }
    else{
      thm = d_rules->universalInst(univ, bind, 0);
    }
  }
  else{
    int gscore = theoryCore()->getQuantLevelForTerm(gterm);    
    if(gscore > max_score){
      max_score = gscore;
      //      cout<<"max score "<<max_score<<endl;
    }
    if(partInst) {
      thm = d_rules->partialUniversalInst(univ, bind, gscore);
    }
    else{
      thm = d_rules->universalInst(univ, bind, gscore);
    }
  }

  Theorem simpThm = simplify(thm.getExpr());  
  
  if(*d_useInstTrue){
    Expr res = simpThm.getRHS();
    if(res.isTrue()){
      return;
    }
    if(res.isFalse() ){
      enqueueFact(thm); 
      //      setInconsistent(simpThm);
      d_allInstCount++;
      d_instThisRound++;
      throw FOUND_FALSE;
    }
  }

  d_simplifiedThmQueue.push(thm);

  TRACE("quant sendinst", "=gterm: ",gterm, "");
  TRACE("quant sendinst", "==add fact simp =", simplifyExpr(thm.getExpr()), "");
  TRACE("quant sendinst", "==add fact org =", thm.getExpr(), "");
  TRACE("quant sendinst", "==add fact from= ", univ.getExpr(), "\n===: "+vectorExpr2string(bind)); 
}


void TheoryQuant::enqueueInst(size_t univ_id , const std::vector<Expr>& bind, const Expr& gterm){
  static int max_score =-1;

  const Theorem& univ = d_univs[univ_id]; 

  bool partInst=false;
  if(bind.size() < univ.getExpr().getVars().size()){
    partInst=false;
    TRACE("sendinst","partinst",partInst,"");
  }
  
  Expr bind_expr(RAW_LIST, bind, getEM());
  
  if (*d_useInstLCache){
    const Expr& e = univ.getExpr();
    ExprMap<CDMap<Expr,bool>*>::iterator iterCache = d_bindHistory.find(e);
    if (iterCache != d_bindHistory.end()){
      CDMap<Expr,bool>* cache = (*iterCache).second; 
      if(cache->find(bind_expr) !=cache->end()){
	return ;
      }
      else{
	(*cache)[bind_expr] = true;
      }
    }
    else{
      CDMap<Expr,bool>* new_cache = new(true) CDMap<Expr,bool> (theoryCore()->getCM()->getCurrentContext());
      (*new_cache)[bind_expr] = true;
    }
  }
  
  Theorem thm ;
  if(null_expr == gterm ){//it is from naive instantiation or multi-inst
    TRACE("sendinst","gterm",gterm,"");
    if(partInst) {
      thm = d_rules->partialUniversalInst(univ, bind, 0);
    }
    else{
      thm = d_rules->universalInst(univ, bind, 0);
    }
  }
  else{
    int gscore = theoryCore()->getQuantLevelForTerm(gterm);    
    if(gscore > max_score){
      max_score = gscore;
      //      cout<<"max score "<<max_score<<endl;
    }
    if(partInst) {
      thm = d_rules->partialUniversalInst(univ, bind, gscore);
    }
    else{
      thm = d_rules->universalInst(univ, bind, gscore);
    }
  }

  Theorem simpThm = simplify(thm.getExpr());  
  
  if(*d_useInstTrue){
    Expr res = simpThm.getRHS();
    if(res.isTrue()){
      return;
    }
    if(res.isFalse() ){
      enqueueFact(thm); 
      //      setInconsistent(simpThm);
      d_allInstCount++;
      d_instThisRound++;
      throw FOUND_FALSE;
    }
  }

  d_simplifiedThmQueue.push(thm);
  //  cout<<"enqueue inst"<<thm << endl;
  TRACE("quant sendinst", "=gterm: ",gterm, "");
  TRACE("quant sendinst", "==add fact simp =", simplifyExpr(thm.getExpr()), "");
  TRACE("quant sendinst", "==add fact org =", thm.getExpr(), "");
  TRACE("quant sendinst", "==add fact from= ", univ.getExpr(), "\n===: "+vectorExpr2string(bind)); 
}


void TheoryQuant::enqueueInst(const Theorem& univ, 
			      Trigger& trig, 
			      const std::vector<Expr>& binds,  
			      const Expr& gterm
			      ) {
  return enqueueInst(univ,binds,gterm);
}

int TheoryQuant::sendInstNew(){
  int resNum = 0 ;
  
  while(!d_simplifiedThmQueue.empty()){
    const Theorem thm = d_simplifiedThmQueue.front();
    d_simplifiedThmQueue.pop();
    
    d_allInstCount++;
    d_instThisRound++;
    resNum++;
    enqueueFact(thm);
  }

  return resNum;
}

void TheoryQuant::addNotify(const Expr& e){}

int recursiveExprScore(const Expr& e) {
  int res=0;
  DebugAssert(!(e.isClosure()), "exprScore called on closure");
  
  if(e.arity()== 0){
    res = 0;
  }
  else{
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i)  {	
      res += recursiveExprScore(*i);
    }
  }
  res++;
  return res;
}

int exprScore(const Expr& e){
  return recursiveExprScore(e);
}

Expr getHeadExpr(const Expr& e){
  if (e.getKind() == APPLY){
    return e.getOp().getExpr();
  }
  
  if ( READ == e.getKind() || WRITE == e.getKind() )  {
    int kind = e[0].getKind();
    if (UCONST==kind) {
      return e[0];
    }
    else if (APPLY==kind || UFUNC == kind || READ == kind || WRITE == kind){
      return getHeadExpr(e[0]);
    }
    else if(e[0].isSkolem()){
      return e[0];
    }
  }

  return null_expr;
}

Expr  getHead(const Expr& e) {
  return getHeadExpr(e);
}

//! get the bound vars in term e,
static bool recursiveGetBoundVars(const Expr& e, std::set<Expr>& result) {
  bool res(false);
  if(e.getFlag()){
    return e.containsBoundVar();
  }
  else if(e.isClosure()){
    res = recursiveGetBoundVars(e.getBody(),result); 
  }
  else if (BOUND_VAR == e.getKind() ){
    result.insert(e);
    e.setContainsBoundVar();
    res = true;
  }
  else {
    res = false;
    for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i){	
      if(recursiveGetBoundVars(*i,result)){
	res = true;
      }
    }
  }

  e.setFlag();
  
  if(res) {
    e.setContainsBoundVar();
  }

  return res;
}


//! get bound vars in term e, 
std::set<Expr>  getBoundVars(const Expr& e){
  /*  
  //  static ExprMap<std::set<Expr> > bvsCache;
  static std::map<Expr, std::set<Expr> > bvsCache;
  std::map<Expr, std::set<Expr> >::iterator iterCache = bvsCache.find(e);
  //ExprMap<std::set<Expr> >::iterator iterCache = bvsCache.find(e);

  if (iterCache != bvsCache.end()){
    //    return iterCache->second; 
    return (*iterCache).second; 
  }
  */
  e.clearFlags(); 
  std::set<Expr> result ;   
  recursiveGetBoundVars(e,result);
  e.clearFlags();
  //  bvsCache[e]=result;
  return  result;
}

bool isGoodSysPredTrigger(const Expr& e){
  if(!isSysPred(e)) return false;
  if(usefulInMatch(e[0]) || usefulInMatch(e[1])) return true;
  return false;
}

bool isGoodFullTrigger(const Expr& e, const std::vector<Expr>& bVarsThm){
  if( !usefulInMatch(e))
    return false;
  
  const std::set<Expr>& bvs = getBoundVars(e);

  if (bvs.size() >= bVarsThm.size()){
     for(size_t i=0; i<bVarsThm.size(); i++)	{
       if (bvs.find(bVarsThm[i]) == bvs.end()){
	 return false;
       }
     }
     return true;
  }
  else {
    return false;
  }
}

bool isGoodMultiTrigger(const Expr& e, const std::vector<Expr>& bVarsThm, int offset){
  if( !usefulInMatch(e) )
    return false;
  
  int bvar_missing = 0;
  const std::set<Expr>& bvs = getBoundVars(e);

  if(bvs.size() <= 0) return false;

  for(size_t i=0; i<bVarsThm.size(); i++)	{
    if (bvs.find(bVarsThm[i]) == bvs.end()){
      bvar_missing++; // found one bound var missing in the e.
    }
  }

  if (0 == bvar_missing){ //it is a full triggers
    return false; 
  }
  
  if(bvar_missing <= offset){
    if(isSysPred(e)){
      if (isGoodSysPredTrigger(e)) {
	return true;
      }
      else {
	return false;
      }
    }
    else {
      return true;
    }
  }
  return false;
}

bool isGoodPartTrigger(const Expr& e, const std::vector<Expr>& bVarsThm){
  if( !usefulInMatch(e) )
    return false;
  
  size_t bvar_missing = 0;
  const std::set<Expr>& bvs = getBoundVars(e);
  
  for(size_t i=0; i<bVarsThm.size(); i++)	{
    if (bvs.find(bVarsThm[i]) == bvs.end()){
      bvar_missing++; // found one bound var missing in the e.
    }
  }

  if (0 == bvar_missing){ //it is a full triggers
    return false; 
  }
  
  if(0 == bvs.size()){
    return false;
  } 
  
  if(bvar_missing < bVarsThm.size()){
    if(isSysPred(e)){
      if (isGoodSysPredTrigger(e)) {
	return true;
      }
      else {
	return false;
      }
    }
    else {
      return true;
    }
  }
  return false;
}


static bool recursiveGetPartTriggers(const Expr& e, std::vector<Expr>& res) {
  if(e.getFlag())
   return false;

  if(e.isClosure())
    return recursiveGetPartTriggers(e.getBody(), res); 
  
  if(0 == e.arity()){
    if(BOUND_VAR == e.getKind()){
      return false;
    }
    else{
      return true;
    }
  }

  bool good=true;
  bool no_bound =true;
  
  for(Expr::iterator i=e.begin(), iend=e.end(); i!=iend; ++i) {	
    if(BOUND_VAR == i->getKind()){
      no_bound=false;
      continue;
    }
    bool temp = recursiveGetPartTriggers(*i,res);
    if(false == temp) {
      good=false;
    }
  }
  
  e.setFlag();
  
  if(good && no_bound) {
    return true;
  }
  else if(good && !no_bound){
    res.push_back(e);
    return false;
  }
  else{
    return false;
  }
}


std::vector<Expr> getPartTriggers(const Expr& e){
  e.clearFlags();
  std::vector<Expr> res;
  recursiveGetPartTriggers(e,res);
  e.clearFlags();
  return res;
}

int trigInitScore(const Expr& e){
  if( isSysPred(e) && !isGoodSysPredTrigger(e)){
    return 1;
  }
  else {
    return 0;
  }
} 

void findPolarity(const Expr& e, ExprMap<Polarity>& res, Polarity  pol){
  if(!e.getType().isBool()) return;
  //now a AND b will be given a polarity too, this is not necessary.
  if(res.count(e)>0){
    if ((Neg == res[e] && Pos == pol) || (Neg == res[e] && Pos == pol) ){
      res[e]=PosNeg;
    }
  }
  else{
    res[e]=pol;
  }
  
  if(PosNeg==pol){
    for(int i=0; i<e.arity(); i++){
      findPolarity(e[i], res, pol);
    }
  }
  else{
    Polarity neg_pol=Ukn;
    if(Pos == pol) {
      neg_pol = Neg;
    }
    else if(Neg == pol){
      neg_pol = Pos;
    }

    if(e.isImpl()){
      findPolarity(e[0], res, neg_pol);
      findPolarity(e[1], res, pol);
    }
    else if(e.isAnd() || e.isOr()){
      for(int i=0; i<e.arity(); i++){
	findPolarity(e[i], res, pol);
      }
    }
    else if(e.isNot()){
      findPolarity(e[0], res, neg_pol);
    }
    else if(e.isITE()){
      findPolarity(e[0], res, PosNeg);
      findPolarity(e[1], res, pol);
      findPolarity(e[2], res, pol);
    }
    else if(e.isClosure()){
      findPolarity(e.getBody(), res, pol);
    }
    else if(e.isIff()){
      findPolarity(e[0], res, PosNeg);
      findPolarity(e[1], res, PosNeg);
    }
    else if(e.isXor()){
      findPolarity(e[0], res, neg_pol);
      findPolarity(e[1], res, neg_pol);
    }
    else if(e.isAtomicFormula()){
      return;
    }
    else{
      DebugAssert(false, "Error in find polarity in "+e.toString());
    }
  }
}

void TheoryQuant::arrayIndexName(const Expr& e){
  std::vector<Expr> res;

  const std::vector<Expr>& subs=getSubTerms(e);
  
  for(size_t i=0; i<subs.size(); i++){
    int kind = subs[i].getKind();
    if (READ == kind || WRITE == kind){
      const Expr& name = subs[i][0];
      const Expr& index = subs[i][1];
      if(getBoundVars(name).size() <= 0 && (getBoundVars(index).size() <=0)){
	std::vector<Expr> tp = d_arrayIndic[name];
	tp.push_back(index);
	d_arrayIndic[name]=tp;
      }
      else {
      }
    }
  }
}

void TheoryQuant::registerTrig(ExprMap<ExprMap<std::vector<dynTrig>* >* >& cur_trig_map,
			       Trigger trig, 
			       const std::vector<Expr> thmBVs, 
			       size_t univ_id){
  {
    if(trig.hasRWOp){
      ExprMap<Expr> bv_map;
      dynTrig newDynTrig(trig, bv_map,univ_id);
      d_arrayTrigs.push_back(newDynTrig);
    }
  }

  ExprMap<Expr> bv_map;
  for(size_t i = 0; i<thmBVs.size(); i++){
    bv_map[thmBVs[i]] = null_expr;
  }
  const Expr& trig_ex = trig.getEx();

  Expr genTrig = generalTrig(trig_ex, bv_map);

  dynTrig newDynTrig(trig,bv_map,univ_id);

  Expr head = trig.getHead();

  ExprMap<ExprMap<vector<dynTrig>* >* >::iterator iter = cur_trig_map.find(head);
  if(cur_trig_map.end() == iter){
    ExprMap<vector<dynTrig>* >* new_cd_map= new  ExprMap<vector<dynTrig>* > ;
    cur_trig_map[head] = new_cd_map;
    vector<dynTrig>* new_dyntrig_list = new vector<dynTrig>;
    (*new_cd_map)[genTrig] = new_dyntrig_list;
    (*new_dyntrig_list).push_back(newDynTrig);
  }
  else{
    ExprMap<vector<dynTrig>* >* cd_map = iter->second;
    ExprMap<vector<dynTrig>* >::iterator iter_map = cd_map->find(genTrig);
    if(cd_map->end() == iter_map){
      vector<dynTrig>* new_dyntrig_list = new vector<dynTrig>; 
      (*cd_map)[genTrig] = new_dyntrig_list;
      (*new_dyntrig_list).push_back(newDynTrig);
    }
    else{
      //      (*((*cd_map)[generalTrig])).push_back(newDynTrig);
      (*(iter_map->second)).push_back(newDynTrig);
    }
  }
}

/*
void TheoryQuant::registerTrigReal(Trigger trig, const std::vector<Expr> thmBVs, size_t univ_id){
  cout<<"register: "<<trig.getEx()<<endl;
  ExprMap<Expr> bv_map;
  for(size_t i = 0; i<thmBVs.size(); i++){
    bv_map[thmBVs[i]] = null_expr;
  }
  const Expr& trig_ex = trig.getEx();

  Expr genTrig = generalTrig(trig_ex, bv_map);

  dynTrig newDynTrig(trig,bv_map,univ_id);

  Expr head = trig.getHead();
  
  ExprMap<CDMap<Expr, CDList<dynTrig>* >* >::iterator iter = d_allmap_trigs.find(head);
  if(d_allmap_trigs.end() == iter){
    CDMap<Expr, CDList<dynTrig>* >* new_cd_map= 
      new(true) CDMap<Expr, CDList<dynTrig>* > (theoryCore()->getCM()->getCurrentContext());
    d_allmap_trigs[head] = new_cd_map;
    CDList<dynTrig>* new_dyntrig_list = new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
    (*new_cd_map)[genTrig] = new_dyntrig_list;
    (*new_dyntrig_list).push_back(newDynTrig);
  }
  else{
    CDMap<Expr, CDList<dynTrig>* >* cd_map = iter->second;
    CDMap<Expr, CDList<dynTrig>* >::iterator iter_map = cd_map->find(genTrig);
    if(cd_map->end() == iter_map){
      CDList<dynTrig>* new_dyntrig_list = new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
      (*cd_map)[genTrig] = new_dyntrig_list;
      (*new_dyntrig_list).push_back(newDynTrig);
    }
    else{
      //      (*((*cd_map)[generalTrig])).push_back(newDynTrig);
      (*((*iter_map).second)).push_back(newDynTrig);
      cout<<"once more"<<endl;
    }
  }
  
}
*/
Expr TheoryQuant::generalTrig(const Expr& trig, ExprMap<Expr>& bvs){
  size_t count =1 ;
  Expr res = recGeneralTrig(trig, bvs, count);
  getBoundVars(res);
  return res;
}

Expr TheoryQuant::recGeneralTrig(const Expr& trig, ExprMap<Expr>& bvs, size_t& mybvs_count){
  
  if (!trig.containsBoundVar()) return trig;
  if (BOUND_VAR == trig.getKind()){
    if (bvs.find(trig) != bvs.end()){
      const Expr& ubv = bvs[trig];
      if(null_expr ==ubv){
	Expr new_bv = d_mybvs[mybvs_count++];
	bvs[trig] = new_bv ;
	if((mybvs_count) >= MAX_TRIG_BVS ){
	  throw "general trig error";
	}
	else{
	  return new_bv;
	}
      }
      else{
	return bvs[trig];
      }
    }
    else{
      return d_mybvs[0];
    }
  }
  else{
    vector<Expr> children;      
      for(Expr::iterator i=trig.begin(), iend=trig.end(); i!=iend; ++i){	
	Expr repChild;
	if(i->containsBoundVar()){
	  repChild = recGeneralTrig(*i, bvs, mybvs_count);
	}
	else{
	  repChild = *i;
	}
	children.push_back(repChild);
      }
      return Expr(trig.getOp(), children);
  }
}


//this function is used to check if two triggers can match with eath other
bool TheoryQuant::canMatch(const Expr& t1, const Expr& t2, ExprMap<Expr>& env){
  if(getBaseType(t1) != getBaseType(t2)) return false;

  if (BOUND_VAR == t1.getKind() || BOUND_VAR == t2.getKind()) {
    return true;
  }

  if ( (t1.arity() != t2.arity()) || (t1.getKind() != t2.getKind() )) {
    return false;
  }
  if (canGetHead(t1) && canGetHead(t2)) {
    if ( getHead(t1) != getHead(t2) ){
      return false;
    }
    for(int i=0; i<t1.arity(); i++){
      if (false == canMatch(t1[i], t2[i] , env))
	return false;
    }
    return true;
  }
  else{
    return false;
  }
}

bool TheoryQuant::isTransLike (const vector<Expr>& cur_trig){
  if(!(*d_useTrans)){
    return false;
  }
  if(3==cur_trig.size()){
    const Expr& t1=cur_trig[0];
    const Expr& t2=cur_trig[1];
    const Expr& t3=cur_trig[2];
    if ( canGetHead(t1) && canGetHead(t2) && canGetHead(t3) && 
	 (getHead(t1) == getHead(t2)) &&  (getHead(t2) == getHead(t3))){
      const std::set<Expr>& ts1 = getBoundVars(t1); 
      const std::set<Expr>& ts2 = getBoundVars(t2); 
      const std::set<Expr>& ts3 = getBoundVars(t3);
      if ( 2==ts1.size() && 2==ts2.size() && 2==ts2.size() && 
	   (ts1 != ts2) && (ts2 != ts3) && (ts3 != ts1)){
	std::set<Expr> all;
	for(set<Expr>::const_iterator i=ts1.begin(), iend = ts1.end(); i != iend; i++){
	  all.insert(*i);
	}
	for(set<Expr>::const_iterator i=ts2.begin(), iend = ts2.end(); i != iend; i++){
	  all.insert(*i);
	}
	for(set<Expr>::const_iterator i=ts3.begin(), iend = ts3.end(); i != iend; i++){
	  all.insert(*i);
	}
	bool res = true;
	if(3==all.size()){
	  for(set<Expr>::const_iterator i=all.begin(), iend = all.end(); i != iend; i++){
	    if(!i->isVar()) {
	      res = false;
	      break;
	    }
	  }
	  if(res) {
	  }
	  return res;
	}
      } 
    }  
  }
  return false; 
}

bool TheoryQuant::isTrans2Like (const std::vector<Expr>& all_terms, const Expr& tr2){
  if(!(*d_useTrans2)){
    return false;
  }
  for(size_t i = 0; i < all_terms.size(); i++){
    if(all_terms[i].isEq()){
      const Expr& cur = all_terms[i];
      if(cur[0] != cur[1] && ( (cur[0]==tr2[0] && cur[1]==tr2[1]) || (cur[0]==tr2[1] && cur[1]==tr2[0]))){
	return true;
      } 
    }
  }
  return false; 
}


bool goodMultiTriggers(const std::vector<Expr>& exprs, const std::vector<Expr> bVars){
  ExprMap<bool> bvar_found;
  
  for( std::vector<Expr>::const_iterator i = bVars.begin(),  iend= bVars.end();  i!=iend; i++) {
    bvar_found[*i]=false;
  }

  for (size_t  i=0; i< exprs.size();i++){
    const std::set<Expr> & bv_in_trig = getBoundVars(exprs[i]);
    for(std::set<Expr>::const_iterator j=bv_in_trig.begin(), jend = bv_in_trig.end();  j != jend; j++){
      if(bvar_found.find(*j) != bvar_found.end()){
	bvar_found[*j]=true;
      }
    }
  }
  
  for( std::vector<Expr>::const_iterator i = bVars.begin(), iend= bVars.end();  i!=iend;  i++) {
    if(false == bvar_found[*i]){
      return false ;
    }
  }
  return true;
}


inline size_t locVar(const vector<Expr>& bvsThm, const Expr& bv){
  for(size_t i=0, iend = bvsThm.size(); i < iend; i++){
    if (bvsThm[i] == bv){
      return i;
    }
  }
  return 999; //this number should be big enough
} 

void TheoryQuant::setupTriggers(const Theorem& thm, size_t univs_id){
}

void TheoryQuant::setupTriggers(ExprMap<ExprMap<vector<dynTrig>* >*>& trig_maps,
				const Theorem& thm, 
				size_t univs_id){
  const Expr& e = thm.getExpr();
  TRACE("triggers","setup : ",e.toString()," || ");
  //  cout<<"set up "<<e<<endl;
  d_univs.push_back(thm);
  const std::vector<Expr>& bVarsThm = e.getVars(); 
  if  (d_hasTriggers.count(e) > 0) {
    std::vector<Trigger>& new_trigs = d_fullTrigs[e];
    for(size_t i=0; i<new_trigs.size(); i++){
      registerTrig(trig_maps, new_trigs[i], bVarsThm, univs_id);
    }
    if(0 == new_trigs.size()){
      std::vector<Trigger>& new_mult_trigs = d_multTrigs[e];
      for(size_t j=0; j<new_mult_trigs.size(); j++){
	registerTrig(trig_maps, new_mult_trigs[j], bVarsThm, univs_id);
      }
    } 
    return;
  }

  d_hasTriggers[e]=true;

  const std::vector<Expr>& subterms = getSubTrig(e);

#ifdef DEBUG
  if( CVC3::debugger.trace("triggers")  ){
    cout<<"===========all sub terms =========="<<endl;
    for (size_t i=0; i<subterms.size(); i++){
      const Expr& sub = subterms[i];
      cout<<"i="<< i << " : " << findExpr(sub) << " | " << sub << " and type is " << sub.getType() 
	  << " and kind is " << sub.getEM()->getKindName(sub.getKind()) << endl;
    }
  }
#endif

  ExprMap<Polarity> exprPol;
  findPolarity(e, exprPol, Pos);

  {
    std::vector<Expr> trig_cadt;
    for(std::vector<Expr>::const_iterator i = subterms.begin(),iend=subterms.end(); i!=iend; i++){
      if(isGoodFullTrigger(*i, bVarsThm)) {
	trig_cadt.push_back(*i);
      }
    }

    std::vector<Expr> trig_list;
    std::vector<Expr> trig_extra;

    for(size_t iter =0; iter < trig_cadt.size(); iter++) {
      Expr* i = &(trig_cadt[iter]);
      bool notfound = true;
      
      for(size_t index=0; index< trig_list.size(); index++){ 
	if (i->subExprOf(trig_list[index])) {
	  trig_list[index]=*i;
	  notfound=false;
	  break;
	}
	if (trig_list[index].subExprOf(*i)) {
	  notfound=false;
	  break;
	}
      }
      if (notfound) {
	trig_list.push_back(*i);
      }
    }
    
    std::vector<Trigger> trig_ex;
    
    for (size_t  i=0; i< trig_list.size();i++){
      const Expr& cur = trig_list[i];
      const std::set<Expr> cur_bvs = getBoundVars(cur);
      int score = trigInitScore(cur);
      if(score > 0) continue;

      //1. test trans2 
      //2. test whether a trigger can trig a bigger instance of itself, now we have no actions for such case because we use expr score and dynamic loop prevention. 
      
      for(size_t j=0; j< trig_cadt.size(); j++){
	if (trig_list[i] == trig_cadt[j]) continue;
	ExprMap<Expr> null;
	if (canMatch(trig_list[i], trig_cadt[j], null)){
	  if(exprScore(trig_list[i]) < exprScore(trig_cadt[j])){
	  } 
	  else if(*d_useTrans2 &&
		  trig_list.size() == 2 &&
		  trig_list[i].arity() == 2 && 
		  BOUND_VAR == trig_list[i][0].getKind() && 
		  BOUND_VAR == trig_list[i][1].getKind() && 
		  BOUND_VAR == trig_cadt[j][0].getKind() && 
		  BOUND_VAR == trig_cadt[j][1].getKind() && 
		  isTrans2Like(subterms, trig_list[i])
		  ){
	    
	    score =0; //useless, to delete;
	    d_trans2_num++;
	    
	    DebugAssert(d_trans2_num<=1, "more than 2 trans2 found");
	    TRACE("triggers",  "trans2 found ", trig_list[i], "");
	    
	    Trigger t(theoryCore(), cur, Neg, cur_bvs);
	    t.setTrans2(true);
	    t.setHead(getHeadExpr(cur));
	    if(isSimpleTrig(cur)){
	      t.setSimp();
	    }
	    if(isSuperSimpleTrig(cur)){
	      t.setSuperSimp();
	    }
	    d_fullTrigs[e].push_back(t);
	    registerTrig(trig_maps,t, bVarsThm, univs_id);
	    return;
	  }
	  else{
	    score =0;
	  }
	}
      }
      
      Polarity pol= Ukn;
      
      if(cur.getType().isBool()){
	DebugAssert(exprPol.count(e)>0,"unknown polarity:"+cur.toString());
	pol = exprPol[cur];
      }
      
      Trigger* t;
      Trigger* t_ex; //so, if a pred is PosNeg, we actually put two triggers into the list, one pos and the other neg
      
      if(PosNeg == pol && *d_usePolarity){
	t = new Trigger(theoryCore(), cur, Pos, cur_bvs);
	t_ex = new Trigger(theoryCore(), cur, Neg, cur_bvs);
	if(isSimpleTrig(cur)){
	  t->setSimp();
	  t_ex->setSimp();
	}
	if(isSuperSimpleTrig(cur)){
	  t->setSuperSimp();
	  t_ex->setSuperSimp();
	}

      }
      else{
	t = new Trigger(theoryCore(), cur, pol, cur_bvs);
	if(isSimpleTrig(cur)){
	  t->setSimp();
	}
	if(isSuperSimpleTrig(cur)){
	  t->setSuperSimp();
	}
	t_ex = NULL;
      }
      
      if(canGetHead(cur)) {
	t->setHead(getHeadExpr(cur));
	if(NULL != t_ex){
	  t_ex->setHead(getHeadExpr(cur));
	}
      }
      else{
	if(!isSysPred(cur)){
	  //	  cout<<"cur " << cur <<endl;
	  DebugAssert(false, "why this is a trigger");
	}
      } 
     
      t->setRWOp(false);
      
      if(READ == cur.getKind() || WRITE == cur.getKind()){
	arrayIndexName(cur);
      }

      if(READ == cur.getKind() && WRITE== cur[0].getKind() && 1 == bVarsThm.size() ){
	//	cout<<t->trig<<endl;
	t->setRWOp(true);
	if(t_ex != NULL) t_ex->setRWOp(true);
      }
      
      if(t_ex != NULL)  {
	trig_ex.push_back(*t_ex);
      }
      
      d_fullTrigs[e].push_back(*t);
      registerTrig(trig_maps,*t, bVarsThm, univs_id);

      TRACE("triggers", "new:full triggers:", cur.toString(),"");
      TRACE("triggers", "new:full trigger score:", score,"");
      TRACE("triggers", "new:full trigger pol:", pol,"");
    }
    
    for(size_t i=0; i<trig_ex.size(); i++){
      d_fullTrigs[e].push_back(trig_ex[i]);
      registerTrig(trig_maps,trig_ex[i], bVarsThm, univs_id);
      TRACE("triggers", "new extra :full triggers:", trig_ex[i].getEx().toString(),"");
    }
    
    if(d_fullTrigs[e].size() == 0){
      TRACE("triggers warning", "no full trig: ", e , ""); 
    }
  }
  
  if(0 == d_fullTrigs[e].size() )
    {  //setup multriggers
      for( std::vector<Expr>::const_iterator i = subterms.begin(),  iend=subterms.end();  i!=iend;  i++) {
	if(isGoodMultiTrigger(*i, bVarsThm, d_offset_multi_trig))  {
	  bool notfound = true;
	  for(size_t index=0; index<d_multTriggers[e].size(); index++){ 
	    if (i->subExprOf(d_multTriggers[e][index]))    {
	      (d_multTriggers[e][index])=*i; 
	      notfound=false;
	    }
	  }
	  if (notfound){		    
	    d_multTriggers[e].push_back(*i);
	  }
	}
      }
      
      std::vector<Expr>& cur_trig = d_multTriggers[e];
      
      if (goodMultiTriggers(cur_trig, bVarsThm)){
	//	cout<<"good multi triggers"<<endl;
	TRACE("multi-triggers", "good set of multi triggers","","");
	for (size_t  i=0; i< d_multTriggers[e].size();i++){
	  //	  cout<<"multi-triggers" <<d_multTriggers[e][i]<<endl;
	  TRACE("multi-triggers", "multi-triggers:", d_multTriggers[e][i].toString(),"");
	}
      }
      else{
	cur_trig.clear();
	//	cout<<"bad multi triggers"<<endl;	
	TRACE("multi-triggers", "bad set of multi triggers","","");
      }
      
      //special code for transitive pred,
      {
	if(isTransLike(cur_trig)){
	  d_trans_num++;
	  DebugAssert(d_trans_num <= 1, "more than one trans found");
	  
	  Expr ex = cur_trig[0];

	  Trigger* trans_trig = new Trigger(theoryCore(), ex, Neg, getBoundVars(ex));
	  trans_trig->setHead(getHeadExpr(ex));
	  if(isSimpleTrig(ex)){
	    trans_trig->setSimp();
	  }
	  if(isSuperSimpleTrig(ex)){
	    trans_trig->setSuperSimp();
	  }

	  trans_trig->setTrans(true);
	  
	  d_fullTrigs[e].push_back(*trans_trig);
	  registerTrig(trig_maps,*trans_trig, bVarsThm, univs_id);
	  cur_trig.clear();
	}
      }
      
      //enhanced multi-triggers 
      if(cur_trig.size() >0 ){
	//  if(cur_trig.size() >0 ){
	std::vector<Expr> posList, negList;
	for(size_t k=0; k<cur_trig.size(); k++){
	  const Expr& cur_item = cur_trig[k];
	  if (cur_item.getType().isBool()){
	    Polarity pol = exprPol[cur_item];
	    if(PosNeg == pol || Pos == pol){
	      posList.push_back(cur_item);
	    }
	    if(PosNeg == pol || Neg == pol){
	      negList.push_back(cur_item);
	    }
	  }
	}
	if (goodMultiTriggers(posList, bVarsThm)){
	  TRACE("multi-triggers", "good set of multi triggers pos","","");
	  for (size_t  i=0; i< posList.size();i++){
	    TRACE("multi-triggers", "multi-triggers:", posList[i].toString(),"");
	  }
	  cur_trig.clear();
	  for(size_t m=0; m<posList.size(); m++){
	    cur_trig.push_back(posList[m]);
	  }
	}
	if (goodMultiTriggers(negList, bVarsThm) && negList.size() < cur_trig.size()){
	  TRACE("multi-triggers", "good set of multi triggers neg","","");
	  for (size_t  i=0; i< negList.size();i++){
	    TRACE("multi-triggers", "multi-triggers:", negList[i].toString(),"");
	  }
	  cur_trig.clear();
	  for(size_t m=0; m<negList.size(); m++){
	    cur_trig.push_back(negList[m]);
	  }
	}
	//	cout<<"neg list and pos list"<<negList.size()<<" | " <<posList.size()<<endl;
      }
      
      {//new way of multi trigger

	
	if( 3 == cur_trig.size() ||  4 == cur_trig.size() || 5 == cur_trig.size() || 6 == cur_trig.size()  ){
	  for(size_t i = 0; i < cur_trig.size(); i++){
	    for(size_t j = 0; j < i; j++){
	      vector<Expr> tempList;
	      tempList.clear();
	      tempList.push_back(cur_trig[i]);
	      tempList.push_back(cur_trig[j]);
	      //	      cout<<i<<" | "<<j<<endl;
	      //	      cout<<vectorExpr2string(tempList)<<endl;
	      if (goodMultiTriggers(tempList, bVarsThm)){
		cur_trig.clear();
		cur_trig.push_back(tempList[0]);
		cur_trig.push_back(tempList[1]);
		break;
	      }
	    }
	  }
	} 
	
	if(cur_trig.size() != 2){
	  if( 0 == cur_trig.size()){
	    return;
	  }
	  //	  FatalAssert(false, "unsupported multi-triggers");
	  //  	  cout<<"e: "<<e<<endl;
	  //  	  cout<<cur_trig.size()<<endl;
	  //  	  cout<<bVarsThm.size()<<endl;
	  //
	  //	  cout<<vectorExpr2string(bVarsThm)<<endl;
	  // 	  for(size_t i =0; i<cur_trig.size(); i++){
	  // 	    cout<<cur_trig[i]<<endl;
	  // 	  } 
	  return;
	}
	
	for(size_t i = 0 ; i<cur_trig.size(); i++){
	  set<Expr> bvs = getBoundVars(cur_trig[i]);
	  Trigger trig(theoryCore(), cur_trig[i], Ukn, bvs); // 
	  trig.setHead(getHead(cur_trig[i]));
	  trig.setMultiTrig();
	  trig.multiIndex = i;
	  trig.multiId=d_all_multTrigsInfo.size();
	  d_multTrigs[e].push_back(trig);
	  registerTrig(trig_maps, trig, bVarsThm, univs_id);
	}
	
	{
	  multTrigsInfo multTrigs;
	  for(size_t i =0, iend = d_multTrigs[e].size(); i<iend; i++){
	    const std::vector<Expr>& one_set_bvs = d_multTrigs[e][i].bvs;
	    std::vector<size_t> one_set_pos;
	    
	    for(size_t v = 0, vend = one_set_bvs.size(); v<vend; v++){
	      size_t loc = locVar(bVarsThm, one_set_bvs[v]); 
	      if( 999 != loc ){
		one_set_pos.push_back(loc);
	      }
	    }
	    
	    sort(one_set_pos.begin(), one_set_pos.end());

	    for(size_t v = 0, vend = one_set_pos.size(); v<vend; v++){
	    }

	    multTrigs.var_pos.push_back(one_set_pos);
	  }//setup pos of all multi tirggers
	  
	  //now we only consider two multi triggers
	  vector<size_t> common;
	  std::vector<size_t>& tar1 = multTrigs.var_pos[0];
	  std::vector<size_t>& tar2 = multTrigs.var_pos[1];
	  vector<size_t>::iterator t1(tar1.begin()), t2(tar2.begin());
	  while(t1 != tar1.end() && t2!= tar2.end()){
	    size_t pos1 = *t1;
	    size_t pos2 = *t2;
	    if( pos1  == pos2 ) {
	      common.push_back(pos1);
	      t1=tar1.erase(t1); 
	      t2=tar2.erase(t2);
	    }
	    else if( pos1 > pos2 ){
	      t2++;
	    }
	    else {
	      t1++;
	    }
	  }
	  multTrigs.common_pos.push_back(common);
	  
	  size_t multi_size = d_multTrigs[e].size(); //should be 2
	  for(size_t i =0; i< multi_size; i++){
	    multTrigs.var_binds_found.push_back(new (true) CDMap<Expr, bool> (theoryCore()->getCM()->getCurrentContext()));
	  }
	  multTrigs.uncomm_list.push_back(new ExprMap<CDList<Expr>* >);
	  multTrigs.uncomm_list.push_back(new ExprMap<CDList<Expr>* >);
	  d_multitrigs_maps[e]=multTrigs;
	  d_all_multTrigsInfo.push_back(multTrigs);
	}
      }
    }
  
  //setup partial triggers
  if(*d_usePart)
    {
    std::vector<Trigger> trig_ex;
    
    trig_ex.clear();
    for( std::vector<Expr>::const_iterator i = subterms.begin(),  iend=subterms.end();  i!=iend;  i++) {
      if(isGoodPartTrigger(*i, bVarsThm))  {
	bool notfound = true;
	for(size_t index=0; index<d_partTriggers[e].size(); index++){ 
	  if (i->subExprOf(d_partTriggers[e][index]))    {
	    (d_partTriggers[e][index])=*i; 
	    notfound=false;
	  }
	}
	if (notfound)		    
	  d_partTriggers[e].push_back(*i); 
      }
    }
    
    for (size_t  i=0; i< d_partTriggers[e].size();i++){
      TRACE("triggers", "partial triggers:", d_partTriggers[e][i].toString(),"");
    }
    
    for (size_t  i=0; i< d_partTriggers[e].size();i++){
      Polarity pol= Ukn;
      const Expr& cur = d_partTriggers[e][i]; 
      const std::set<Expr> cur_bvs = getBoundVars(cur); 
      if(cur.getType().isBool()){
	DebugAssert(exprPol.count(e)>0,"unknown polarity:"+cur.toString());
	pol = exprPol[cur];
      }
      
      Trigger* t;
      Trigger* t_ex; //so, if a pred is PosNeg, we actually put two triggers into the list, one pos and the other neg
      
      if(PosNeg == pol && *d_usePolarity){
	t = new Trigger(theoryCore(), cur, Pos, cur_bvs);
	t_ex = new Trigger(theoryCore(), cur, Neg, cur_bvs);
      }
      else{
	t = new Trigger(theoryCore(), cur, pol, cur_bvs);
	t_ex = NULL;
      }
      
      if(canGetHead(cur)) {
	t->setHead(getHeadExpr(cur));
      }
      
      if(t_ex != NULL)  trig_ex.push_back(*t_ex);
      
      d_partTrigs[e].push_back(*t);
      
      TRACE("triggers", "new:part trigger pol:", pol,cur.toString());
    }
    
    for(size_t i=0; i<trig_ex.size(); i++){
      d_partTrigs[e].push_back(trig_ex[i]);
      TRACE("triggers", "new extra :part triggers:", trig_ex[i].getEx().toString(),"");
    }
  }  
}



//! test if a sub-term contains more bounded vars than quantified by out-most quantifier.
int hasMoreBVs(const Expr& thm){
  DebugAssert(thm.isForall(), "hasMoreBVS called by non-forall exprs");
  
  const std::vector<Expr>& bvsOutmost = thm.getVars();
  const std::set<Expr>& bvs = getBoundVars(thm); 

  return int(bvs.size()-bvsOutmost.size()); 

}

/*! \brief Theory interface function to assert quantified formulas
 *
 * pushes in negations and converts to either universally or existentially 
 * quantified theorems. Universals are stored in a database while 
 * existentials are enqueued to be handled by the search engine.
 */
void TheoryQuant::assertFact(const Theorem& thm){

  if(*d_translate) return;
  TRACE("quant assertfact", "assertFact => ", thm.toString(), "{");
  Theorem rule, result;
  const Expr& expr = thm.getExpr();
  // Ignore existentials

  if(expr.isExists()) {
    TRACE("quant assertfact", "assertFact => (ignoring existential) }", expr.toString(), "");
    return;
  }

  DebugAssert(expr.isForall() || (expr.isNot() && (expr[0].isExists() || expr[0].isForall())),
	      "Theory of quantifiers cannot handle expression "
	      + expr.toString());

  if(expr.isNot()) {//find the right rule to eliminate negation
    if(expr[0].isForall()) {
      rule = d_rules->rewriteNotForall(expr);
    }
    else if(expr[0].isExists()) {
      rule = d_rules->rewriteNotExists(expr);
    }
    result = iffMP(thm, rule);
  }
  else{
    result = thm;
  }

  result = d_rules->boundVarElim(result); //eliminate useless bound variables
  
  if(result.getExpr().isForall()){

    if(*d_useNew){

      if(result.getExpr().getBody().isForall()){ // if it is of the form forall x. forall. y
	result=d_rules->packVar(result);
      }
      result = d_rules->boundVarElim(result); //eliminate useless bound variables

      int nBVs = hasMoreBVs(result.getExpr());
      if( nBVs >= 1){
	d_hasMoreBVs[result.getExpr()]=true;
      }
      d_rawUnivs.push_back(result);
      return;
      /* -------------------------------------- */
      //      int nBVs = hasMoreBVs(result.getExpr());

      if(0 == nBVs){//good 
	TRACE("quant assertfact", "assertFact => forall enqueueing: ", result.toString(), "}");
      	d_univs.push_back(result);
	setupTriggers(result, d_univs.size()-1);
      }
      else if(1== nBVs){
	d_hasMoreBVs[result.getExpr()]=true;
	const Expr& body = result.getExpr().getBody();

	if(*d_usePullVar){
	  if((body.isAnd() && body[1].isForall()) || (body.isImpl() && body[1].isForall()) ){
	    result=d_rules->pullVarOut(result);

	    TRACE("quant assertfact", "assertFact => pull-var enqueueing: ", result.toString(), "}");

	    d_univs.push_back(result);
	    setupTriggers(result,  d_univs.size()-1);
	  }
	}
	else{
	  TRACE("quant assertfact", "debug:not recognized case", result.toString(), thm.toString());

	  d_univs.push_back(result);
	  setupTriggers(result,  d_univs.size()-1);
	  return;
	}
      }
      else{
	d_hasMoreBVs[result.getExpr()]=true;
	d_univs.push_back(result);
	setupTriggers(result,  d_univs.size()-1);
	return;
      }
    }
    else{

      TRACE("quant assertfact", "assertFact => old-fashoin enqueueing: ", result.toString(), "}");
      //      cout<<"error"<<endl;
      d_univs.push_back(result);
    }
  }
  else { //quantifier got eliminated or is an existantial formula 

    TRACE("quant assertfact", "assertFact => non-forall enqueueing: ", result.toString(), "}");
    enqueueFact(result);
  }
}

void TheoryQuant::recGoodSemMatch(const Expr& e,
				  const std::vector<Expr>& bVars,
				  std::vector<Expr>& newInst,
				  std::set<std::vector<Expr> >& instSet)
{
  size_t curPos = newInst.size();
  if (bVars.size() == curPos)    {
    Expr simpleExpr = simplifyExpr(e.substExpr(bVars,newInst));
    if (simpleExpr.hasFind()){
      std::vector<Expr> temp = newInst;
      instSet.insert(temp);
      TRACE("quant yeting", "new inst found for ", e.toString()+" ==> ", simpleExpr.toString());
    };
  }
  else {
    Type t = getBaseType(bVars[curPos]);
    std::vector<Expr> tyExprs= d_typeExprMap[t];
    if (0 == tyExprs.size())  {
      return;//has some problem
    }
    else{
      for (size_t i=0;i<tyExprs.size();i++){
	newInst.push_back(tyExprs[i]);
	recGoodSemMatch(e,bVars,newInst,instSet);
	newInst.pop_back();
      }
    }
  }
}

bool isIntx(const Expr& e, const Rational& x){
  if(e.isRational() && e.getRational()==x)
    return true;
  else return false;
}

Expr getLeft(const Expr& e){
  if(e.getKind()!= PLUS) return null_expr;
  if(e.arity() != 3) return null_expr;
  Expr const_expr, minus ,pos;
  int numMinus=0, numPos=0, numConst=0;;
  for(int i=0; i<e.arity(); i++){
    if((e[i]).getKind() == MULT){
      if(isIntx(e[i][0], -1)){
	numMinus++;
	minus=e[i][1];
      }
      else{
	numPos++;
	pos=e[i];
      }
    }
    else if(e[i].isRational())      {
      const_expr = e[i];
      numConst++;
    }
    else{
      numPos++;
      pos=e[i];
    }
  }
  if(1==numPos && 1==numConst && 1==numMinus){
    return minus;
  }
  else{
    return null_expr;
  }
}

Expr getRight(const Expr& e){
  if(e.getKind()!= PLUS) return null_expr;
  if(e.arity() != 3) return null_expr;
  Expr const_expr, minus ,pos;
  int numMinus=0, numPos=0, numConst=0;;
 
  for(int i=0; i<e.arity(); i++){
    if((e[i]).getKind() == MULT){
      if(isIntx(e[i][0], -1)){
	numMinus++;
	minus=e[i][1];
      }
      else{
	numPos++;
	pos=e[i];
      }
    }
    else if(e[i].isRational())      {
      const_expr = e[i];
      numConst++;
    }
    else{
      numPos++;
      pos=e[i];
    }
  }
  
  if(1==numPos && 1==numConst && 1==numMinus){
    if(isIntx(const_expr,0)){
      return pos;
    }
    else{
      //      return null_expr;
      return Expr(PLUS, const_expr, pos);
    }
  }
  else{
    return null_expr;
  }
}
 
inline void TheoryQuant::add_parent(const Expr& parent){
  ExprMap<CDList<Expr>* >::iterator iter;
  for(int i=0; i< parent.arity(); i++){
    const Expr& child = parent[i];
    iter = d_parent_list.find(child);
    if(d_parent_list.end() == iter){
      d_parent_list[child] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
      d_parent_list[child]->push_back(parent);
    }
    else{
      iter->second->push_back(parent);
    }
  }
}

void TheoryQuant::collectChangedTerms(CDList<Expr>& changed){
  ExprMap<bool> eqs_hash;
  ExprMap<bool> changed_hash;
  /*
  {
    for(ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.begin(), iter_end=d_eq_list.end(); 
	iter != iter_end; iter++){
      CDList<Expr>* cur_eqs = iter->second;
      int begin_pos;
      Expr head = iter->first;
      if(d_eq_pos.find(head) == d_eq_pos.end()){
	begin_pos=0;
	d_eq_pos[head]= new(true) CDO<size_t>(theoryCore()->getCM()->getCurrentContext(), 0, 0);
	
      }
      else{
	begin_pos = *(d_eq_pos[head]);
      } 
      for(size_t i=begin_pos; i<cur_eqs->size(); i++){
	eqs_hash[(*cur_eqs)[i]]=true;
      }
      (d_eq_pos[head])->set(cur_eqs->size());
    }
    }*/
  for(size_t i=d_eqs_pos; i<d_eqs.size(); i++){
    eqs_hash[d_eqs[i]]=true;
  }
  d_eqs_pos.set(d_eqs.size());
  {
    for(ExprMap<bool>::iterator iter = eqs_hash.begin(), iter_end = eqs_hash.end(); iter != iter_end; iter++){
      const Expr& cur_ex = iter->first;
      ExprMap<CDList<Expr>* >::iterator iter_parent = d_parent_list.find(cur_ex);
      if(d_parent_list.end() != iter_parent){
	CDList<Expr>* cur_parents = iter_parent->second;
	for(size_t i=0; i<cur_parents->size(); i++){
	  changed_hash[(*cur_parents)[i]]=true;
	}
      }
    }
  }
  {
    for(ExprMap<bool>::iterator iter = changed_hash.begin(), iter_end = changed_hash.end(); iter != iter_end; iter++){
      changed.push_back(iter->first);
    }
  }
}

inline bool TheoryQuant::matchChild(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  if(gterm.arity() != vterm.arity()) {
    return false; 
  }
  for(int i = 0 ; i< gterm.arity(); i++){
    const Expr& cur_v = vterm[i];
    const Expr& cur_g = gterm[i];
    if(BOUND_VAR == cur_v.getKind()){
      ExprMap<Expr>::iterator p = env.find(cur_v);
      if ( p != env.end()){
	if (simplifyExpr(cur_g) != simplifyExpr(p->second)){
	  return false;
	}
      }
      else {
	env[cur_v] = simplifyExpr(cur_g);
      }
    }
    else if (!cur_v.containsBoundVar()){
      if(simplifyExpr(cur_v) != simplifyExpr(cur_g)){
	return false;
      }
    }
    else{
      if (false == recSynMatch(cur_g, cur_v, env)){
	return false;
      }
    }
  }
  return true;
}

inline void TheoryQuant::matchChild(const Expr& gterm, const Expr& vterm, vector<ExprMap<Expr> >& binds){
  ExprMap<Expr> env;
  if(gterm.arity() != vterm.arity()) {
    return; 
  }
  
  for(int i = 0 ; i< gterm.arity(); i++){
    const Expr& cur_v = vterm[i];
    const Expr& cur_g = gterm[i];
    if(BOUND_VAR == cur_v.getKind()){
      ExprMap<Expr>::iterator p = env.find(cur_v);
      if ( p != env.end()){
	if (simplifyExpr(cur_g) != simplifyExpr(p->second)){
	  return;
	}
      }
      else {
	env[cur_v] = simplifyExpr(cur_g);
      }
    }
    else if (!cur_v.containsBoundVar()){
      if(simplifyExpr(cur_v) != simplifyExpr(cur_g)){
	return ;
      }
    }
    else{
      if (false == recSynMatch(cur_g, cur_v, env)){
	return;
      }
    }
  }
  binds.push_back(env);
  return;
}



//match a gterm against all the trigs in d_allmap_trigs
void TheoryQuant::matchListOld(const CDList<Expr>& glist, size_t gbegin, size_t gend){
  for(size_t g_index = gbegin; g_index < gend; g_index++){

    const Expr& gterm = glist[g_index]; 
    if(gterm.isEq()){
      continue; // we do not match with equality
    }
    
    Expr head = getHead(gterm);  
    
    ExprMap<CDMap<Expr, CDList<dynTrig>* > *>::iterator iter = d_allmap_trigs.find(head);
    if(d_allmap_trigs.end() == iter) continue;
    CDMap<Expr, CDList<dynTrig>*>* cd_map = iter->second;
//     if(cd_map->size()>10){
//       cout<<"map size1:"<<cd_map->size()<<endl;
//       cout<<head<<endl;
//     }

    CDMap<Expr, CDList<dynTrig>*>::iterator iter_trig = (*cd_map).begin();
    CDMap<Expr, CDList<dynTrig>*>::iterator iter_trig_end = (*cd_map).end();
    
    for(;iter_trig != iter_trig_end; iter_trig++){
      CDList<dynTrig>* cur_list = (*iter_trig).second;
      if(1 == cur_list->size() || null_expr == head || gterm.getType().isBool()){
	for(size_t cur_index =0; cur_index < cur_list->size(); cur_index++){
	
	  const Trigger& cur_trig = (*cur_list)[cur_index].trig;
	  size_t univ_id = (*cur_list)[cur_index].univ_id;
	  vector<ExprMap<Expr> > binds;
	  const Expr& vterm = cur_trig.trig;
	  if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans && !cur_trig.isMulti) continue;
	  //      if  ( d_allout && cur_trig.isSimple ) continue;
	  newTopMatch(gterm, vterm, binds, cur_trig);
	  
	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      bind_vec.push_back(cur_map[bVarsThm[j]]);
	    }
	    synNewInst(univ_id, bind_vec, gterm, cur_trig);
	  }
	}
      }
      else if ( cur_list->size() > 1){
	
	const Trigger& cur_trig = (*cur_list)[0].trig;//here we have a polarity problem
	const Expr& general_vterm = (*iter_trig).first;
	vector<ExprMap<Expr> > binds;       
	if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans && !cur_trig.isMulti) continue;
	//if  ( d_allout && cur_trig.isSimple ) continue;
	newTopMatch(gterm, general_vterm, binds, cur_trig);
	
	for(size_t trig_index = 0; trig_index< cur_list->size(); trig_index++){
	  size_t univ_id = (*cur_list)[trig_index].univ_id;
	  const ExprMap<Expr>& trig_map = (*cur_list)[trig_index].binds;
	  const Trigger& ind_cur_trig = (*cur_list)[trig_index].trig;
	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      const Expr& inter=(*(trig_map.find(bVarsThm[j]))).second;
	      const Expr& inter2 = cur_map[inter];
	      bind_vec.push_back(inter2);
	    }
	    synNewInst(univ_id, bind_vec, gterm, ind_cur_trig);
	  }
	}
      }
      else{
	FatalAssert(false, "error in matchlistold");
      }
    }//end of for each trig begins with head
  }//end of each gterm
}

void TheoryQuant::delNewTrigs(ExprMap<ExprMap<std::vector<dynTrig>*>*>& new_trigs){
  //return;
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator i = new_trigs.begin();
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator iend = new_trigs.end();
  for(; i!=iend; i++){
    ExprMap<std::vector<dynTrig>*>* cur_new_cd_map = i->second;
    ExprMap<vector<dynTrig>* >::iterator j = cur_new_cd_map->begin();
    ExprMap<vector<dynTrig>* >::iterator jend = cur_new_cd_map->end();
      for(; j!=jend; j++){
	Expr general_trig = j->first;
	vector<dynTrig>* trigs = j->second;
	delete trigs;
      }
      delete cur_new_cd_map;
    }
  new_trigs.clear();
}


void TheoryQuant::combineOldNewTrigs(ExprMap<ExprMap<std::vector<dynTrig>*>*>& new_trigs){
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator i = new_trigs.begin();
  ExprMap<ExprMap<std::vector<dynTrig>*>*>::iterator iend = new_trigs.end();
  for(; i!=iend; i++){
    ExprMap<std::vector<dynTrig>*>* cur_new_cd_map = i->second;
    Expr head = i->first;
    ExprMap<CDMap<Expr, CDList<dynTrig>* >* >::iterator old_iter = d_allmap_trigs.find(head);
    if(d_allmap_trigs.end() == old_iter){
      CDMap<Expr, CDList<dynTrig>* >* old_cd_map = 
	//	new(true) CDMap<Expr, CDList<dynTrig>* > (theoryCore()->getCM()->getCurrentContext());
	new(false) CDMap<Expr, CDList<dynTrig>* > (theoryCore()->getCM()->getCurrentContext());
      d_allmap_trigs[head] = old_cd_map;
      ExprMap<vector<dynTrig>* >::iterator j = cur_new_cd_map->begin();
      ExprMap<vector<dynTrig>* >::iterator jend = cur_new_cd_map->end();
      for(; j!=jend; j++){
	Expr general_trig = j->first;
	vector<dynTrig>* trigs = j->second;
	CDList<dynTrig>* old_cd_list = 	
	  //new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	  new(false) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	(*old_cd_map)[general_trig] = old_cd_list;
	for(size_t k=0; k<trigs->size(); k++){
	  (*old_cd_list).push_back((*trigs)[k]);
	  //	  cout<<"combined 1 "<<(*trigs)[k].trig.getEx()<<endl;
	}
	//	delete trigs;
      }
      //      delete cur_new_cd_map;
    }
    else{
      CDMap<Expr, CDList<dynTrig>* >* old_cd_map = old_iter->second;
      ExprMap<std::vector<dynTrig>*>::iterator j = cur_new_cd_map->begin();
      ExprMap<std::vector<dynTrig>*>::iterator jend = cur_new_cd_map->end();
      for(; j!=jend; j++){
	Expr general_trig = j->first;
	vector<dynTrig>* trigs = j->second;
	CDMap<Expr, CDList<dynTrig>* >::iterator old_trigs_iter = old_cd_map->find(general_trig);
	CDList<dynTrig>* old_cd_list;
	if(old_cd_map->end() == old_trigs_iter){
	 old_cd_list = 
	   //new(true) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	   new(false) CDList<dynTrig> (theoryCore()->getCM()->getCurrentContext());
	 (*old_cd_map)[general_trig] = old_cd_list;
	}
	else{
	  old_cd_list = (*old_trigs_iter).second; 
	}
	for(size_t k=0; k<trigs->size(); k++){
	  (*old_cd_list).push_back((*trigs)[k]);
	  //	  cout<<"combined 2 "<<(*trigs)[k].trig.getEx()<<endl;
	}
	//	delete trigs;
      }
      //      delete cur_new_cd_map;
    }
  }
  delNewTrigs(new_trigs);
  //  new_trigs.clear();
}

//match a gterm against all the trigs in d_allmap_trigs
void TheoryQuant::matchListNew(ExprMap<ExprMap<vector<dynTrig>*>*>& new_trigs,
			       const CDList<Expr>& glist,
			       size_t gbegin,
			       size_t gend){
  for(size_t g_index = gbegin; g_index<gend; g_index++){

    const Expr& gterm = glist[g_index]; 
  
    if(gterm.isEq()){
      continue; // we do not match with equality
    }
    
    Expr head = getHead(gterm);  
    
    ExprMap<ExprMap<vector<dynTrig>* > *>::iterator iter = new_trigs.find(head);
    if(new_trigs.end() == iter) continue;
    ExprMap<vector<dynTrig>*>* cd_map = iter->second;
//     if(cd_map->size()>10){
//       cout<<"map size2:"<<cd_map->size()<<endl;
//       cout<<head<<endl;
//     }

    ExprMap<vector<dynTrig>*>::iterator iter_trig = (*cd_map).begin();
    ExprMap<vector<dynTrig>*>::iterator iter_trig_end = (*cd_map).end();
    
    for(;iter_trig != iter_trig_end; iter_trig++){
      
      vector<dynTrig>* cur_list = (*iter_trig).second;
      if(1 == cur_list->size() || null_expr == head ||  gterm.getType().isBool()){
	for(size_t cur_index =0; cur_index < cur_list->size(); cur_index++){
	  const Trigger& cur_trig = (*cur_list)[cur_index].trig;
	  
	  //	if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans) continue;
	  
	  size_t univ_id = (*cur_list)[cur_index].univ_id;
	  vector<ExprMap<Expr> > binds;
	  const Expr& vterm = cur_trig.trig;
	  
	  newTopMatch(gterm, vterm, binds, cur_trig);
	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      bind_vec.push_back(cur_map[bVarsThm[j]]);
	    }
	    synNewInst(univ_id, bind_vec, gterm, cur_trig);
	  }
	}
      }
      else if ( cur_list->size() > 1){

	const Trigger& cur_trig = (*cur_list)[0].trig;//here we have a polarity problem

	//	if  ( d_allout && cur_trig.isSuperSimple && !cur_trig.hasTrans) continue;
	const Expr& general_vterm = (*iter_trig).first;
	vector<ExprMap<Expr> > binds;      
	newTopMatch(gterm, general_vterm, binds, cur_trig);
	
	for(size_t trig_index = 0; trig_index< cur_list->size(); trig_index++){
	  size_t univ_id = (*cur_list)[trig_index].univ_id;
	  const Trigger& ind_cur_trig = (*cur_list)[trig_index].trig;
	  const ExprMap<Expr>& trig_map = (*cur_list)[trig_index].binds;
	  
	  for(size_t i=0; i<binds.size(); i++){
	    ExprMap<Expr>& cur_map = binds[i];
	    vector<Expr> bind_vec;
	    const vector<Expr>& bVarsThm = d_univs[univ_id].getExpr().getVars();
	    for(size_t j=0; j< bVarsThm.size(); j++){
	      const Expr& inter=(*(trig_map.find(bVarsThm[j]))).second;
	      const Expr& inter2 = cur_map[inter];
	      bind_vec.push_back(inter2);
	    }
	    synNewInst(univ_id, bind_vec, gterm, ind_cur_trig);
	  }
	}
      }
      else{
	FatalAssert(false, "error in matchlistold");
      }
    }//end of for each trig begins with head
  }// end of each gterm
}


void TheoryQuant::newTopMatch(const Expr& gterm, 
			      const Expr& vterm, 
			      vector<ExprMap<Expr> >& binds, 
			      const Trigger& trig){
  ExprMap<Expr>  cur_bind;
  if(trig.isSuperSimple){
    for(int i = vterm.arity()-1; i>=0 ; i--){
      cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
    } 
    binds.push_back(cur_bind);
    return;
  }
  
  if(trig.isSimple){
    for(int i = vterm.arity()-1; i>=0 ; i--){
      if(BOUND_VAR != vterm[i].getKind()){
	if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
	  return ;
	}
      }
      else{
	cur_bind[vterm[i]] = simplifyExpr(gterm[i]);
      }
    }
    binds.push_back(cur_bind);
    return;
  }


  if(!isSysPred(vterm)){ //then gterm cannot be a syspred
    if(!gterm.getType().isBool()){
      //      res2= recSynMatch(gterm, vterm, env);
      matchChild(gterm, vterm, binds);
      return;
    }

    matchChild(gterm, vterm, binds);
    return;

	
    if(!*d_usePolarity){
      //      return recSynMatch(gterm, vterm, env);
      matchChild(gterm, vterm, binds);
      return;
    }
    
    const bool gtrue = (trueExpr()==findExpr(gterm));
    //    const bool gtrue = (trueExpr()==simplifyExpr(gterm));
    if(gtrue ){
      if((Neg==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	matchChild(gterm, vterm, binds);
	return;
      }
      else{
	//	cout<<"returned 1"<<endl;
	return;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    //const bool gfalse = (falseExpr()==simplifyExpr(gterm));
    if(gfalse){
      if((Pos==trig.polarity || PosNeg==trig.polarity)) {
	//	return recSynMatch(gterm, vterm, env);
	matchChild(gterm, vterm, binds); //it is possible that we need binds here, not a single bind
	return;
      }
      else{
	//	cout<<"returned 2"<<endl;
	return;
      }
    }


//     cout<<"immpossible here in new top match"<<endl;
//     cout<<"vterm "<<vterm<<endl;
//     cout<<trig.polarity<<endl;
//     cout<<gtrue<<" | " <<gfalse<<endl;
//     cout<<"gterm " <<gterm<<endl;
//     cout<<"gterm " <<simplifyExpr(gterm)<<endl;
    
    matchChild(gterm, vterm, binds);
    return;

    return;
  }
  else{ // must be syspreds
    //we can move the work to split vterm into left and right into setuptriggers
    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);
    
    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }
    
    Expr vr, vl;
    Expr tvr, tvl;
    
    tvr=null_expr;
    tvl=null_expr;
    
    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      FatalAssert(false, "impossilbe in toppred");
    }
    
    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }
    
    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }
    
    
    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));
    
    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());
    
    //    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");
    
    if(!*d_usePolarity){
      if((recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind))){
	binds.push_back(cur_bind); // it is possible that cur_bind will be binds
	return;
      }
      else{
	return;
      }
    }
    if((Neg==trig.polarity || PosNeg==trig.polarity)) {
      if (( gtrue ) )  {
	if (recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(recSynMatch(gl, vr, cur_bind) && recSynMatch(gr, vl, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
    }
    else if((Pos==trig.polarity || PosNeg==trig.polarity)) {
      if (( gfalse )) {
	if(recSynMatch(gl, vl, cur_bind) && recSynMatch(gr, vr, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
      else {
	if(recSynMatch(gl, vr, cur_bind) && recSynMatch(gr, vl, cur_bind)){
	  binds.push_back(cur_bind);
	  return;
	}
	else{
	  return;
	}
      }
    }
    else {
      FatalAssert(false, "impossible polarity for trig");
	//DebugAssert(false, "impossible polarity for trig");
//      res = false;
      return;
    }
  } 
}

/*
bool TheoryQuant::synMatchTopPred(const Expr& gterm, Trigger trig, ExprMap<Expr>& env){


  Expr vterm = trig.getEx();

  TRACE("quant toppred", "top pred: gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");

  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert ((BOUND_VAR != vterm.getKind()),"top pred match "+gterm.toString()+" has bound var");

  if(gterm.isEq() || vterm.isEq()){
    return false; // we do not match with equality
  }

  bool res2=false;
  
  if(vterm.arity() != gterm.arity()) return false;
  
  if(trig.isSuperSimp()){
    if(trig.getHead() == getHead(gterm) ){
      for(int i = vterm.arity()-1; i>=0 ; i--){
	env[vterm[i]] = simplifyExpr(gterm[i]);
      } 
      return true;
    }
    return false;
  }
  


  if(trig.isSimp()){
    if(trig.getHead() == getHead(gterm) ){
       for(int i = vterm.arity()-1; i>=0 ; i--){
 	if(BOUND_VAR != vterm[i].getKind()){
 	  if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
 	    return false;
 	  }
 	} 
       }
      for(int i = vterm.arity()-1; i>=0 ; i--){
	if(BOUND_VAR == vterm[i].getKind()){
	  if(d_allout){
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	  else {
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	} 
      }
      return true;
    }
    else{
      return false;
    }
  }

  if(!(isSysPred(vterm) && isSysPred(gterm))){
    if(isSysPred(vterm) || isSysPred(gterm)) {
      return false;
    }
    if(!usefulInMatch(gterm)){
      return false;
    }
    if(trig.getHead() != getHead(gterm)){
      return false;
    }
    
    if(!gterm.getType().isBool()){
      //      res2= recSynMatch(gterm, vterm, env);
      res2= matchChild(gterm, vterm, env);
      return res2;
    }
    
    if(!*d_usePolarity){
      //      return recSynMatch(gterm, vterm, env);
      return matchChild(gterm, vterm, env);
    }
    
    const bool gtrue = (trueExpr()==findExpr(gterm));
    if(gtrue ){
      if(trig.isNeg()) {
	//	return recSynMatch(gterm, vterm, env);
	return matchChild(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    if(gfalse){
      if (trig.isPos()){
	//	return recSynMatch(gterm, vterm, env);
	return matchChild(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    else {
      return false;
    }
  }
  else{
    DebugAssert((2==gterm.arity() && 2==vterm.arity()), "impossible situation in top pred");
    DebugAssert(!((isLE(gterm) || isLT(gterm)) && !isIntx(gterm[0],0)), "canonical form changed");
    
#ifdef DEBUG
    if( CVC3::debugger.trace("quant toppred")  ){
      cout << "toppred gterm, vterm" << gterm << "::" << vterm << endl;
      cout << findExpr(gterm) << "::" << trig.isPos() << "|" << trig.isNeg() << endl;
    }
#endif
    
    
    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);
    
    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }
    
    Expr vr, vl;
    Expr tvr, tvl;
    
    tvr=null_expr;
    tvl=null_expr;
    
    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      DebugAssert(false, "impossilbe in toppred");
    }
    
    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }
    
    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }
    
    
    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));
    
    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());
    
    bool res;
    
    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");
    
    if(!*d_usePolarity){
      return (recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
    }
    
    if(trig.isNeg()){
      if (( gtrue ) )  {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else if(trig.isPos()){
      if (( gfalse )) {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env)); 
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else {
      DebugAssert(false, "impossible polarity for trig");
      res = false;
    }
    
#ifdef DEBUG
    if( CVC3::debugger.trace("quant toppred")  ){
      cout<<"res| "<< res << " | " << gtrue << " | " << gfalse << endl;
    }
#endif
    return res;
  }
}
*/

bool TheoryQuant::recSynMatch(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  TRACE("quant match", "gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  
  if (BOUND_VAR == vterm.getKind() )  {
    TRACE("quant match", "bound var found;", vterm.toString(),"");
    ExprMap<Expr>::iterator p = env.find(vterm);
    if ( p != env.end()){
      if (simplifyExpr(gterm) != simplifyExpr(p->second)){ 
	return false; 
      }
      else
	return true;
    }
    else {
      env[vterm] = simplifyExpr(gterm);
      return true; 
    }
  }
  else if (!vterm.containsBoundVar()){
    //    return true;
    //    cout<<"vterm and gterm"<<vterm << " # " <<gterm<<endl;
    if(simplifyExpr(vterm) == simplifyExpr(gterm)) {
      return true;
    }
    else{
      return false;
    }
  }

  else if(false && isSysPred(vterm) && isSysPred(gterm)){
    
    TRACE("quant syspred"," vterm, gterm ", vterm.toString()+" :|: ", gterm.toString());
    TRACE("quant syspred"," simplified vterm, gterm ", simplifyExpr(vterm).toString()+" :|: ", simplifyExpr(gterm).toString());
    FatalAssert(false, "should not be here in synmatch");
    exit(3);
  }
  else{ 
      if(canGetHead(vterm)){
	Expr vhead = getHead(vterm);
	TRACE("quant match", "head vterm:", getHead(vterm), "");
	if(vterm.isAtomicFormula()){
	  if (canGetHead(gterm)) {
	    if ( vhead != getHead(gterm) ){
	      return false;
	    }
	    return matchChild(gterm, vterm, env);
// 	    for(int i=vterm.arity()-1; i >= 0; i--){
// 	      if (false == recSynMatch(gterm[i], vterm[i] , env))
// 		return false;
// 	    }
// 	    return true;
	  }
	  else{
	    return false;
	  }
	}
	if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	  //	  if(gterm.arity() != vterm.arity()){
	  //	    return false;
	  //	  }
// 	  for(int i=vterm.arity()-1; i >= 0; i--){
// 	    if (false == recSynMatch(gterm[i], vterm[i] , env)) {
// 	      return false;
// 	    }
// 	  }
// 	  return true;
	  return matchChild(gterm, vterm, env);
	}
	
	if(!*d_useEqu){
	  return false;
	}

	
	//	cout<<"==============================="<<endl;
	//	cout<<gterm<<" # " <<vterm<<endl;

	/*
	{ // 
	  //	  std::set<Expr> eq_set;
	  std::map<Expr,bool> eq_set;
	  eq_set.clear();
	  eq_set[gterm]=true;
	  
	  std::queue<Expr> eq_queue;

	  ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.find(gterm);
	  
	  if(iter != d_eq_list.end()){
	    for(size_t len =0; len< iter->second->size(); len++){
	      eq_queue.push((*(iter->second))[len]);
	    }
	    int count =0;
	    while(eq_queue.size()>0){
	      count++;
	      const Expr& cur = eq_queue.front();
	      eq_queue.pop();
	      if(eq_set.find(cur) == eq_set.end()){
		if(canGetHead(cur) && getHead(cur) == vhead){
// 		  	      cout<<"VTERM: "<<vterm<<endl;
// 		  	      cout<<"FOUND: "<<cur<<endl;
// 		  	      cout<<"GTERM:  "<<gterm<<endl;
		  //		  cout<<"--good match: " << count << "  // " << gterm << " # " << cur << endl;
		  //		  cout<<"===good simple: " << count << "  // " << simplifyExpr(gterm) << " # " << simplifyExpr(cur) << endl;

		  if(simplifyExpr(cur) != simplifyExpr(gterm)){
		    // return false;
		    //		    return matchChild(cur, vterm, env);
		    //		    cout<<"en? "<<gterm<<" # " <<cur <<" # " <<vterm<<endl;
		  }
		  else{
		    //		    cout<<"--good match: " << count << "  // " << gterm << " # " << cur << endl;
		    //		    cout<<"===good simple: " << count << "  // " << simplifyExpr(gterm) << " # " << simplifyExpr(cur) << endl;
		    //		    return matchChild(cur, vterm, env);
		  }
		}
		
		eq_set[cur]=true;
		ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.find(cur);
		
		if(iter != d_eq_list.end()){
		  for(size_t len =0; len< iter->second->size(); len++){
		    eq_queue.push((*(iter->second))[len]);
		  }
		}
	      }
	    }
	  }
	  //	  return false;
	}
	*/
	if( d_same_head_expr.count(vhead) > 0 ) {
	  const Expr& findGterm = simplifyExpr(gterm);
	  //if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	  TRACE("quant match", "find gterm:", findGterm.toString(),"");
	  CDList<Expr>* gls = d_same_head_expr[vhead];
	  /*
	  { int count =0;
	    for(size_t i = 0; i<gls->size(); i++){
	      if (simplifyExpr((*gls)[i]) == findGterm){
 		count++;
	      }
	    }
	    if(count>1){
	      cout<<"count " << count << " # " << gls->size() << " | "<<gterm<<endl;
	      for(size_t i = 0; i<gls->size(); i++){
		if (simplifyExpr((*gls)[i]) == findGterm){
		  cout<<"eq "<<(*gls)[i]<<endl;
		}
	      }
	    }
	  }
	  */
	  for(size_t i = 0; i<gls->size(); i++){
	    if (simplifyExpr((*gls)[i]) == findGterm){
	      TRACE("quant match", "find matched gterm:", (*gls)[i].toString(),"");
	      DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");

	      const Expr& newgterm = (*gls)[i];
	      for(int child=vterm.arity()-1; child >= 0 ; child--){
		if (false == recSynMatch(newgterm[child], vterm[child] , env)){
		  TRACE("quant match", "match false", (*gls)[i][child].toString(), vterm[child].toString());
		  return false;
		}
	      }
	      TRACE("quant match", "good match, return true:", gterm, vterm.toString());
	      //	      cout<<"quant good match: " <<i<<" // "<<gterm << " # "<<vterm<<endl;
	      //	      cout<<"quant simple: " <<i<<" // "<<simplifyExpr(gterm) << " # "<<vterm<<endl;
	      return true;
	    }
	  }//end of for
	  return false;
	} 
	else  {
	  return false;//end of if
	}
      }
      else{
 	TRACE("quant match more", "match more", gterm.toString()+" # ", vterm.toString());
 	if( (gterm.getKind() == vterm.getKind()) && 
	    (gterm.arity() == vterm.arity()) &&
	    gterm.arity()>0 ){
//  	  for(int child=0; child < vterm.arity() ; child++){
//  	    if (false == recSynMatch(gterm[child], vterm[child] , env)){
//  	      TRACE("quant match", "match false", gterm[child].toString(), vterm[child].toString());
//  	      return false;
//  	    }
//  	  }
//  	  return true;
//   	  if( gterm.getKind() == PLUS || gterm.getKind() == MINUS){
//   	    cout<<"g v"<<gterm<< " # " <<vterm<<endl;
//   	  }

	  return matchChild(gterm, vterm, env);
 	}
	else {
//   	  if( gterm.getKind() == PLUS || gterm.getKind() == MINUS){
// 	    static bool gvfound = false;
//   	    if(!gvfound){
// 	      cout<<"g v 1"<<endl;
// 	      gvfound =true;
// 	    }
	    //gterm<< " # " <<vterm<<endl;
	  //  }
	  return false;
	}
      }
  }
}

/*

bool TheoryQuant::synMatchTopPred(const Expr& gterm, Trigger trig, ExprMap<Expr>& env){

  const Expr vterm = trig.getEx();

  TRACE("quant toppred", "top pred: gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");

  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  DebugAssert ((BOUND_VAR != vterm.getKind()),"top pred match "+gterm.toString()+" has bound var");

  if(gterm.isEq() || vterm.isEq()){
    return false; // we do not match with equality
  }

  bool res2=false;
  
  //  if(vterm.arity() != gterm.arity()) return false;

  if(trig.isSimp()){
    if(trig.getHead() == getHead(gterm) ){
      for(int i = vterm.arity()-1; i>=0 ; i--){
	if(BOUND_VAR != vterm[i].getKind()){
	  if(simplifyExpr(gterm[i]) != simplifyExpr(vterm[i])) {
	    return false;
	  }
	} 
      }
      for(int i = vterm.arity()-1; i>=0 ; i--){
	if(BOUND_VAR == vterm[i].getKind()){
	  if(d_allout){
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	  else {
	    env[vterm[i]] = simplifyExpr(gterm[i]);
	  }
	} 
      }
      return true;
    }
    else{
      return false;
    }
  }

  if(!(isSysPred(vterm) && isSysPred(gterm))){
    if(isSysPred(vterm) || isSysPred(gterm)) {
      return false;
    }
    if(!usefulInMatch(gterm)){
      return false;
    }
    if(trig.getHead() != getHead(gterm)){
      return false;
    }
    
    if(!gterm.getType().isBool()){
      res2= recSynMatch(gterm, vterm, env);
      return res2;
    }
    
    if(!*d_usePolarity){
      return recSynMatch(gterm, vterm, env);
    }
    
    const bool gtrue = (trueExpr()==findExpr(gterm));
    if(gtrue ){
      if(trig.isNeg()) {
	return recSynMatch(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    const bool gfalse = (falseExpr()==findExpr(gterm));
    if(gfalse){
      if (trig.isPos()){
	return recSynMatch(gterm, vterm, env);
      }
      else{
	return false;
      }
    }
    else {
      return false;
    }
  }
  else{
    DebugAssert((2==gterm.arity() && 2==vterm.arity()), "impossible situation in top pred");
    DebugAssert(!((isLE(gterm) || isLT(gterm)) && !isIntx(gterm[0],0)), "canonical form changed");
    
#ifdef DEBUG
    if( CVC3::debugger.trace("quant toppred")  ){
      cout << "toppred gterm, vterm" << gterm << "::" << vterm << endl;
      cout << findExpr(gterm) << "::" << trig.isPos() << "|" << trig.isNeg() << endl;
    }
#endif
    
    
    Expr gl = getLeft(gterm[1]);
    Expr gr = getRight(gterm[1]);
    
    if(null_expr == gr || null_expr == gl){
      gl = gterm[0];
      gr = gterm[1];
    }
    
    Expr vr, vl;
    Expr tvr, tvl;
    
    tvr=null_expr;
    tvl=null_expr;
    
    if(isGE(vterm) || isGT(vterm)){
      vr = vterm[0];
      vl = vterm[1];
    }
    else if(isLE(vterm) || isLT(vterm)){
      vr = vterm[1];
      vl = vterm[0];
    }
    else{
      DebugAssert(false, "impossilbe in toppred");
    }
    
    if(isIntx(vl,0)){
      tvl = getLeft(vr);
      tvr = getRight(vr);
    }
    else if(isIntx(vr,0)) {
      tvl = getLeft(vl);
      tvr = getRight(vl);
    }
    
    if( (null_expr != tvl) && (null_expr != tvr)){
      vl = tvl;
      vr = tvr;
    }
    
    
    const bool gtrue = (trueExpr()==findExpr(gterm));
    const bool gfalse = (falseExpr()==findExpr(gterm));
    
    TRACE("quant toppred"," vl, gl, vr, gr:", vl.toString()+"::"+gl.toString()+"||", vr.toString()+"::"+gr.toString());
    
    bool res;
    
    DebugAssert(!(trig.isNeg() && trig.isPos()), "expr in both pos and neg");
    
    if(!*d_usePolarity){
      return (recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
    }
    
    if(trig.isNeg()){
      if (( gtrue ) )  {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env));
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else if(trig.isPos()){
      if (( gfalse )) {
	res=(recSynMatch(gl, vl, env) && recSynMatch(gr, vr, env)); 
      }
      else {
	res=(recSynMatch(gl, vr, env) && recSynMatch(gr, vl, env));
      }
    }
    else {
      DebugAssert(false, "impossible polarity for trig");
      res = false;
    }
    
#ifdef DEBUG
    if( CVC3::debugger.trace("quant toppred")  ){
      cout<<"res| "<< res << " | " << gtrue << " | " << gfalse << endl;
    }
#endif
    return res;
  }
}

bool TheoryQuant::recSynMatch(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env){
  TRACE("quant match", "gterm:| "+gterm.toString()," vterm:| "+vterm.toString(),"");
  DebugAssert ((BOUND_VAR != gterm.getKind()),"gound term "+gterm.toString()+" has bound var");
  
  if (BOUND_VAR == vterm.getKind())  {
    TRACE("quant match", "bound var found;", vterm.toString(),"");
    ExprMap<Expr>::iterator p = env.find(vterm);
    if ( p != env.end()){
      if (simplifyExpr(gterm) != simplifyExpr(p->second)){ 
	return false; 
      }
      else
	return true;
    }
    else {
      env[vterm] = simplifyExpr(gterm);
      return true; 
    }
  }
  else if (!vterm.containsBoundVar()){
    if(simplifyExpr(vterm) == simplifyExpr(gterm)) {
      return true;
    }
    else{
      return false;
    }
  }

  else if(false && isSysPred(vterm) && isSysPred(gterm)){
    
    TRACE("quant syspred"," vterm, gterm ", vterm.toString()+" :|: ", gterm.toString());
    TRACE("quant syspred"," simplified vterm, gterm ", simplifyExpr(vterm).toString()+" :|: ", simplifyExpr(gterm).toString());
    FatalAssert(false, "should not be here in synmatch");
    exit(3);
  }
  else{ 
      if(canGetHead(vterm)){
	Expr vhead = getHead(vterm);
	TRACE("quant match", "head vterm:", getHead(vterm), "");
	if(vterm.isAtomicFormula()){
	  if (canGetHead(gterm)) {
	    if ( vhead != getHead(gterm) ){
	      return false;
	    }
	    for(int i=vterm.arity()-1; i >= 0; i--){
	      if (false == recSynMatch(gterm[i], vterm[i] , env))
		return false;
	    }
	    return true;
	  }
	  else{
	    return false;
	  }
	}
	if ( (canGetHead(gterm)) && vhead == getHead(gterm)){
	  if(gterm.arity() != vterm.arity()){
	    return false;
	  }
	  for(int i=vterm.arity()-1; i >= 0; i--){
	    if (false == recSynMatch(gterm[i], vterm[i] , env)) {
	      return false;
	    }
	  }
	  return true;
	}
	
	if(false && !*d_useEqu){
	  return false;
	}

	if( d_same_head_expr.count(vhead) > 0 ) {
	  const Expr& findGterm = simplifyExpr(gterm);
	  //if(isIntx(findGterm,0) || isIntx(findGterm,1)) return false;//special for simplify benchmark
	  TRACE("quant match", "find gterm:", findGterm.toString(),"");
	  CDList<Expr>* gls = d_same_head_expr[vhead];
	  for(size_t i = 0; i<gls->size(); i++){
	    if (simplifyExpr((*gls)[i]) == findGterm){
	      TRACE("quant match", "find matched gterm:", (*gls)[i].toString(),"");
	      DebugAssert((*gls)[i].arity() == vterm.arity(), "gls has different arity");

	      for(int child=vterm.arity()-1; child >= 0 ; child--){
		const Expr& newgterm = (*gls)[i];
		if (false == recSynMatch(newgterm[child], vterm[child] , env)){
		  TRACE("quant match", "match false", (*gls)[i][child].toString(), vterm[child].toString());
		  return false;
		}
	      }
	      TRACE("quant match", "good match, return true:", gterm, vterm.toString());
	      return true;
	    }
	  }//end of for
	  return false;
	} 
	else  {
	  return false;//end of if
	}
      }
      else{
 	TRACE("quant match more", "match more", gterm.toString()+" # ", vterm.toString());
 	if( (gterm.getKind() == vterm.getKind()) && 
	    (gterm.arity() == vterm.arity()) &&
	    gterm.arity()>0 ){
 	  for(int child=0; child < vterm.arity() ; child++){
 	    if (false == recSynMatch(gterm[child], vterm[child] , env)){
 	      TRACE("quant match", "match false", gterm[child].toString(), vterm[child].toString());
 	      return false;
 	    }
 	  }
 	  return true;
 	}
	else  return false;
      }
  }
}

*/

void TheoryQuant::goodSynMatch(const Expr& e,
			       const std::vector<Expr> & boundVars,
			       std::vector<std::vector<Expr> >& instBinds,
			       std::vector<Expr>& instGterms,
			       const CDList<Expr>& allterms,		       
			       size_t tBegin){
  for (size_t i=tBegin; i<allterms.size(); i++)    {
    Expr gterm = allterms[i];
    if (0 == gterm.arity() )
      continue;
    TRACE("quant matching", gterm.toString(), "||", e.toString()) ;
    //    if( usefulInMatch(gterm) && possibleMatch(gterm,e))   {
    if(usefulInMatch(gterm))   {
      ExprMap<Expr> env;
      env.clear();
      bool found = recSynMatch(gterm,e,env); 
      if(found){
	
	TRACE("quant matching found", " good:",gterm.toString()+" to " , e.toString());
	TRACE("quant matching found", " simplified good:",simplifyExpr(gterm).toString()+" to " , simplifyExpr(e).toString());
	std::vector<Expr> inst;
	
	DebugAssert((boundVars.size() == env.size()),"bound var size != env.size()");
	
	for(size_t i=0; i<boundVars.size(); i++) {
	  ExprMap<Expr>::iterator p = env.find(boundVars[i]);
	  DebugAssert((p!=env.end()),"bound var cannot be found");
	  inst.push_back(p->second);
	}
	instBinds.push_back(inst);
	instGterms.push_back(gterm);
      }
      else{
	TRACE("quant matching", "bad one",gterm.toString()+" to " , e.toString());
      }
    }
  }
}
 
/*
void TheoryQuant::goodSynMatchNewTrig(const Trigger& trig,
				      const std::vector<Expr> & boundVars,
				      std::vector<std::vector<Expr> >& instBinds,
				      std::vector<Expr>& instGterms,
				      const CDList<Expr>& allterms,		       
				      size_t tBegin){
  for (size_t i=tBegin; i<allterms.size(); i++)    {
    Expr gterm (allterms[i]);
    //    TRACE("quant matching", gterm.toString(), "||", trig.getEx().toString()) ;
    if(usefulInMatch(gterm)) {
      ExprMap<Expr> env;
      env.clear();
      bool found = synMatchTopPred(gterm,trig,env); 
      if(found){
	//TRACE("quant matching found", " top good:",gterm.toString()+" to " , trig.getEx().toString());
	std::vector<Expr> inst;
	inst.clear();
	DebugAssert((boundVars.size() <= env.size()),"bound var size != env.size()");

	for(size_t i=0; i<boundVars.size(); i++) {
	  ExprMap<Expr>::iterator p = env.find(boundVars[i]);
	  DebugAssert((p!=env.end()),"bound var cannot be found");
	  inst.push_back(p->second);
	}
	
	instBinds.push_back(inst);
	instGterms.push_back(gterm);
      }
      else{
	//	TRACE("quant matching", "bad one",gterm.toString()+" to ", trig.getEx().toString());
      }
    }
  }
}
*/

/*
bool TheoryQuant::hasGoodSynInstNewTrigOld(Trigger& trig,
					   std::vector<Expr> & boundVars,
					   std::vector<std::vector<Expr> >& instBinds,
					   std::vector<Expr>& instGterms,
					   const CDList<Expr>& allterms,		       
					   size_t tBegin){

  const std::set<Expr>& bvs = getBoundVars(trig.getEx());
  
  boundVars.clear();
  for(std::set<Expr>::const_iterator i=bvs.begin(),iend=bvs.end(); i!=iend; ++i)
    boundVars.push_back(*i);
  
  instBinds.clear();
  goodSynMatchNewTrig(trig, boundVars, instBinds, instGterms, allterms, tBegin);
  
  if (instBinds.size() > 0)
    return true;
  else
    return false;    
}


bool TheoryQuant::hasGoodSynInstNewTrig(Trigger& trig,
					const std::vector<Expr>& boundVars,
					std::vector<std::vector<Expr> >& instBinds,
					std::vector<Expr>& instGterms,
					const CDList<Expr>& allterms,		       
					size_t tBegin){
//   boundVars=trig.getBVs();
//   const std::set<Expr>& bvs = getBoundVars(trig.getEx());
  
//   boundVars.clear();
//   for(std::set<Expr>::const_iterator i=bvs.begin(),iend=bvs.end(); i!=iend; ++i)
//     boundVars.push_back(*i);
  
  instBinds.clear();
  goodSynMatchNewTrig(trig, boundVars, instBinds, instGterms, allterms, tBegin);
  
  if (instBinds.size() > 0)
    return true;
  else
    return false;    
}
*/
int TheoryQuant::loc_gterm(const std::vector<Expr>& border,
			   const Expr& vterm, 
			   int pos){
  const std::vector<Expr>& order = d_mtrigs_bvorder[vterm];
  const Expr& var = order[pos];
  for(size_t i=0; i<border.size(); i++){
    if (border[i] == var) return i;
  }

  DebugAssert(false, "internal error in loc_germ");
  return -1;
}

void  TheoryQuant::recSearchCover(const std::vector<Expr>& border,
				  const std::vector<Expr>& mtrigs, 
				  int cur_depth, 
				  std::vector<std::vector<Expr> >& instSet,
				  std::vector<Expr>& cur_inst
				  ){
  int max_dep = mtrigs.size();

  if(cur_depth >= max_dep) return; 

  Expr cur_vterm = mtrigs[cur_depth]; //get the current vterm
  if(d_mtrigs_inst.count(cur_vterm) <=0) return;
  CDList<std::vector<Expr> >* gterm_list = d_mtrigs_inst[cur_vterm]; // get the list of ground term found for cur_vterm
  for(size_t i=0; i< gterm_list->size(); i++){
    const std::vector<Expr>& cur_gterm = (*gterm_list)[i];
    std::vector<Expr> new_inst(border.size()); //get a new inst array
    
    for(size_t j=0; j< border.size(); j++){
      new_inst[j]=cur_inst[j]; //copy to cur_int to new_inst
    }
    
    bool has_problem = false;//next, try to put the cur gterm into new_inst
    for(size_t j=0; j< cur_gterm.size(); j++){
      int cur_loc_gterm = loc_gterm(border, cur_vterm, j);
      
      if( null_expr == new_inst[cur_loc_gterm]){
	new_inst[cur_loc_gterm] = cur_gterm[j];
      }
      else if (new_inst[cur_loc_gterm] != cur_gterm[j]){
	has_problem = true;
	break;
      }
      
    }
    
    if (has_problem){
      continue;
    }

    bool finished = true;
    for(size_t j=0; j< border.size() ;j++){
      if(null_expr == new_inst[j]){
	finished = false;
	break;
      }
    }
    
    if(finished){
      std::vector<Expr> good_inst;
      for(size_t j=0; j<border.size(); j++){
	good_inst.push_back(new_inst[j]);
      }
      instSet.push_back(good_inst);
    }
    else{
      recSearchCover(border,
		     mtrigs, 
		     cur_depth+1, 
		     instSet,
		     new_inst);
    }
  }//end of for
}

void  TheoryQuant::searchCover(const Expr& thm,
			       const std::vector<Expr>& border,
			       std::vector<std::vector<Expr> >& instSet
			       ){
  std::vector<Expr> dumy(border.size()) ; //use dynamic array here
  for(size_t j=0; j< border.size() ;j++){
    dumy[j]=null_expr;
  }
  const std::vector<Expr>& mtrigs = d_multTriggers[thm];
  recSearchCover(border, mtrigs, 0, instSet, dumy);
}

bool TheoryQuant::hasGoodSynMultiInst(const Expr& thm,
				      std::vector<Expr> & boundVars,
				      std::vector<std::vector<Expr> >& instSet,
				      const CDList<Expr>& allterms,		       
				      size_t tBegin){

  const std::set<Expr>& bvs = getBoundVars(thm);
  
  boundVars.clear();
  for(std::set<Expr>::const_iterator i=bvs.begin(),iend=bvs.end(); i!=iend; ++i)
    boundVars.push_back(*i);
  
  instSet.clear();
  
  bool new_match = false;
  //assumption: every trig is different
  //this is not true later, fix this asap
  const std::vector<Expr>& mtrigs = d_multTriggers[thm];
  
  for(std::vector<Expr>::const_iterator i= mtrigs.begin(), iend = mtrigs.end(); i != iend; i++){

    if(d_mtrigs_bvorder[*i].empty()){ //setup an order
      const std::set<Expr>& trig_bvs = getBoundVars(*i);
      for(std::set<Expr>::const_iterator j= trig_bvs.begin(), jend = trig_bvs.end();
	  j != jend;
	  j++){
	d_mtrigs_bvorder[*i].push_back(*j);
      }
    }
    
    const std::vector<Expr>& trig_bvorder = d_mtrigs_bvorder[*i];
    //    std::set<std::vector<Expr> > trig_insts;    
    std::vector<std::vector<Expr> > trig_insts;    
    trig_insts.clear();

    std::vector<Expr> gtms;
    goodSynMatch(*i, trig_bvorder, trig_insts, gtms, allterms, tBegin);

    if (trig_insts.size() > 0){
      new_match=true;
      if(d_mtrigs_inst.count(*i) <= 0){
	d_mtrigs_inst[*i] = new(true) CDList<std::vector<Expr> > (theoryCore()->getCM()->getCurrentContext());
      }
      for(std::vector<std::vector<Expr> >::const_iterator j = trig_insts.begin(), jend = trig_insts.end();
	  j != jend;
	  j++){
	
	d_mtrigs_inst[*i]->push_back(*j);
	for(std::vector<Expr>::const_iterator k = j->begin(), kend = j->end();
	    k != kend;
	    k++){
	}
      }
    }
  } // end of for

  for(std::vector<Expr>::const_iterator i= mtrigs.begin(), iend = mtrigs.end(); i != iend; i++){
    if (d_mtrigs_inst.count(*i) <=0 ) continue;
    for(CDList<std::vector<Expr> >::const_iterator j = d_mtrigs_inst[*i]->begin(), 
	  jend = d_mtrigs_inst[*i]->end();
	  j != jend;
	  j++){
      
      for(std::vector<Expr>::const_iterator k = j->begin(), kend = j->end();
	  k != kend;
	  k++){
      }
    }
  }
  {//code for search a cover
    if(new_match){
      searchCover(thm, boundVars, instSet);
    }
  }      

  if(instSet.size() > 0 ) {
    return true;
  }
  else {
    return false;
  }
  
}

bool inStrCache(std::set<std::string> cache, std::string str){
  return (cache.find(str) != cache.end());
} 


bool TheoryQuant::hasGoodSemInst(const Expr& e,
				 std::vector<Expr> & boundVars,
				 std::set<std::vector<Expr> >& instSet,
				 size_t tBegin){
  return false;
}

void genPartInstSetThm(const std::vector<Expr>&  bVarsThm,
		       std::vector<Expr>& bVarsTerm,
		       const std::vector<std::vector<Expr> >& termInst,
		       std::vector<std::vector<Expr> >& instSetThm){
  ExprMap<bool> bVmap;

  for(size_t i=0; i< bVarsThm.size(); ++i)    {
    bVmap[bVarsThm[i]]=true;
  }

  std::vector<Expr> tempBVterm;
  std::vector<int> locTerm;

  for (size_t j=0; j<bVarsTerm.size(); j++){
    if (bVmap.count(bVarsTerm[j]) > 0){
      locTerm.push_back(1);
      tempBVterm.push_back(bVarsTerm[j]);
    }
    else{
      locTerm.push_back(0);
    }
  }

  DebugAssert(locTerm.size() == bVarsTerm.size(), "locTerm.size !- bVarsTerm.size()");

  for(std::vector<std::vector<Expr> >::const_iterator i=termInst.begin(),
	iend=termInst.end();i!=iend; i++)  {
    std::vector<Expr> buf;
    buf.clear();
    for(size_t j=0; j< bVarsTerm.size(); ++j){
      if(locTerm[j])
	buf.push_back((*i)[j]);
    }
    instSetThm.push_back(buf);
  }
  bVarsTerm=tempBVterm;
}


void genInstSetThm(const std::vector<Expr>& bVarsThm,
		   const std::vector<Expr>& bVarsTerm,
		   const std::vector<std::vector<Expr> >& termInst,
		   std::vector<std::vector<Expr> >& instSetThm){

  std::vector<int> bVmap;

  for(size_t i=0; i< bVarsThm.size(); ++i)    {
    bVmap.push_back(-1);
    for (size_t j=0; j<bVarsTerm.size(); j++){
      if (bVarsThm[i] == bVarsTerm[j]){
	DebugAssert(bVmap[i] == -1, "bVmap[1] != -1");
	bVmap[i]=j;	      
      }
    }
  }
  
  for(size_t i=0; i< bVarsThm.size(); ++i)
    if( -1 == bVmap[i])  {
      return;
    }
  
  for(std::vector<std::vector<Expr> >::const_iterator i=termInst.begin(),
	iend=termInst.end();i!=iend; i++)  {
    std::vector<Expr> buf;
    buf.clear();
    for(size_t j=0; j< bVarsThm.size(); ++j){
      buf.push_back((*i)[bVmap[j]]);
    }
    instSetThm.push_back(buf);
  }
}
	

/*
void TheoryQuant::synInst(const Theorem & univ, const CDList<Expr>& allterms, size_t tBegin ){
  if(d_useFullTrig){
    synFullInst(univ, allterms, tBegin);
  }

  if(d_useMultTrig){
    synMultInst(univ, allterms, tBegin);
  }

  if(d_usePartTrig){
    synPartInst(univ, allterms, tBegin);
  }
}
*/
inline bool TheoryQuant::transFound(const Expr& comb){
  return (d_trans_found.count(comb) > 0);
}

inline void TheoryQuant::setTransFound(const Expr& comb){
  d_trans_found[comb] = true;
}

inline bool TheoryQuant::trans2Found(const Expr& comb){
  return (d_trans2_found.count(comb) > 0);
}

inline void TheoryQuant::setTrans2Found(const Expr& comb){
  d_trans2_found[comb] = true;
}


inline CDList<Expr> & TheoryQuant::backList(const Expr& ex){
  if(d_trans_back.count(ex)>0){
    return *d_trans_back[ex];
  }
  else{
    return null_cdlist;
  } 
} 

inline CDList<Expr> & TheoryQuant::forwList(const Expr& ex){
  if(d_trans_forw.count(ex)>0){
    return *d_trans_forw[ex];
  }
  else{
    return null_cdlist;
  } 
} 

inline void  TheoryQuant::pushBackList(const Expr& node, Expr ex){
  if(d_trans_back.count(node)>0){
    d_trans_back[node]->push_back(ex);
  }
  else{
    d_trans_back[node] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext());
    d_trans_back[node]->push_back(ex);
  } 
} 

inline void  TheoryQuant::pushForwList(const Expr& node, Expr ex){
  if(d_trans_forw.count(node)>0){
    d_trans_forw[node]->push_back(ex);
  }
  else{
    d_trans_forw[node] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext());
    d_trans_forw[node]->push_back(ex);
  } 
} 

/*
void TheoryQuant::synFullInst(const Theorem & univ, const CDList<Expr>& allterms, size_t tBegin ){

  const Expr& quantExpr = univ.getExpr();  
  //  const std::vector<Expr>& bVarsThm = quantExpr.getVars();
  std::vector<Expr> bVarsThm = quantExpr.getVars();

  TRACE("quant inst", "try full inst with:|", quantExpr.toString() , " ");
  
  std::vector<std::vector<Expr> > instBindsThm; //set of instantiations for the thm,
  std::vector<std::vector<Expr> > instBindsTerm; //bindings, in the order of bVarsTrig
  std::vector<Expr > instGterms; //instGterms are gterms matched, instBindsTerm and instGterms must have the same length
  std::vector<Expr> bVarsTrig; 

  if(*d_useTrigNew){
    std::vector<Trigger>& new_trigs=d_fullTrigs[quantExpr];
    for( size_t i= 0; i<new_trigs.size(); i++)  {
      Trigger& trig = new_trigs[i];
      //      if( 0 != trig.getPri()) continue;
      TRACE("quant inst","try new full trigger:|", trig.getEx().toString(),"");
      
      instBindsTerm.clear();
      bVarsTrig.clear();
      instBindsThm.clear();
      instGterms.clear();
      
      {//code for trans2
	if(trig.hasTr2()){
	  //if(hasGoodSynInstNewTrig(trig, bVarsTrig, instBindsTerm, instGterms, allterms, tBegin)) {
	  if(hasGoodSynInstNewTrig(trig, trig.getBVs(), instBindsTerm, instGterms, allterms, tBegin)) {
	    for(size_t j=0; j<instBindsTerm.size(); j++){
	      DebugAssert(2 == instBindsTerm[j].size(), "internal error in trans2");

	      Expr& gterm = instGterms[j];
	      
	      if(simplifyExpr(instBindsTerm[j][0]) != simplifyExpr(instBindsTerm[j][1])){
		Expr comb = Expr(RAW_LIST,instBindsTerm[j][0],instBindsTerm[j][1]);
		if(!trans2Found(comb)){
		  setTrans2Found(comb);
		  
		  TRACE("quant trans","new trans2: ", vectorExpr2string(instBindsTerm[j]), "");		  
		  
		  Expr comb_rev = Expr(RAW_LIST,instBindsTerm[j][1],instBindsTerm[j][0]);
		  if(trans2Found(comb_rev)){
		    Expr sr(instBindsTerm[j][0]);
		    Expr dt(instBindsTerm[j][1]);
		    
		    vector<Expr> bind;
		    bind.clear();
		    bind.push_back(sr);
		    bind.push_back(dt);
		    
		    enqueueInst(univ, bind, gterm);
		    TRACE("quant inst", "trans pred rule2 ", univ.toString(), " | with bind: "+vectorExpr2string(bind));  		    TRACE("quant trans", "trans2 ", vectorExpr2string(bind), "");
		  }
		}
	      } 
	    }
	  }
	  return;
	}
      }
            
      {//code for trans pred
	if(trig.hasTr()){
	  //	  if(hasGoodSynInstNewTrig(trig, bVarsTrig, instBindsTerm, instGterms, allterms, tBegin)) {
	  if(hasGoodSynInstNewTrig(trig, trig.getBVs(), instBindsTerm, instGterms, allterms, tBegin)) {
	    for(size_t j=0; j<instBindsTerm.size(); j++){
	      DebugAssert(2 == instBindsTerm[j].size(), "internal error in trans");

	      Expr& gterm = instGterms[j];

	      if(simplifyExpr(instBindsTerm[j][0]) != simplifyExpr(instBindsTerm[j][1])){

		Expr comb = Expr(RAW_LIST,instBindsTerm[j][0],instBindsTerm[j][1]);

		if(!transFound(comb)){
		  setTransFound(comb);

		  TRACE("quant trans","new: ", vectorExpr2string(instBindsTerm[j]), "");		  

		  Expr sr(instBindsTerm[j][0]);
		  Expr dt(instBindsTerm[j][1]);
		  
		  const CDList<Expr>& dtForw = forwList(dt);
		  const CDList<Expr>& srBack = backList(sr);
		  
		  for(size_t k=0; k<dtForw.size(); k++){
		    vector<Expr> bind;
		    bind.clear();
		    bind.push_back(sr);
		    bind.push_back(dt);
		    bind.push_back(dtForw[k]);

		    enqueueInst(univ, bind, gterm);

		    TRACE("quant inst", "trans pred rule", univ.toString(), " | with bind: "+vectorExpr2string(bind));  
		    TRACE("quant trans", "trans res forw: ", vectorExpr2string(bind), "");
		  }

		  for(size_t k=0; k<srBack.size(); k++){
		    vector<Expr> bind;
		    bind.clear();
		    bind.push_back(srBack[k]);
		    bind.push_back(sr);
		    bind.push_back(dt);

		    enqueueInst(univ, bind, gterm);
		    TRACE("quant inst", "trans pred rule ", univ.toString(), " | with bind: "+vectorExpr2string(bind));
  		    TRACE("quant trans", "trans res back: ", vectorExpr2string(bind), "");
		  }

		  pushForwList(sr,dt);
		  pushBackList(dt,sr);
		}
	      } 
	    }
	  }
	  return;
	}
      }
            
      bool univsHasMoreBVs ;

      univsHasMoreBVs = (d_hasMoreBVs.count(quantExpr) > 0);

      //      if ( !d_allout || !trig.isSimp() || univsHasMoreBVs || *d_useLazyInst){
      //      if ( !d_allout || !trig.isSimp() || univsHasMoreBVs || true){
      if  ( !d_allout || !trig.isSuperSimp() || univsHasMoreBVs ){
      //      if ( !d_allout || !trig.isSimp() || univsHasMoreBVs ){
      */
	/*
	if(hasGoodSynInstNewTrigOld(trig, bVarsTrig, instBindsTerm, instGterms, allterms, tBegin)) {
	  genInstSetThm(bVarsThm, bVarsTrig, instBindsTerm, instBindsThm);
	  for (size_t j = 0; j<instBindsTerm.size(); j++){
 	    const Expr& gterm = instGterms[j];
 	    const std::vector<Expr>& binds = instBindsThm[j];
 	    enqueueInst(univ, trig, binds, gterm); 
 	    TRACE("quant inst", "insert full inst", univ.toString(), " | with bind: "+vectorExpr2string(binds));  
 	  }
 	}
	*/
/*
	bVarsTrig=trig.getBVs();//vVarsTrig is used later, do not forget this.
 	if(hasGoodSynInstNewTrig(trig, bVarsThm, instBindsTerm, instGterms, allterms, tBegin)) {
  	  for (size_t j = 0; j<instBindsTerm.size(); j++){
  	    const Expr& gterm = instGterms[j];
  	    const std::vector<Expr>& binds = instBindsTerm[j];
	    
  	    enqueueInst(univ, trig, binds, gterm); 
	    
  	    TRACE("quant inst", "insert full inst", univ.toString(), " | with bind: "+vectorExpr2string(binds));  
  	  }
  	}
	
      }      
      
      //      if(!d_allout || *d_useLazyInst){
      if(!d_allout){
	if(trig.hasRW() ){
	  
	  if(1 == bVarsTrig.size()){
	    std::vector<Expr> tp = d_arrayIndic[trig.getHead()];
	    for(size_t i=0; i<tp.size(); i++){
	      std::vector<Expr> tp = d_arrayIndic[trig.getHead()];

	      Expr index = tp[i];
	      std::vector<Expr> temp;
	      temp.clear();
	      temp.push_back(index);
	      
	      enqueueInst(univ, temp, index);
	      TRACE("quant inst", "read write rule", univ.toString(), " | with bind: "+vectorExpr2string(temp));  
	    }
	  }
	  else{
	  }
	}
      }
    }//end for each trigger      
  }
}
*/
void TheoryQuant::arrayHeuristic(const Trigger& trig, size_t univ_id){

  std::vector<Expr> tp = d_arrayIndic[trig.head];
  for(size_t i=0; i<tp.size(); i++){
    const Expr& index = tp[i];
    std::vector<Expr> temp;
    temp.push_back(index);
    enqueueInst(univ_id, temp, index);
    //	  TRACE("quant inst", "read write rule", univ.toString(), " | with bind: "+vectorExpr2string(temp));  
  }
}

void TheoryQuant::synNewInst(size_t univ_id, const vector<Expr>& bind, const Expr& gterm, const Trigger& trig ){
  if(trig.isMulti){
    const multTrigsInfo& mtriginfo = d_all_multTrigsInfo[trig.multiId];

    vector<Expr> actual_bind;
    for(size_t i=0, iend=bind.size(); i<iend; i++){
      if(null_expr != bind[i]){
	actual_bind.push_back(bind[i]);
      }
    }
    Expr actual_bind_expr = Expr(RAW_LIST, actual_bind);
    
    size_t index = trig.multiIndex;
    CDMap<Expr,bool> * cur_cd_map = mtriginfo.var_binds_found[index];
    CDMap<Expr,bool>::iterator cur_iter = cur_cd_map->find(actual_bind_expr);

    if (cur_cd_map->end() != cur_iter){
      return; 
    }
 
    (*cur_cd_map)[actual_bind_expr] = true;
    
    const vector<size_t>& comm_pos = mtriginfo.common_pos[0];
    size_t comm_pos_size = comm_pos.size();

    Expr comm_expr;
    vector<Expr> comm_expr_vec;
    for(size_t i = 0; i < comm_pos_size; i++){
      comm_expr_vec.push_back(bind[comm_pos[i]]);
      //      cout<<"bind " <<bind[comm_pos[i]]<<endl;
    }
    if(0 == comm_pos_size){
      comm_expr = null_expr;
    }
    else{
      comm_expr = Expr(RAW_LIST, comm_expr_vec);
    }
    Expr uncomm_expr;
    vector<Expr> uncomm_expr_vec;
    
    const vector<size_t>& uncomm_pos = mtriginfo.var_pos[index];
    size_t uncomm_pos_size = uncomm_pos.size();
    for(size_t i = 0; i< uncomm_pos_size; i++){
      uncomm_expr_vec.push_back(bind[uncomm_pos[i]]);
    }
    uncomm_expr = Expr(RAW_LIST, uncomm_expr_vec);
    
    CDList<Expr>* add_into_list ;
    CDList<Expr>* iter_list;
    ExprMap<CDList<Expr>* >::iterator add_into_iter;
    ExprMap<CDList<Expr>* >::iterator iter_iter;

    size_t other_index = 0;
    if(0 == index){
      other_index =1;
    }
    else if (1 == index){
      other_index = 0;
    }
    else{
      FatalAssert(false, "wrong ");
    }

    //    cout<<"comm expr"<<comm_expr<<endl;
    add_into_iter = mtriginfo.uncomm_list[index]->find(comm_expr);
    iter_iter = mtriginfo.uncomm_list[other_index]->find(comm_expr);
    
    if(mtriginfo.uncomm_list[index]->end() == add_into_iter){
      add_into_list = new (true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext());
      (*mtriginfo.uncomm_list[index])[comm_expr] = add_into_list;
    }
    else{
      add_into_list = add_into_iter->second;
    }
    //    cout<<"uncomm expr"<<uncomm_expr<<endl;
    add_into_list->push_back(uncomm_expr);

    if(mtriginfo.uncomm_list[other_index]->end() == iter_iter){
      return;
    }
    else{
      iter_list = iter_iter->second;
    }

    const vector<size_t>& uncomm_iter_pos = mtriginfo.var_pos[other_index];
    size_t uncomm_iter_pos_size = uncomm_iter_pos.size();
      
    for(size_t i =0, iend = iter_list->size(); i<iend; i++){
      const Expr& cur_iter_expr = (*iter_list)[i];
      vector<Expr> new_bind(bind);
      for(size_t j=0; j<uncomm_iter_pos_size; j++){
	new_bind[uncomm_iter_pos[j]] = cur_iter_expr[j];
      }
      enqueueInst(univ_id, new_bind, gterm);    
    }
    return;
  }
  //  cout<<"synnewinst "<<univ_id<<endl;
  {//code for trans2
    if(trig.hasT2){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(bind[i]);
	}
      }
      if(actual_bind.size() != 2){
	cout<<"2 != bind.size()" <<endl;
      }
      
      Expr acb1 = simplifyExpr(actual_bind[0]);
      Expr acb2 = simplifyExpr(actual_bind[1]);
      actual_bind[0]=acb1;
      actual_bind[1]=acb2;
      if(acb1 != acb2){
	Expr comb = Expr(RAW_LIST,acb1, acb2);
	if(!trans2Found(comb)){
	  setTrans2Found(comb);
	  Expr comb_rev = Expr(RAW_LIST,acb2, acb1);
	  if(trans2Found(comb_rev)){
	    enqueueInst(univ_id, actual_bind, gterm);
	  }
	}
      } 
    return;
    }
  }
  
  {//code for trans pred
    if(trig.hasTrans){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(simplifyExpr(bind[i]));
	}
      }
      if(simplifyExpr(actual_bind[0]) != simplifyExpr(actual_bind[1])){
	Expr comb = Expr(RAW_LIST,actual_bind[0], actual_bind[1]);
	    
	if(!transFound(comb)){
	  setTransFound(comb);
	  
	  Expr sr(actual_bind[0]);
	  Expr dt(actual_bind[1]);
	      
	  const CDList<Expr>& dtForw = forwList(dt);
	  const CDList<Expr>& srBack = backList(sr);
	  
	  for(size_t k=0; k<dtForw.size(); k++){
	    vector<Expr> tri_bind;
	    tri_bind.push_back(sr);
	    tri_bind.push_back(dt);
	    tri_bind.push_back(dtForw[k]);
	    
	    enqueueInst(univ_id, tri_bind, gterm);
	  }
	  
	  for(size_t k=0; k<srBack.size(); k++){
	    vector<Expr> tri_bind;
	    tri_bind.push_back(srBack[k]);
	    tri_bind.push_back(sr);
	    tri_bind.push_back(dt);
	    
	    enqueueInst(univ_id, tri_bind, gterm);
	    //	    TRACE("quant inst", "trans pred rule ", univ.toString(), " | with bind: "+vectorExpr2string(bind));
	    //	    TRACE("quant trans", "trans res back: ", vectorExpr2string(bind), "");
	  }
	  
	  pushForwList(sr,dt);
	  pushBackList(dt,sr);
	}
      } 
      return;
    }
  }
  //  cout<<"before enqueueisnt"<<endl;
  enqueueInst(univ_id, bind, gterm); 
  //      if(!d_allout || *d_useLazyInst){

}


/*

void TheoryQuant::synNewInst(size_t univ_id, const vector<Expr>& bind, const Expr& gterm, const Trigger& trig ){
  //  cout<<"synnewinst "<<univ_id<<endl;
  {//code for trans2
    if(trig.hasT2){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(bind[i]);
	}
      }
      if(actual_bind.size() != 2){
	cout<<"2 != bind.size()" <<endl;
      }
      if(simplifyExpr(actual_bind[0]) != simplifyExpr(actual_bind[1])){
	Expr comb = Expr(RAW_LIST,actual_bind[0], actual_bind[1]);
	if(!trans2Found(comb)){
	  setTrans2Found(comb);
	  Expr comb_rev = Expr(RAW_LIST,actual_bind[1], actual_bind[0]);
	  if(trans2Found(comb_rev)){
	    enqueueInst(univ_id, actual_bind, gterm);
	  }
	}
      } 
    return;
    }
  }
  
  {//code for trans pred
    if(trig.hasTrans){
      vector<Expr> actual_bind;
      for(size_t i=0; i<bind.size(); i++){
	if(bind[i] != null_expr){
	  actual_bind.push_back(bind[i]);
	}
      }
      if(simplifyExpr(actual_bind[0]) != simplifyExpr(actual_bind[1])){
	Expr comb = Expr(RAW_LIST,actual_bind[0], actual_bind[1]);
	    
	if(!transFound(comb)){
	  setTransFound(comb);
	  
	  Expr sr(actual_bind[0]);
	  Expr dt(actual_bind[1]);
	      
	  const CDList<Expr>& dtForw = forwList(dt);
	  const CDList<Expr>& srBack = backList(sr);
	  
	  for(size_t k=0; k<dtForw.size(); k++){
	    vector<Expr> tri_bind;
	    tri_bind.push_back(sr);
	    tri_bind.push_back(dt);
	    tri_bind.push_back(dtForw[k]);
	    
	    enqueueInst(univ_id, tri_bind, gterm);
	  }
	  
	  for(size_t k=0; k<srBack.size(); k++){
	    vector<Expr> tri_bind;
	    tri_bind.push_back(srBack[k]);
	    tri_bind.push_back(sr);
	    tri_bind.push_back(dt);
	    
	    enqueueInst(univ_id, tri_bind, gterm);
	    //	    TRACE("quant inst", "trans pred rule ", univ.toString(), " | with bind: "+vectorExpr2string(bind));
	    //	    TRACE("quant trans", "trans res back: ", vectorExpr2string(bind), "");
	  }
	  
	  pushForwList(sr,dt);
	  pushBackList(dt,sr);
	}
      } 
      return;
    }
  }
  //  cout<<"before enqueueisnt"<<endl;
  enqueueInst(univ_id, bind, gterm); 
      
  //      if(!d_allout || *d_useLazyInst){
  if(!d_allout){
    if(trig.hasRWOp ){
      
      if(1 == trig.bvs.size()){
	std::vector<Expr> tp = d_arrayIndic[trig.head];
	for(size_t i=0; i<tp.size(); i++){
	  std::vector<Expr> tp = d_arrayIndic[trig.head];
	  
	  Expr index = tp[i];
	  std::vector<Expr> temp;
	  temp.clear();
	  temp.push_back(index);
	  
	  enqueueInst(univ_id, temp, index);
	  //	  TRACE("quant inst", "read write rule", univ.toString(), " | with bind: "+vectorExpr2string(temp));  
	}
      }
      else{
      }
    }
  }
}
*/
/*
void TheoryQuant::synMultInst(const Theorem & univ, const CDList<Expr>& allterms, size_t tBegin ){

  const Expr& quantExpr = univ.getExpr();
  
  if(d_multTriggers[quantExpr].size() <= 0) return ;

  TRACE("quant inst", "try muli with:|", quantExpr.toString() , " ");
  const std::vector<Expr>& bVarsThm = quantExpr.getVars();

  std::vector<std::vector<Expr> > instSetThm; //set of instantiations for the thm
  std::vector<std::vector<Expr> > termInst; //terminst are bindings, in the order of bVarsTrig
  std::vector<Expr> bVarsTrig; 


  if(hasGoodSynMultiInst(quantExpr, bVarsTrig, termInst, allterms, tBegin)) {
    genInstSetThm(bVarsThm, bVarsTrig, termInst, instSetThm);
  }  
  {
    for(std::vector<std::vector<Expr> >::iterator i=instSetThm.begin(), iend=instSetThm.end(); i!=iend; ++i) {
      enqueueInst(univ, *i, null_expr);//fix the null_expr here asap
      TRACE("quant inst", "insert mult inst", univ.toString(), " | with bind: "+vectorExpr2string(*i));  
    }
  }
  
}
*/
/*
void TheoryQuant::synPartInst(const Theorem & univ, const CDList<Expr>& allterms,  size_t tBegin ){
  
  const Expr& quantExpr = univ.getExpr();
  TRACE("quant inst", "try part with ", quantExpr.toString() , " ");
  
  const std::vector<Trigger>& triggers = d_partTrigs[quantExpr];

  std::vector<std::vector<Expr> > instSetThm; //set of instantiations for the thm
  std::vector<std::vector<Expr> > termInst; //terminst are bindings, in the order of bVarsTrig
  std::vector<Expr> bVarsTrig; 
  std::vector<Expr> instGterms;

  for( std::vector<Trigger>::const_iterator i= triggers.begin(), iend=triggers.end();i!=iend;++i)  {
  
    Trigger trig = *i;
    TRACE("quant inst","handle part trigger", trig.getEx().toString(),"");
    termInst.clear();
    bVarsTrig.clear();
    instSetThm.clear();
    //    if(hasGoodSynInstNewTrig(trig, bVarsTrig, termInst, instGterms,allterms, tBegin)) {
    if(hasGoodSynInstNewTrig(trig, trig.getBVs(), termInst, instGterms,allterms, tBegin)) {
      TRACE("quant syninst", "has good ", termInst.size(),"");
      TRACE("quant syninst", "after good ",instSetThm.size(), "");

      Theorem newUniv = d_rules->adjustVarUniv(univ, trig.getBVs());
      
      TRACE("quant syninst", " new univ:" ,newUniv.toString(),"");
      {
	for(size_t i = 0; i< termInst.size(); i++){
	  const std::vector<Expr>& binds = termInst[i];
	  const Expr& gterm = instGterms[i];
	  enqueueInst(newUniv, binds, gterm);
	  TRACE("quant yeting inst", "instantiating =========", "" , "");  
	  TRACE("quant yeting inst", "instantiating", newUniv.getExpr().toString(), " | with bind: "+vectorExpr2string(binds));  
	  TRACE("quant yeting inst", "instantiating org ", univ.getExpr().toString(), " | with gterm "+gterm.toString());  
	}
      }
    }
  }
}

*/
void TheoryQuant::semInst(const Theorem & univ, size_t tBegin){
}

void TheoryQuant::checkSat(bool fullEffort){
  if(*d_translate) return;
  if(d_rawUnivs.size() <=0 ) return;

  DebugAssert(d_univsQueue.size() == 0, "something left in d_univsQueue");
  DebugAssert(d_simplifiedThmQueue.size() == 0, "something left in d_univsQueue");

#ifdef DEBUG  
  if(fullEffort){
    if( CVC3::debugger.trace("quant assertfact")  ){
      cout<<"===========all cached univs =========="<<endl;
      //      for (ExprMap<Theorem>::iterator i=d_simpUnivs.begin(), iend=d_simpUnivs.end(); i!=iend;  i++){
      //	cout<<"------------------------------------"<<endl;
      //	cout<<(i->first).toString()<<endl;
      //	cout<<"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"<<endl;
      //	cout<<(i->second).getExpr().toString()<<endl;
      //}
    }
    if( CVC3::debugger.trace("quant samehead")  ){
      cout<<"===========all cached  =========="<<endl;
      for (ExprMap< CDList<Expr>*>::iterator i=d_same_head_expr.begin(), iend=d_same_head_expr.end(); i!=iend;  i++){
	cout<<"------------------------------------"<<endl;	
	cout<<(i->first)<<endl;
	cout<<"_______________________"<<endl;
	CDList<Expr> * terms= i->second;
	for(size_t i =0; i<terms->size(); i++){
	  cout<<(*terms)[i]<<endl;
	}
      }
    }
  }  
#endif

#ifdef DEBUG  
  if( CVC3::debugger.trace("quant checksat")  ){
    const CDList<Expr>& allpreds = theoryCore()->getPredicates();
    cout<<"=========== cur pred & terms =========="<<endl;
    
    for (size_t i=d_lastPredsPos; i<allpreds.size(); i++){
      cout<<"i="<<allpreds[i].getIndex()<<" :"<<findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
    }
    
    const CDList<Expr>&  allterms = theoryCore()->getTerms();
    
    for (size_t i=d_lastTermsPos; i<allterms.size(); i++){
      cout<<"i="<<allterms[i].getIndex()<<" :"<<findExpr(allterms[i])<<"|"<<allterms[i]<<endl;
    }
    cout<<"=========== cur quant =========="<<endl;
    for (size_t i=0; i<d_univs.size(); i++){
      cout<<"i="<<d_univs[i].getExpr().getIndex()<<" :"<<findExpr(d_univs[i].getExpr())<<"|"<<d_univs[i]<<endl;
    }
  }
  

  if( CVC3::debugger.trace("quant checksat equ") ){
    const CDList<Expr>& allpreds = theoryCore()->getPredicates();
    cout<<"=========== cur pred equ =========="<<endl;
    
    for (size_t i=d_lastPredsPos; i<allpreds.size(); i++){
      if(allpreds[i].isEq()){
	cout<<"i="<<allpreds[i].getIndex()<<" :"<<findExpr(allpreds[i])<<"|"<<allpreds[i]<<endl;
      }
    }
    cout<<"=========== cur pred equ end  =========="<<endl;
  }
  
#endif
  
  if((*d_useLazyInst && !fullEffort) ) return;

  {//for the same head list
   const CDList<Expr>&  allterms = theoryCore()->getTerms();
   for(size_t i=d_lastTermsPos; i<allterms.size(); i++){
     Expr t = allterms[i];
     if(canGetHead(t)){
       if(d_same_head_expr.count(getHead(t)) >0){
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
       else{
	 d_same_head_expr[getHead(t)]= 
	   new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
     }
   }

   const CDList<Expr>&  allpreds = theoryCore()->getPredicates();
   for(size_t i=d_lastPredsPos; i<allpreds.size(); i++){
     Expr t = allpreds[i];
     if(canGetHead(t)){
       if(d_same_head_expr.count(getHead(t)) >0){
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
       else{
	 d_same_head_expr[getHead(t)]= 
	   new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	 d_same_head_expr[getHead(t)]->push_back(t);
       }
     }
   }
  }
    
  {//for the equalities list
    const CDList<Expr>&  allpreds = theoryCore()->getPredicates();
    for(size_t i=d_lastPredsPos; i<allpreds.size(); i++){
      const Expr& t = allpreds[i];
      if(t.isEq()){
	//	cout<<"EQ: "<<t<<endl;
	const Expr lterm = t[0];
	const Expr rterm = t[1];
	d_eqs.push_back(lterm);
	d_eqs.push_back(rterm);
		
	/*	 
	ExprMap<CDList<Expr>* >::iterator iter = d_eq_list.find(lterm);
	if(d_eq_list.end() == iter){
	  d_eq_list[lterm] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	  d_eq_list[lterm]->push_back(rterm);
	}
	else{
	  iter->second->push_back(rterm);
	}

	//	cout<<"LTERM: " <<rterm<<endl;
	iter = d_eq_list.find(rterm);
	if(d_eq_list.end() == iter){
	  d_eq_list[rterm] = new(true) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	  d_eq_list[rterm]->push_back(lterm);
	}
	else{
	  iter->second->push_back(lterm);
	}
	//	cout<<"RTERM: " <<lterm<<endl;
	*/
      }
    }
  }
  

  {//for rw heuristic
   const CDList<Expr>&  allterms = theoryCore()->getTerms();
   for(size_t i=d_lastTermsPos; i<allterms.size(); i++){
     const Expr& cur=allterms[i];
     if(READ == cur.getKind() || WRITE == cur.getKind()){
       arrayIndexName(cur);
     }
   }
  }
 
  d_instThisRound = 0;
  d_useMultTrig=*d_useMult;
  d_usePartTrig=*d_usePart;
  d_useFullTrig=true;

  if(fullEffort) {
    d_inEnd=true;
  }
  else{
    d_inEnd=false;
  }


  ExprMap<ExprMap<vector<dynTrig>* >* > new_trigs;
  for(size_t i=d_univs.size(); i<d_rawUnivs.size(); i++){
    setupTriggers(new_trigs, d_rawUnivs[i], i);
  }

  try {
    if (!(*d_useNew)){
      naiveCheckSat(fullEffort);
    }
    else if (*d_useSemMatch){
      semCheckSat(fullEffort);
    }
    else {
      synCheckSat(new_trigs, fullEffort);
    }
  }
  
  catch (int x){

     while(!d_simplifiedThmQueue.empty()){
       d_simplifiedThmQueue.pop();
     }
    d_tempBinds.clear();
    saveContext();
    delNewTrigs(new_trigs);
    return;
  }
  
  sendInstNew();   

  saveContext();

  try{
    if((*d_useNew) && (0 == d_instThisRound) && fullEffort && theoryCore()->getTerms().size()< (size_t)(*d_maxNaiveCall) ) {
      //    cout<<"naive called"<<endl;
      if (0== theoryCore()->getTerms().size()){
	static int counter =0;

	std::set<Expr> types;
	for(size_t i = 0; i<d_univs.size(); i++){
	  const Expr& cur_quant = d_univs[i].getExpr();
	  const std::vector<Expr> cur_vars = cur_quant.getVars();
	  for(size_t j =0; j<cur_vars.size(); j++){
	    types.insert(cur_vars[j].getType().getExpr());
	  }
	}
      
	std::string base("_naiveInst");
	for(std::set<Expr>::iterator i=types.begin(), iend = types.end(); i != iend; i++){
	  counter++;
	  std::stringstream tempout;
	  tempout << counter;
	  std::string out_str = base + tempout.str();
	  Expr newExpr = theoryCore()->getEM()->newVarExpr(out_str);

	  newExpr.setType(Type(*i));
	  
	  Proof pf;
	  
	  Expr newExpr2 = theoryCore()->getEM()->newVarExpr(out_str+"extra");
	  newExpr2.setType(Type(*i));
	  
	  Expr newConstThm;

	  if(Type(*i) == theoryCore()->getEM()->newRatExpr(0).getType()){
	    //somehow theory_arith will complain if we use expr2 to form the eq here
	    newConstThm = newExpr.eqExpr(theoryCore()->getEM()->newRatExpr(0));
	  }
	  else{
	    newConstThm = newExpr.eqExpr(newExpr2);
	  }
	  Theorem newThm  = d_rules->addNewConst(newConstThm);
	  
	  enqueueFact(newThm);
	  d_tempBinds.clear();
	  return;
	}
	
      }
    naiveCheckSat(fullEffort);
    }
  }//end of try
  
  catch (int x){
    //    d_simplifiedThmQueue.clear();
     while(!d_simplifiedThmQueue.empty()){
       d_simplifiedThmQueue.pop();
     }
    d_tempBinds.clear();
    saveContext();
    delNewTrigs(new_trigs);
    return;
  }
  
  if(fullEffort) {
    sendInstNew();
  }

  combineOldNewTrigs(new_trigs);
  delNewTrigs(new_trigs);
}

void TheoryQuant::saveContext(){
  d_lastArrayPos.set(d_arrayTrigs.size());
  d_univsSavedPos.set(d_univs.size());
  d_rawUnivsSavedPos.set(d_rawUnivs.size());
  d_lastTermsPos.set(theoryCore()->getTerms().size());
  d_lastPredsPos.set(theoryCore()->getPredicates().size());
  d_lastUsefulGtermsPos.set(d_usefulGterms.size());
}

/*void TheoryQuant::synCheckSat(bool fullEffort){
}
*/
void TheoryQuant::synCheckSat(ExprMap<ExprMap<vector<dynTrig>* >* >&  new_trigs, bool fullEffort){
  
  d_allout=false;

  if(fullEffort)   {
    setIncomplete("Quantifier instantiation");
  }

  size_t uSize = d_univs.size() ;
  const CDList<Expr>& allterms = theoryCore()->getTerms();
  const CDList<Expr>& allpreds = theoryCore()->getPredicates();
  size_t tSize = allterms.size();
  size_t pSize = allpreds.size();

  TRACE("quant",uSize, " uSize and univsSavedPOS ", d_univsSavedPos);
  TRACE("quant",tSize, " tSize and termsLastPos ", d_lastTermsPos);
  TRACE("quant",pSize, " pSize and predsLastPos ", d_lastPredsPos);
  TRACE("quant", fullEffort, " fulleffort:scope ",theoryCore()->getCM()->scopeLevel() );
    
  for(size_t i=d_lastTermsPos; i<tSize; i++){
    const Expr& cur(allterms[i]);
    if(usefulInMatch(cur)){
      if(*d_useExprScore){
	int score = getExprScore(cur);
	if(score <= d_curMaxExprScore && 0 <= score ){
	  d_usefulGterms.push_back(cur);
	  add_parent(cur);
	} 
      }
      else{
	d_usefulGterms.push_back(cur);
	add_parent(cur);
      }
    }
    else{
    }
  }

  for(size_t i=d_lastPredsPos; i<pSize; i++){
    const Expr& cur=allpreds[i];
    if( usefulInMatch(cur)){
      if(*d_useExprScore ){
	int score = getExprScore(cur);
	if(score <= d_curMaxExprScore && 0 <= score){
	  d_usefulGterms.push_back(cur);
	  add_parent(cur);
	} 
      }
      else{
	d_usefulGterms.push_back(cur);
	add_parent(cur);
      }
    }
    else{
    }
  }
  

  if(d_useFullTrig && d_inEnd && *d_useInstEnd ){

    if(*d_useExprScore){

      matchListOld(d_usefulGterms, d_lastUsefulGtermsPos, d_usefulGterms.size() ); //new terms to old list
      matchListNew(new_trigs, d_usefulGterms, 0, d_usefulGterms.size()); //new and old terms to new list
      
      if(sendInstNew() > 0){
	TRACE("inend", "debug 1", "" ,"" );
	return;
      } 
      
      d_allout = true;
      {
 	CDList<Expr>* changed_terms = new (false) CDList<Expr> (theoryCore()->getCM()->getCurrentContext()) ;
	collectChangedTerms(*changed_terms);
	
	matchListOld(*changed_terms, 0, changed_terms->size());
	matchListNew(new_trigs, *changed_terms, 0 , changed_terms->size());
	delete changed_terms;
      }

      int n;
      if( ( n = sendInstNew()) > 0){
 	TRACE("inend",  "debug 2", " # ",n );
 	return;
      }
      d_allout = false;      


      int numNewTerm=0;
      int oldNum=d_usefulGterms.size();

      for(size_t i=0; i<tSize; i++){
	const Expr& cur(allterms[i]);
	if(!(usefulInMatch(cur))) continue;
	int score = getExprScore(cur);
	if( score > d_curMaxExprScore){
	  if((d_curMaxExprScore + 1) == score){
	    d_usefulGterms.push_back(cur);
	    add_parent(cur);
	    numNewTerm++;
	  }
	  else{
	    TRACE("inend", "is this good? ", cur.toString()+" #-# " , score);
	    d_usefulGterms.push_back(cur);
	    add_parent(cur);
	    numNewTerm++;
	  }
	}
      }

      for(size_t i=0; i<pSize; i++){
	const Expr& cur(allpreds[i]);
	if(!(usefulInMatch(cur))) continue;
	int score = getExprScore(cur);
	if( score > d_curMaxExprScore){
	  if((d_curMaxExprScore + 1) == score){
	    d_usefulGterms.push_back(cur);
	    add_parent(cur);
	    numNewTerm++;
	  }
	  else{
	    TRACE("inend", "is this good? ", cur.toString()+" #-# " , score);
	    d_usefulGterms.push_back(cur);
	    add_parent(cur);
	    numNewTerm++;
	  }
	}
      }

      if(numNewTerm >0 ){

	if(d_curMaxExprScore >=0 ){

	  d_curMaxExprScore =  d_curMaxExprScore+1;;
	}
	else {
	  d_curMaxExprScore =  d_curMaxExprScore+1;
	}
	
	matchListOld(d_usefulGterms, oldNum, d_usefulGterms.size() );
	matchListNew(new_trigs, d_usefulGterms, oldNum, d_usefulGterms.size());
	
	if(sendInstNew() > 0){
	  TRACE("inend",  "debug 3", "" , "" );
	  return;
	}
      }
      for(size_t array_index = 0; array_index < d_arrayTrigs.size(); array_index++){
	arrayHeuristic(d_arrayTrigs[array_index].trig, d_arrayTrigs[array_index].univ_id); 
      }
      
      return ;
    }
    
    TRACE("inend", "debug 3 0", "", "");
    TRACE("quant","this round; ",d_callThisRound,"");

    return;
  }
        

  if ((uSize == d_univsSavedPos) && 
      (tSize == d_lastTermsPos) && 
      (pSize == d_lastPredsPos) ) return;
  

  matchListOld(d_usefulGterms, d_lastUsefulGtermsPos,d_usefulGterms.size() ); //new terms to old list
  
  matchListNew(new_trigs, d_usefulGterms, 0, d_usefulGterms.size() ); //new and old terms to new list

  for(size_t array_index = d_lastArrayPos; array_index < d_arrayTrigs.size(); array_index++){
    arrayHeuristic(d_arrayTrigs[array_index].trig, d_arrayTrigs[array_index].univ_id); 
  }

  TRACE("quant","this round; ",d_callThisRound,"");
  
  return;
}


void TheoryQuant::semCheckSat(bool fullEffort){
}

//the following is old code and I did not modify much, Yeting
void TheoryQuant::naiveCheckSat(bool fullEffort){
  TRACE("quant", "checkSat ", fullEffort, "{");
  IF_DEBUG(int instCount = d_instCount);
  size_t uSize = d_univs.size(), stSize = d_savedTerms.size();
  if(true || (fullEffort && uSize > 0)) {
    // First of all, this algorithm is incomplete
    setIncomplete("Quantifier instantiation");
    
    if(d_instCount>=*d_maxQuantInst)
      return;
    //first attempt to instantiate with the saved terms
    //only do this if there are new saved terms or new theroems and 
    // at least some saved terms
    bool savedOnly = ((uSize > d_univsSavedPos.get()  && stSize > 0) ||
		      (stSize > d_savedTermsPos.get()));
    int origCount = d_instCount;
    if(savedOnly)
      {
	TRACE("quant", "checkSat [saved insts]: univs size = ", uSize , " ");
	for(size_t i=0, pos = d_univsSavedPos.get(); i<uSize; i++) {
	  if(d_instCount>= *d_maxQuantInst)
	    break;
	  else
	    instantiate(d_univs[i], i>=pos, true,  d_savedTermsPos.get());
	}
	d_univsSavedPos.set(d_univs.size());
	d_savedTermsPos.set(stSize);
      }
    if(!savedOnly || d_instCount == origCount)
      { //instantiate with context dependent assertions terms
	TRACE("quant", "checkSat [context insts]: univs size = ", uSize , " ");
	const CDList<Expr>& assertions = theoryCore()->getTerms();
	int origSize = d_contextTerms.size();
// 	for(size_t i=0; i<uSize; i++)
// 	  assertions.push_back(d_univs[i].getExpr());
	//build the map of all terms grouped into vectors by types
	TRACE("quant", "checkSat terms size = ", assertions.size() , " ");
	mapTermsByType(assertions);
	for(size_t i=0, pos = d_univsContextPos.get(); i<uSize; i++) {
	  if(d_instCount>= *d_maxQuantInst)
	    break;
	  else
	    instantiate(d_univs[i], i>=pos, false, origSize);
	}
	d_univsContextPos.set(d_univs.size());
      }
    TRACE("quant terse", "checkSat total insts: ",
	  d_instCount, ", new "+int2string(d_instCount - instCount));
  }
  TRACE("quant", "checkSat total insts: ", d_instCount, " ");
  TRACE("quant", "checkSat new insts: ", d_instCount - instCount, " ");
  TRACE("quant", "checkSat effort:",  fullEffort, " }");

}


/*! \brief Queues up all possible instantiations of bound
 * variables.
 *
 * The savedMap boolean indicates whether to use savedMap or
 * d_contextMap the all boolean indicates weather to use all
 * instantiation or only new ones and newIndex is the index where
 * new instantiations begin.
 */
void TheoryQuant::instantiate(Theorem univ, bool all, bool savedMap, 
			      size_t newIndex)
{
  
  if(!all && ((savedMap &&  newIndex == d_savedTerms.size())
	      ||(!savedMap && newIndex == d_contextTerms.size())))
    return;

  TRACE("quant", "instanitate", all , "{");
  std::vector<Expr> varReplacements;
  recInstantiate(univ, all, savedMap, newIndex, varReplacements);
  TRACE("quant", "instanitate", "", "}");
  
}

 //! does most of the work of the instantiate function.
void TheoryQuant::recInstantiate(Theorem& univ, bool all, bool savedMap,
				 size_t newIndex, 
				 std::vector<Expr>& varReplacements)
{
  Expr quantExpr = univ.getExpr();
  const vector<Expr>& boundVars = quantExpr.getVars();
  
  size_t curPos = varReplacements.size(); 
  TRACE("quant", "recInstantiate: ", boundVars.size() - curPos, "");
  //base case: a full vector of instantiations exists
  if(curPos == boundVars.size()) {
    if(!all)
      return;
    Theorem t = d_rules->universalInst(univ, varReplacements);
    d_insts[t.getExpr()] = varReplacements;
    TRACE("quant", "recInstantiate => " , t.toString(), "");
    if(d_instCount< *d_maxQuantInst) {
      d_instCount=d_instCount+1;
      enqueueInst(univ, varReplacements, null_expr);
      //            enqueueInst(univ, t);
	    // enqueueFact(t);
    }
    return;
  }
  //recursively add all possible instantiations in the next 
  //available space of the vector
  else {
    Type t = getBaseType(boundVars[curPos]);
    int iendC=0, iendS=0, iend;
    std::vector<size_t>* typeVec = NULL; // = d_savedMap[t];
    CDList<size_t>* typeList = NULL; // = *d_contextMap[t];
    if(d_savedMap.count(t) > 0) {
      typeVec = &(d_savedMap[t]);
      iendS = typeVec->size();
      TRACE("quant", "adding from savedMap: ", iendS, "");
    }
    if(!savedMap) {
      if(d_contextMap.count(t) > 0) {
	typeList = d_contextMap[t];
	iendC = typeList->size();
	TRACE("quant", "adding from contextMap:", iendC , "");
      }
    }
    iend = iendC + iendS;
    for(int i =0; i<iend; i++) {
      TRACE("quant", "I must have gotten here!", "", "");
      size_t index;
      if(i<iendS){
	index = (*typeVec)[i];
	varReplacements.push_back(d_savedTerms[index]);
      }
      else {
	index = (*typeList)[i-iendS];
	varReplacements.push_back(d_contextTerms[index]);
      }
      if((index <  newIndex) || (!savedMap && i<iendS))
	recInstantiate(univ, all, savedMap, newIndex,  varReplacements);
      else
	recInstantiate(univ, true, savedMap, newIndex,  varReplacements);
      varReplacements.pop_back();   
    }


  }
}

/*! \brief categorizes all the terms contained in a vector of  expressions by
 * type.
 *
 * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
 */
void TheoryQuant::mapTermsByType(const CDList<Expr>& terms)
{
  Expr trExpr=trueExpr(), flsExpr = falseExpr();
  Type boolT = boolType();
  if(d_contextMap.count(boolT) == 0)
    {
      d_contextMap[boolT] =
        new(true) CDList<size_t>(theoryCore()->getCM()->getCurrentContext());
      size_t pos = d_contextTerms.size();
      d_contextTerms.push_back(trExpr);
      d_contextTerms.push_back(flsExpr);
      (*d_contextMap[boolT]).push_back(pos);
      (*d_contextMap[boolT]).push_back(pos+1);
    }
  for(size_t i=0; i<terms.size(); i++)
    recursiveMap(terms[i]);
  // Add all our saved universals to the pool
  for(size_t i=0; i<d_univs.size(); i++)
    recursiveMap(d_univs[i].getExpr());
}

/*! \brief categorizes all the terms contained in an expressions by
 * type. 
 *
 * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
 * returns true if the expression does not contain bound variables, false
 * otherwise.
 */
bool TheoryQuant::recursiveMap(const Expr& e)
{
  if(d_contextCache.count(e)>0) {
    return(d_contextCache[e]);
  }
  if(e.arity()>0)  {
    for(Expr::iterator it = e.begin(), iend = e.end(); it!=iend; ++it)
      //maps the children and returns a bool
      if(recursiveMap(*it) == false) {
	d_contextCache[e] = false;
      }
  }
  else if(e.getKind() == EXISTS || e.getKind() == FORALL){
    //maps the body
    if(recursiveMap(e.getBody())==false) {
      d_contextCache[e]=false;
    }
  }
  //found a bound variable in the children
  if(d_contextCache.count(e)>0) {
    return false;
  }
  
  if(d_savedCache.count(e) > 0) {
    return true;
  }
  
  Type type = getBaseType(e);
  
  if(!type.isBool() && !(e.getKind()==BOUND_VAR)){
     TRACE("quant", "recursiveMap: found ", 
	   e.toString() + " of type " + type.toString(), "");
    int pos = d_contextTerms.size();
    d_contextTerms.push_back(e);
    if(d_contextMap.count(type)==0)
      d_contextMap[type] =
        new(true) CDList<size_t>(theoryCore()->getCM()->getCurrentContext());
    (*d_contextMap[type]).push_back(pos);
  }

  if(e.getKind() == BOUND_VAR) {
    d_contextCache[e] = false;
    return false;
  }
  else {
    d_contextCache[e] = true;
    return true;
  }
  //need  to implement: 
  //insert all instantiations if type is finite and reasonable
  //also need to implement instantiations of subtypes
}

/*!\brief Used to notify the quantifier algorithm of possible 
 * instantiations that were used in proving a context inconsistent.
 */
void TheoryQuant::notifyInconsistent(const Theorem& thm){
#ifdef DEBUG

  if( CVC3::debugger.trace("quant inscon")  ){

    cout<<"the one caused incsonsistency"<<endl;
    cout<<thm.getAssumptionsRef().toString()<<endl;
    std::vector<Expr> assump;
    thm.getLeafAssumptions(assump);

    cout<<"===========leaf assumptions; =========="<<endl;
    for(std::vector<Expr>::iterator i=assump.begin(), iend=assump.end(); i!=iend; i++){
      cout<<">>"<<i->toString()<<endl;
    }
  }
#endif

  if(d_univs.size() == 0)
    return;
  DebugAssert(thm.getExpr().isFalse(), "notifyInconsistent called with"
	" theorem: " + thm.toString() + " which is not a derivation of false");
  TRACE("quant", "notifyInconsistent: { " , thm.toString(), "}");
  //  thm.clearAllFlags();
  //  findInstAssumptions(thm);
  TRACE("quant terse", "notifyInconsistent: savedTerms size = ",
	d_savedTerms.size(), "");
  TRACE("quant terse", "last term: ", 
	d_savedTerms.size()? d_savedTerms.back() : Expr(), "");
}
/*! \brief A recursive function used to find instantiated universals
 * in the hierarchy of assumptions.
 */
void TheoryQuant::findInstAssumptions(const Theorem& thm)
{
  if(thm.isNull() || thm.isRefl() || thm.isFlagged())
    return;
  thm.setFlag();
  const Expr& e = thm.getExpr();
  if(d_insts.count(e) > 0) {
    vector<Expr>& insts = d_insts[e];
    int pos;
    for(vector<Expr>::iterator it = insts.begin(), iend = insts.end(); it!=iend
	  ; ++it)
      {
	if(d_savedCache.count(*it) ==  0) {
	  TRACE("quant", "notifyInconsistent: found:", (*it).toString(), "");
	  d_savedCache[*it] = true;
	  pos = d_savedTerms.size();
	  d_savedTerms.push_back(*it);
	  d_savedMap[getBaseType(*it)].push_back(pos);
	}
      }
  }
  if(thm.isAssump())
    return;
  const Assumptions& a = thm.getAssumptionsRef();
  for(Assumptions::iterator it =a.begin(), iend = a.end(); it!=iend; ++it){
    findInstAssumptions(*it);
  }
}

//! computes the type of a quantified term. Always a  boolean.
void TheoryQuant::computeType(const Expr& e)
{
  switch (e.getKind()) {
  case FORALL:
  case EXISTS: {
    if(!e.getBody().getType().isBool())
      throw TypecheckException("Type mismatch for expression:\n\n   "
			      + e.getBody().toString()
			      + "\n\nhas the following type:\n\n  "
			      + e.getBody().getType().toString()
			      + "\n\nbut the expected type is Boolean:\n\n  ");
    else
      
      e.setType(e.getBody().getType());
    break;
  }
  default:
    DebugAssert(false,"Unexpected kind in Quantifier Theory: " 
		+ e.toString());
    break;
  }
}

/*!
 * TCC(forall x.phi(x)) = (forall x. TCC(phi(x)))
 *                         OR (exists x. TCC(phi(x)) & !phi(x))
 * TCC(exists x.phi(x)) = (forall x. TCC(phi(x)))
 *                         OR (exists x. TCC(phi(x)) & phi(x))
 */


Expr TheoryQuant::computeTCC(const Expr& e) {
  DebugAssert(e.isQuantifier(), "Unexpected expression in Quantifier Theory: " 
	      + e.toString());

  bool forall(e.getKind() == FORALL);
  const Expr& phi = e.getBody();
  Expr tcc_phi = getTCC(phi);
  Expr forall_tcc = getEM()->newClosureExpr(FORALL, e.getVars(), tcc_phi);
  Expr exists_tcc = getEM()->newClosureExpr(EXISTS, e.getVars(),
                                            tcc_phi && (forall? !phi : phi));
  return (forall_tcc || exists_tcc);  
}


ExprStream&
TheoryQuant::print(ExprStream& os, const Expr& e) {
  switch(os.lang()) {
  case SIMPLIFY_LANG:
    {
      switch(e.getKind()){
      case FORALL:
      case EXISTS: {
	if(!e.isQuantifier()) {
	  e.print(os);
	  break;
	}
	os << "(" << ((e.getKind() == FORALL)? "FORALL" : "EXISTS");
	const vector<Expr>& vars = e.getVars();
	bool first(true);
	os << "(" ;
	for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	    i!=iend; ++i) {
	  if(first) first = false;
	  else os << " " ;
	  os << *i;
	  // The quantifier may be in a raw parsed form, in which case
	  // the type is not assigned yet
	  //if(i->isVar())  // simplify do not need type
	  //  os << ":" << space << pushdag << (*i).getType() << popdag;
	}
	os << ") "  << e.getBody() <<  ")";
      }
	break;
      default:
	e.print(os);
	break;
      }
      break;
    }

  case PRESENTATION_LANG: {
    switch(e.getKind()){
    case FORALL:
    case EXISTS: {
      if(!e.isQuantifier()) {
	e.print(os);
	break;
      }
      os << "(" << push << ((e.getKind() == FORALL)? "FORALL" : "EXISTS")
	 << space << push;
      const vector<Expr>& vars = e.getVars();
      bool first(true);
      os << "(" << push;
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	  i!=iend; ++i) {
	if(first) first = false;
	else os << push << "," << pop << space;
	os << *i;
	// The quantifier may be in a raw parsed form, in which case
	// the type is not assigned yet
	// the following lines are changed for a neat output / by yeting
	if(*d_translate || true){
	  if(i->isVar())
	    os << ":" << space << pushdag << (*i).getType() << popdag;
	}
      }
      os << push << "): " << pushdag << push
	 << e.getBody() << push << ")";
    }
      break;
    default:
      e.print(os);
      break;
    }
    break;
  }
  case SMTLIB_LANG: {
    d_theoryUsed = true;
    switch(e.getKind()){
      case FORALL:
      case EXISTS: {
        if(!e.isQuantifier()) {
          e.print(os);
          break;
        }
        os << "(" << push << ((e.getKind() == FORALL)? "forall" : "exists")
           << space;
        const vector<Expr>& vars = e.getVars();
        bool first(true);
        //      os << "(" << push;
        for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
            i!=iend; ++i) {
          if(first) first = false;
          else os << space;
          os << "(" << push << *i;
          // The quantifier may be in a raw parsed form, in which case
          // the type is not assigned yet
          if(i->isVar())
            os << space << pushdag << (*i).getType() << popdag;
          os << push << ")" << pop << pop;
        }
        os << space << pushdag
           << e.getBody() << push << ")";
        break;
      }
      default:
        throw SmtlibException("TheoryQuant::print: SMTLIB_LANG: Unexpected expression: "
                              +getEM()->getKindName(e.getKind()));
        break;
    }
    break;
  } // End of SMTLIB_LANG
  case LISP_LANG: {
    switch(e.getKind()){
    case FORALL:
    case EXISTS: {
      if(!e.isQuantifier()) {
	e.print(os);
	break;
      }
      os << "(" << push << ((e.getKind() == FORALL)? "FORALL" : "EXISTS")
	 << space;
      const vector<Expr>& vars = e.getVars();
      bool first(true);
      os << "(" << push;
      for(vector<Expr>::const_iterator i=vars.begin(), iend=vars.end();
	  i!=iend; ++i) {
	if(first) first = false;
	else os << space;
	os << "(" << push << *i;
	// The quantifier may be in a raw parsed form, in which case
	// the type is not assigned yet
	if(i->isVar())
	  os << space << pushdag << (*i).getType() << popdag;
	os << push << ")" << pop << pop;
      }
      os << push << ")" << pop << pop << pushdag
	 << e.getBody() << push << ")";
    }
      break;
    default:
      e.print(os);
      break;
    }
    break;
  }
  default:
    e.print(os);
    break;
  }
  return os;
}

///////////////////////////////////////////////////////////////////////////////
//parseExprOp:
//translating special Exprs to regular EXPR??
///////////////////////////////////////////////////////////////////////////////
Expr
TheoryQuant::parseExprOp(const Expr& e) {
  TRACE("parser", "TheoryQuant::parseExprOp(", e, ")");
  // If the expression is not a list, it must have been already
  // parsed, so just return it as is.
  if(RAW_LIST != e.getKind()) return e;

  DebugAssert(e.arity() > 0,
	      "TheoryQuant::parseExprOp:\n e = "+e.toString());
  
  const Expr& c1 = e[0][0];
  const string& opName(c1.getString());
  int kind = getEM()->getKind(opName);
  switch(kind) {
  case FORALL:
  case EXISTS: { // (OP ((v1 ... vn tp1) ...) body)
    if(!(e.arity() == 3 && e[1].getKind() == RAW_LIST && e[1].arity() > 0))
      throw ParserException("Bad "+opName+" expression: "+e.toString());
    // Iterate through the groups of bound variables
    vector<pair<string,Type> > vars; // temporary stack of bound variables
    for(Expr::iterator i=e[1].begin(), iend=e[1].end(); i!=iend; ++i) {
      if(i->getKind() != RAW_LIST || i->arity() < 2)
	throw ParserException("Bad variable declaration block in "+opName
			    +" expression: "+i->toString()
			    +"\n e = "+e.toString());
      // Iterate through individual bound vars in the group.  The
      // last element is the type, which we have to rebuild and
      // parse, since it is used in the creation of bound variables.
      Type tp(parseExpr((*i)[i->arity()-1]));
      if (tp == boolType()) {
        throw ParserException("A quantified variable may not be of type BOOLEAN");
      }
      for(int j=0, jend=i->arity()-1; j<jend; ++j) {
	if((*i)[j].getKind() != ID)
	  throw ParserException("Bad variable declaration in "+opName+""
			      " expression: "+(*i)[j].toString()+
			      "\n e = "+e.toString());
	vars.push_back(pair<string,Type>((*i)[j][0].getString(), tp));
      }
    }
    // Create all the bound vars and save them in a vector
    vector<Expr> boundVars;
    for(vector<pair<string,Type> >::iterator i=vars.begin(), iend=vars.end();
	i!=iend; ++i)
      boundVars.push_back(addBoundVar(i->first, i->second));
    // Rebuild the body
    Expr body(parseExpr(e[2]));
    // Build the resulting Expr as (OP (vars) body)
    Expr res = getEM()->newClosureExpr((kind == FORALL) ? FORALL : EXISTS,
                                       boundVars, body);
    return res;
    break;
  }
  default:
    DebugAssert(false,
		"TheoryQuant::parseExprOp: invalid command or expression: " + e.toString());
    break;
  }
  return e;
}

