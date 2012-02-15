/*****************************************************************************/
/*!
 * \file theory_quant.h
 * 
 * Author: Sergey Berezin, Yeting Ge
 * 
 * Created: Jun 24 21:13:59 GMT 2003
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
 * ! Author: Daniel Wichs
 * ! Created: Wednesday July 2, 2003
 *
 * 
 */
/*****************************************************************************/
#ifndef _cvc3__include__theory_quant_h_
#define _cvc3__include__theory_quant_h_

#include "theory.h"
#include "cdmap.h"
#include "statistics.h"
#include<queue>

namespace CVC3 {

class QuantProofRules;

/*****************************************************************************/
/*!
 *\class TheoryQuant
 *\ingroup Theories
 *\brief This theory handles quantifiers.
 *
 * Author: Daniel Wichs
 *
 * Created: Wednesday July 2,  2003
 */
/*****************************************************************************/

 typedef enum{ Ukn, Pos, Neg, PosNeg} Polarity;

 class Trigger {
   Expr trig;
   Polarity polarity;
   CDO<int>* priority;
   Expr head;
   bool hasRWOp;
   bool hasTrans;
   bool hasT2; //if has trans of 2,
   bool isSimple; //if of the form g(x,a);
 public: 
   Trigger(TheoryCore* core, Expr e, Polarity pol, int pri);
   bool  isPos();
   bool  isNeg();
   int   getPri();
   void  setPri(int pri);
   Expr  getEx();
   void  setHead(Expr h);
   Expr  getHead();
   void  setRWOp(bool b);
   bool  hasRW(); 
   void  setTrans(bool b);
   bool  hasTr(); 
   void  setTrans2(bool b);
   bool  hasTr2(); 
   void  setSimp();
   bool  isSimp(); 
 };


class TheoryQuant :public Theory {
  
  class  TypeComp { //!< needed for typeMap
  public:
    bool operator() (const Type t1, const Type t2) const
      {return (t1.getExpr() < t2.getExpr()); }
  };

  //! used to facilitate instantiation of universal quantifiers
  typedef std::map<Type, std::vector<size_t>, TypeComp > typeMap; 

  //! database of universally quantified theorems
  CDList<Theorem> d_univs; 

  //! universally quantified formulas to be instantiated, the var bindings is in d_bingQueue and the ground term matched with the trigger is in d_gtermQueue 
  std::queue<Theorem> d_univsQueue;

  std::queue<Theorem> d_simplifiedThmQueue;

  ExprMap<std::set<std::vector<Expr> > >  d_tempBinds;

  //!tracks the possition of preds 
  CDO<size_t> d_lastPredsPos;
  //!tracks the possition of terms 
  CDO<size_t> d_lastTermsPos;

  //!tracks the positions of preds for partial instantiation
  CDO<size_t> d_lastPartPredsPos;
  //!tracks the possition of terms for partial instantiation
  CDO<size_t> d_lastPartTermsPos;
  //!tracks a possition in the database of universals for partial instantiation
  CDO<size_t> d_univsPartSavedPos;
  
  //! the last decision level on which partial instantion is called
  CDO<size_t> d_lastPartLevel;
  
  //!useful gterms for matching
  CDList<Expr> d_usefulGterms; 

  //!tracks the position in d_usefulGterms
  CDO<size_t> d_lastUsefulGtermsPos;
  
  //!tracks a possition in the savedTerms map
  CDO<size_t> d_savedTermsPos;
  //!tracks a possition in the database of universals
  CDO<size_t> d_univsSavedPos;
  //!tracks a possition in the database of universals
  CDO<size_t> d_univsPosFull;
  //!tracks a possition in the database of universals if fulleffort mode, the d_univsSavedPos now uesed when fulleffort=0 only.

  CDO<size_t> d_univsContextPos;
  
  
  CDO<int> d_instCount; //!< number of instantiations made in given context

  //! set if the fullEffort = 1
  int d_inEnd; 

  int d_allout; 

  //! a map of types to posisitions in the d_contextTerms list
  std::map<Type, CDList<size_t>* ,TypeComp> d_contextMap;
  //! a list of all the terms appearing in the current context
  CDList<Expr> d_contextTerms;
  //!< chache of expressions
  CDMap<Expr, bool> d_contextCache;
  
  //! a map of types to positions in the d_savedTerms vector
  typeMap d_savedMap;
  ExprMap<bool> d_savedCache; //!< cache of expressions
  //! a vector of all of the terms that have produced conflicts.
  std::vector<Expr> d_savedTerms; 

  //! a map of instantiated universals to a vector of their instantiations
  ExprMap<std::vector<Expr> >  d_insts;

  //! quantifier theorem production rules
  QuantProofRules* d_rules;
  
  const int* d_maxQuantInst; //!< Command line option


  /*! \brief categorizes all the terms contained in an expressions by
   *type.
   *
   * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
   * returns true if the expression does not contain bound variables, false
   * otherwise.
   */
  bool recursiveMap(const Expr& term);

  /*! \brief categorizes all the terms contained in a vector of  expressions by
   * type.
   *
   * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
   */
  void mapTermsByType(const CDList<Expr>& terms);
  
  /*! \brief Queues up all possible instantiations of bound
   * variables.
   *
   * The savedMap boolean indicates whether to use savedMap or
   * d_contextMap the all boolean indicates weather to use all
   * instantiation or only new ones and newIndex is the index where
   * new instantiations begin.
   */
  void instantiate(Theorem univ, bool all, bool savedMap, 
		   size_t newIndex);
  //! does most of the work of the instantiate function.
  void recInstantiate(Theorem& univ , bool all, bool savedMap,size_t newIndex, 
				   std::vector<Expr>& varReplacements);

  /*! \brief A recursive function used to find instantiated universals
   * in the hierarchy of assumptions.
   */
  void findInstAssumptions(const Theorem& thm);

  //  CDO<bool> usedup;
  const bool* d_useNew;//!use new way of instantiation
  const bool* d_useLazyInst;//!use lazy instantiation
  const bool* d_useSemMatch;//!use semantic matching
  const bool* d_useAtomSem;
  const bool* d_translate;//!translate only

  const bool* d_useTrigNew;//!use new trig class, to be deleted
  const bool* d_usePart;//!use partial instantiaion
  const bool* d_useMult;//use 
  const bool* d_useInstEnd;
  const bool* d_useInstLCache;
  const bool* d_useInstGCache;
  const bool* d_useInstTrue;
  const bool* d_usePullVar;
  const bool* d_useExprScore;
  const int* d_useTrigLoop;
  const int* d_maxInst;
  //  const int* d_maxUserScore;
  const bool* d_useTrans;
  const bool* d_useTrans2;
  const bool* d_useInstAll;
  const bool* d_usePolarity;
  const bool* d_useEqu;
  const int* d_maxNaiveCall;

  CDO<int> d_curMaxExprScore;

  bool d_useFullTrig;
  bool d_usePartTrig;
  bool d_useMultTrig;

  //ExprMap<std::vector<Expr> > d_arrayIndic; //map array name to a list of indics
  CDMap<Expr, std::vector<Expr> > d_arrayIndic; //map array name to a list of indics
  void arrayIndexName(const Expr& e);

  std::vector<Expr> d_allInsts; //! all instantiations

  int d_initMaxScore;
  int d_offset_multi_trig ;
  
  int d_instThisRound;
  int d_callThisRound;

  int partial_called;

  //  ExprMap<std::vector<Expr> > d_fullTriggers;
  //for multi-triggers, now we only have one set of multi-triggers.
  ExprMap<std::vector<Expr> > d_multTriggers;
  ExprMap<std::vector<Expr> > d_partTriggers;

  ExprMap<std::vector<Trigger> > d_fullTrigs;
  //for multi-triggers, now we only have one set of multi-triggers.
  ExprMap<std::vector<Trigger> > d_multTrigs;
  ExprMap<std::vector<Trigger> > d_partTrigs;

 
  CDO<size_t> d_exprLastUpdatedPos ;//the position of the last expr updated in d_exprUpdate 

  std::map<ExprIndex, int> d_indexScore;

  std::map<ExprIndex, Expr> d_indexExpr;

  int getExprScore(const Expr& e);

  //!the score for a full trigger
  
  ExprMap<bool> d_hasTriggers;
  ExprMap<bool> d_hasMoreBVs;

  int d_trans_num;
  int d_trans2_num;

  ExprMap<CDList<Expr>* > d_trans_back;
  ExprMap<CDList<Expr>* > d_trans_forw;
  CDMap<Expr,bool > d_trans_found;
  CDMap<Expr,bool > d_trans2_found;


  bool transFound(const Expr& comb);

  void setTransFound(const Expr& comb);

  bool trans2Found(const Expr& comb);

  void setTrans2Found(const Expr& comb);

 
  CDList<Expr> & backList(const Expr& ex);
  
  CDList<Expr> & forwList(const Expr& ex);

  CDList<Expr> null_cdlist;


  void  pushBackList(const Expr& node, Expr ex);
  void  pushForwList(const Expr& node, Expr ex);


  ExprMap<CDList<std::vector<Expr> >* > d_mtrigs_inst; //map expr to bindings
  
  ExprMap<CDList<Expr>* > d_same_head_expr; //map an expr to a list of expres shard the same head

  ExprMap<std::vector<Expr> > d_mtrigs_bvorder;

  int loc_gterm(const std::vector<Expr>& border,
		const Expr& gterm, 
		int pos);

  void  recSearchCover(const std::vector<Expr>& border,
		       const std::vector<Expr>& mtrigs, 
		       int cur_depth, 
		       std::vector<std::vector<Expr> >& instSet,
		       std::vector<Expr>& cur_inst
		       );

  void  searchCover(const Expr& thm, 
		    const std::vector<Expr>& border,
		    std::vector<std::vector<Expr> >& instSet
		    );


  std::map<Type, std::vector<Expr>,TypeComp > d_typeExprMap;
  std::set<std::string> cacheHead;

  StatCounter d_allInstCount ;

  CDO<bool> d_partCalled;;

  std::vector<Theorem> d_cacheTheorem;
  size_t d_cacheThmPos;

  void addNotify(const Expr& e);

  int sendInstNew();

  CDMap<Expr, std::set<std::vector<Expr> > > d_instHistory;//the history of instantiations
  //map univ to the trig, gterm and result

  ExprMap<std::set<std::vector<Expr> > > d_instHistoryGlobal;//the history of instantiations

  
  ExprMap<std::vector<Expr> > d_subTermsMap;
  //std::map<Expr, std::vector<Expr> > d_subTermsMap;
  const std::vector<Expr>& getSubTerms(const Expr& e);

  //ExprMap<int > d_thmTimes; 
  void enqueueInst(const Theorem, const Theorem); 
  void enqueueInst(const Theorem& univ, const std::vector<Expr>& bind, const Expr& gterm);

  void enqueueInst(const Theorem& univ, 
		   Trigger& trig,
		   const std::vector<Expr>& binds,  
		   const Expr& gterm
		   );
    
  void synCheckSat(bool);
  void semCheckSat(bool);
  void naiveCheckSat(bool);

  bool insted(const Theorem & univ, const std::vector<Expr>& binds);
  void synInst(const Theorem & univ,  const CDList<Expr>& allterms, size_t tBegin);

  void synFullInst(const Theorem & univ,  const CDList<Expr>& allterms,	size_t tBegin);

  void synMultInst(const Theorem & univ,  const CDList<Expr>& allterms,	 size_t tBegin);

  void synPartInst(const Theorem & univ,  const CDList<Expr>& allterms,	 size_t tBegin);

  void semInst(const Theorem & univ, size_t tBegin);


  void goodSynMatch(const Expr& e,
		    const std::vector<Expr> & boundVars,
		    std::vector<std::vector<Expr> >& instBindsTerm,
		    std::vector<Expr>& instGterm,
		    const CDList<Expr>& allterms,		       
		    size_t tBegin);
  void goodSynMatchNewTrig(Trigger& trig,
			   const std::vector<Expr> & boundVars,
			   std::vector<std::vector<Expr> >& instBinds,
			   std::vector<Expr>& instGterms,
			   const CDList<Expr>& allterms,		       
			   size_t tBegin);

  bool goodSynMatchNewTrig(Trigger& trig,
			   const std::vector<Expr> & boundVars,
			   std::vector<std::vector<Expr> >& instBinds,
			   std::vector<Expr>& instGterms,
			   const Expr& gterm);
    

  bool synMatchTopPred(const Expr& gterm, const Trigger trig, ExprMap<Expr>& env);

  bool recSynMatch(const Expr& gterm, const Expr& vterm, ExprMap<Expr>& env);

  bool hasGoodSynInstNewTrig(Trigger& trig,
			     std::vector<Expr> & boundVars,
			     std::vector<std::vector<Expr> >& instBinds,
			     std::vector<Expr>& instGterms,
			     const CDList<Expr>& allterms,		       
			     size_t tBegin);
    
  bool hasGoodSynMultiInst(const Expr& e,
			   std::vector<Expr>& bVars,
			   std::vector<std::vector<Expr> >& instSet,
			   const CDList<Expr>& allterms,		       
			   size_t tBegin);
  
  void recGoodSemMatch(const Expr& e,
		       const std::vector<Expr>& bVars,
		       std::vector<Expr>& newInst,
		       std::set<std::vector<Expr> >& instSet);
  
  bool hasGoodSemInst(const Expr& e,
		   std::vector<Expr>& bVars,
		   std::set<std::vector<Expr> >& instSet,
		   size_t tBegin);

  bool isTransLike (const std::vector<Expr>& cur_trig);

  bool canMatch(const Expr& t1, const Expr& t2, ExprMap<Expr>& env);
  void setGround(const Expr& gterm, const Expr& trig, const Theorem& univ, const std::vector<Expr>& subTerms) ;    

  //  std::string getHead(const Expr& e) ;
  void setupTriggers(const Theorem& thm);

  void saveContext();


  /*! \brief categorizes all the terms contained in an expressions by
   *type.
   *
   * Updates d_contextTerms, d_contextMap, d_contextCache accordingly.
   * returns true if the expression does not contain bound variables, false
   * otherwise.
   */

  
 public:
  TheoryQuant(TheoryCore* core); //!< Constructor
  ~TheoryQuant(); //! Destructor

  QuantProofRules* createProofRules();
  

 
  void addSharedTerm(const Expr& e) {} //!< Theory interface
  
  /*! \brief Theory interface function to assert quantified formulas
   *
   * pushes in negations and converts to either universally or existentially 
   * quantified theorems. Universals are stored in a database while 
   * existentials are enqueued to be handled by the search engine.
   */
  void assertFact(const Theorem& e); 
  

  /* \brief Checks the satisfiability of the universal theorems stored in a 
   * databse by instantiating them.
   *
   * There are two algorithms that the checkSat function uses to find 
   * instnatiations. The first algortihm looks for instanitations in a saved 
   * database of previous instantiations that worked in proving an earlier
   * theorem unsatifiable. All of the class variables with the word saved in
   * them  are for the use of this algorithm. The other algorithm uses terms 
   * found in the assertions that exist in the particular context when 
   * checkSat is called. All of the class variables with the word context in
   * them are used for the second algorithm.
   */
  void checkSat(bool fullEffort);
  void setup(const Expr& e); 
  void update(const Theorem& e, const Expr& d);
  /*!\brief Used to notify the quantifier algorithm of possible 
   * instantiations that were used in proving a context inconsistent.
   */
  void notifyInconsistent(const Theorem& thm); 
  //! computes the type of a quantified term. Always a  boolean.
  void computeType(const Expr& e); 
  Expr computeTCC(const Expr& e);
  
  virtual Expr parseExprOp(const Expr& e);

  ExprStream& print(ExprStream& os, const Expr& e);
};
 
}

#endif
