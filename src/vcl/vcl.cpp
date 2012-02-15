/*****************************************************************************/
/*!
 * \file vcl.cpp
 * 
 * Author: Clark Barrett
 * 
 * Created: Tue Dec 31 18:27:11 2002
 *
 * <hr>
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 *
 * <hr>
 * 
 */
/*****************************************************************************/


#include <fstream>
#include "vcl.h"
#include "parser.h"
#include "vc_cmd.h"
#include "search_simple.h"
#include "search_fast.h"
#include "search_sat.h"
#include "theory_core.h"
#include "theory_uf.h"
#include "theory_arith_old.h"
#include "theory_arith_new.h"
#include "theory_bitvector.h"
#include "theory_array.h"
#include "theory_quant.h"
#include "theory_records.h"
#include "theory_simulate.h"
#include "theory_datatype.h"
#include "theory_datatype_lazy.h"
#include "translator.h"
#include "typecheck_exception.h"
#include "eval_exception.h"
#include "expr_transform.h"
#include "theorem_manager.h"


namespace CVC3{
  VCL* myvcl;
}

using namespace std;
using namespace CVC3;


///////////////////////////////////////////////////////////////////////////////
// Static ValidityChecker methods
///////////////////////////////////////////////////////////////////////////////



ValidityChecker* ValidityChecker::create(const CLFlags& flags)
{
  return new VCL(flags);
}


CLFlags ValidityChecker::createFlags() {
  CLFlags flags;
  // We expect the user to type cvc3 -h to get help, which will set
  // the "help" flag to false; that's why it's initially true.

  // Overall system control flags
  flags.addFlag("timeout", CLFlag(0, "Kill cvc3 process after given number of seconds (0==no limit)"));
  flags.addFlag("resource", CLFlag(0, "Set finite resource limit (0==no limit)"));
  flags.addFlag("mm", CLFlag("chunks", "Memory manager (chunks, malloc)"));

  // Information printing flags
  flags.addFlag("help",CLFlag(true, "print usage information and exit"));
  flags.addFlag("version",CLFlag(true, "print version information and exit"));
  flags.addFlag("interactive", CLFlag(false, "Interactive mode"));
  flags.addFlag("stats", CLFlag(false, "Print run-time statistics"));
  flags.addFlag("seed", CLFlag(1, "Set the seed for random sequence"));
  flags.addFlag("printResults", CLFlag(true, "Print results of interactive commands."));
  flags.addFlag("dump-log", CLFlag("", "Dump API call log in CVC3 input "
				   "format to given file "
				   "(off when file name is \"\")"));

  //Translation related flags
  flags.addFlag("expResult", CLFlag("", "For smtlib translation.  Give the expected result"));
  flags.addFlag("category", CLFlag("unknown", "For smtlib translation.  Give the category"));
  flags.addFlag("translate", CLFlag(false, "Produce a complete translation from "
                                           "the input language to output language.  "));
  flags.addFlag("real2int", CLFlag(false, "When translating, convert reals to integers."));
  flags.addFlag("convertArith", CLFlag(false, "When translating, try to rewrite arith terms into smt-lib subset"));
  flags.addFlag("convert2diff", CLFlag("", "When translating, try to force into difference logic.  Legal values are int and real."));
  flags.addFlag("iteLiftArith", CLFlag(false, "For translation.  If true, ite's are lifted out of arith exprs."));
  flags.addFlag("convertArray", CLFlag(false, "For translation.  If true, arrays are converted to uninterpreted functions if possible."));
  flags.addFlag("combineAssump", CLFlag(false, "For translation.  If true, assumptions are combined into the query."));

  // Parser related flags
  flags.addFlag("old-func-syntax",CLFlag(false, "Enable parsing of old-style function syntax"));

  // Pretty-printing related flags
  flags.addFlag("dagify-exprs",
		CLFlag(true, "Print expressions with sharing as DAGs"));
  flags.addFlag("lang", CLFlag("smtlib", "Input language "
			       "(presentation, smtlib, internal)"));
  flags.addFlag("output-lang", CLFlag("", "Output language "
				      "(presentation, smtlib, simplify, internal, lisp)"));
  flags.addFlag("indent", CLFlag(false, "Print expressions with indentation"));
  flags.addFlag("width", CLFlag(80, "Suggested line width for printing"));
  flags.addFlag("print-depth", CLFlag(-1, "Max. depth to print expressions "));
  flags.addFlag("print-assump", CLFlag(false, "Print assumptions in Theorems "));

  // Search Engine (SAT) related flags
  flags.addFlag("sat",CLFlag("minisat", "choose a SAT solver to use "
			     "(fast, simple, sat, minisat)"));
  flags.addFlag("de",CLFlag("dfs", "choose a decision engine to use "
			    "(dfs, sat)"));

  // Proofs and Assumptions
  flags.addFlag("proofs", CLFlag(false, "Produce proofs"));
  flags.addFlag("check-proofs",
		CLFlag(IF_DEBUG(true ||) false, "Check proofs on-the-fly"));
  flags.addFlag("minimizeClauses", CLFlag(false, "Use brute-force minimization of clauses"));

  // Core framework switches
  flags.addFlag("tcc", CLFlag(false, "Check TCCs for each ASSERT and QUERY"));
  flags.addFlag("cnf", CLFlag(true, "Convert top-level Boolean formulas to CNF"));
  flags.addFlag("ignore-cnf-vars", CLFlag(false, "Do not split on aux. CNF vars (with +cnf)"));
  flags.addFlag("orig-formula", CLFlag(false, "Preserve the original formula with +cnf (for splitter heuristics)"));
  flags.addFlag("iflift", CLFlag(false, "Translate if-then-else terms to CNF (with +cnf)"));
  flags.addFlag("circuit", CLFlag(false, "With +cnf, use circuit propagation"));
  flags.addFlag("un-ite-ify", CLFlag(false, "Unconvert ITE expressions"));
  flags.addFlag("ite-cond-simp",
		CLFlag(false, "Replace ITE condition by TRUE/FALSE in subexprs"));
  flags.addFlag("pp-pushneg", CLFlag(false, "Push negation in preprocessor"));
  flags.addFlag("pushneg", CLFlag(true, "Push negation while simplifying"));
  flags.addFlag("simp-and", CLFlag(false, "Rewrite x&y to x&y[x/true]"));
  flags.addFlag("simp-or", CLFlag(false, "Rewrite x|y to x|y[x/false]"));
  // Concrete model generation (counterexamples) flags
  flags.addFlag("applications", CLFlag(true, "Add relevant function applications and array accesses to the concrete countermodel"));
  // Debugging flags (only for the debug build)
  // #ifdef DEBUG
  vector<pair<string,bool> > sv;
  flags.addFlag("trace", CLFlag(sv, "Tracing.  Multiple flags add up."));
  flags.addFlag("dump-trace", CLFlag("", "Dump debugging trace to "
				   "given file (off when file name is \"\")"));
  // #endif
  // DP-specific flags

  // Arithmetic
  flags.addFlag("arith-new",CLFlag(false, "Use new arithmetic dp"));
  flags.addFlag("var-order",
		CLFlag(false, "Use simple variable order in arith"));
  flags.addFlag("ineq-delay", CLFlag(10, "Accumulate this many inequalities "
				     "before processing"));

  // Arrays
  flags.addFlag("liftReadIte", CLFlag(true, "Lift read of ite"));

  // Quantifiers
  flags.addFlag("max-quant-inst", CLFlag(200, "The maximum number of"
			       	" naive instantiations"));

  flags.addFlag("quant-new",
		 CLFlag(true, "Use new quantifier instantiation algorithm"));

  flags.addFlag("quant-lazy", CLFlag(false, "Instantiate lazily"));

  flags.addFlag("quant-sem-match",
                CLFlag(false, "Attempt to match semantically when instantiating"));

  flags.addFlag("quant-const-match",
                CLFlag(true, "When matching semantically, only match with constants"));

  flags.addFlag("quant-match-old",
		CLFlag(false, "Use the old match algorithm"));

  flags.addFlag("quant-inst-part", 
                CLFlag(false, "Use partial instantiation"));

  flags.addFlag("quant-inst-mult", 
                CLFlag(true, "Use multi-triggers in instantiation"));

  flags.addFlag("quant-trig-new", 
		CLFlag(true, "Use new trig algorithms"));

  flags.addFlag("quant-max-inst", 
		CLFlag(600, "The maximum number of instantiations"));

  flags.addFlag("quant-inst-end", 
		CLFlag(true, "Use end heuristic"));

  flags.addFlag("quant-inst-lcache", 
                CLFlag(true, "Cache instantiations"));

  flags.addFlag("quant-inst-gcache", 
                CLFlag(false, "Cache instantiations"));

  flags.addFlag("quant-inst-true", 
                CLFlag(true, "Ignore true instantiations"));

  flags.addFlag("quant-pullvar", 
                CLFlag(false, "Pull out vars"));

  flags.addFlag("quant-trig-loop", 
                CLFlag(0, "Trigger loop prevention method, 0, 1, 2"));

  flags.addFlag("quant-score", 
                CLFlag(true, "Use instantiation level"));

  flags.addFlag("quant-polarity", 
                CLFlag(true, "Use polarity "));

  flags.addFlag("quant-equ", 
                CLFlag(true, "Use equality matching"));

  flags.addFlag("quant-max-score", 
                CLFlag(0, "Maximum initial dynamic score"));

  flags.addFlag("quant-inst-all", 
                CLFlag(false, "try all possible instantiation eagerly"));

  flags.addFlag("quant-trans3", 
                CLFlag(true, "Use trans heuristic"));

  flags.addFlag("quant-trans2", 
                CLFlag(true, "Use trans2 heuristic"));

  flags.addFlag("quant-naive-num", 
                CLFlag(100, "Maximum number to call niave instantiation"));

  
  //Bitvectors
  flags.addFlag("bv32-flag",
		CLFlag(false, "assume that all bitvectors are 32bits with no overflow"));
  flags.addFlag("bv-rewrite",
		CLFlag(true, "Rewrite bitvector expressions"));
  flags.addFlag("bv-concatnormal-rewrite",
		CLFlag(true, "Concat Normal Form rewrites"));
  flags.addFlag("bv-plusnormal-rewrite",
		CLFlag(true, "Bvplus Normal Form rewrites"));
  flags.addFlag("bv-rw-bitblast",
		CLFlag(false, "Rewrite while bit-blasting"));
  flags.addFlag("bv-cnf-bitblast", 
		CLFlag(true,"Bitblast equalities in CNFconverter with +cnf"));
  flags.addFlag("bv-lhs-minus-rhs", 
		CLFlag(false,"Do lhs-rhs=0 if both lhs/rhs are BVPLUS"));
  flags.addFlag("bv-pushnegation", 
		CLFlag(true,"pushnegation to the leaves"));

  // Uninterpreted Functions
  flags.addFlag("trans-closure",
		CLFlag(false,"enables transitive closure of binary relations"));

  // Datatypes
  flags.addFlag("dt-smartsplits",
                CLFlag(true, "enables smart splitting in datatype theory"));
  flags.addFlag("dt-lazy",
                CLFlag(false, "lazy splitting on datatypes"));

  return flags;
}


ValidityChecker* ValidityChecker::create()
{
  return new VCL(createFlags());
}


///////////////////////////////////////////////////////////////////////////////
// VCL private methods
///////////////////////////////////////////////////////////////////////////////


Theorem3 VCL::deriveClosure(const Theorem3& thm) {
  vector<Expr> assump;
  set<UserAssertion> assumpSet;
  // Compute the vector of assumptions for thm, and iteratively move
  // the assumptions to the RHS until done.  Each closure step may
  // introduce new assumptions from the proofs of TCCs, so those need
  // to be dealt with in the same way, until no assumptions remain.
  Theorem3 res = thm;
  vector<Theorem> tccs;
  while(true) {
    {
      const Assumptions& a(res.getAssumptionsRef());
      if (a.empty()) break;
      assump.clear();
      assumpSet.clear();
      Assumptions::iterator i=a.begin(), iend=a.end();
      if(i!=iend) i->clearAllFlags();
      // Collect the assumptions of 'res' *without* TCCs
      for(; i!=iend; ++i)
        getAssumptionsRec(*i, assumpSet, false);

      // Build the vectors of assumptions and TCCs
      if(getFlags()["tcc"].getBool()) {
        tccs.clear();
        for(set<UserAssertion>::iterator i=assumpSet.begin(),
              iend=assumpSet.end(); i!=iend; ++i) {
          assump.push_back(i->thm().getExpr());
          tccs.push_back(i->tcc());
        }
      }
    }
    // Derive the closure
    res = d_se->getCommonRules()->implIntro3(res, assump, tccs);
  }
  return res;
}


//! Recursive assumption graph traversal to find user assumptions
/*!
 *  If an assumption has a TCC, traverse the proof of TCC and add its
 *  assumptions to the set recursively.
 */
void VCL::getAssumptionsRec(const Theorem& thm,
			    set<UserAssertion>& assumptions,
			    bool addTCCs) {
  if(thm.isNull() || thm.isRefl() || thm.isFlagged()) return;
  thm.setFlag();
  if(thm.isAssump()) {
    if(d_userAssertions->count(thm.getExpr())>0) {
      const UserAssertion& a = (*d_userAssertions)[thm.getExpr()];
      assumptions.insert(a);
      if(addTCCs) {
	DebugAssert(!a.tcc().isNull(), "getAssumptionsRec(a="
		    +a.thm().toString()+", thm = "+thm.toString()+")");
	getAssumptionsRec(a.tcc(), assumptions, true);
      }
    } else { // it's a splitter
      UserAssertion a(thm, Theorem(), d_nextIdx++);
      assumptions.insert(a);
    }
  }
  else {
    const Assumptions& a(thm.getAssumptionsRef());
    for(Assumptions::iterator i=a.begin(), iend=a.end(); i!=iend; ++i)
      getAssumptionsRec(*i, assumptions, addTCCs);
  }
}


void VCL::getAssumptions(const Assumptions& a, vector<Expr>& assumptions)
{
  set<UserAssertion> assumpSet;
  if(a.empty()) return;
  Assumptions::iterator i=a.begin(), iend=a.end();
  if(i!=iend) i->clearAllFlags();
  for(; i!=iend; ++i)
    getAssumptionsRec(*i, assumpSet, getFlags()["tcc"].getBool());
  // Order assumptions by their creation time
  for(set<UserAssertion>::iterator i=assumpSet.begin(), iend=assumpSet.end();
      i!=iend; ++i)
    assumptions.push_back(i->thm().getExpr());
}


IF_DEBUG(
void VCL::dumpTrace(int scope) {
  vector<StrPair> fields;
  fields.push_back(strPair("scope", int2string(scope)));
  debugger.dumpTrace("scope", fields);
}
)


///////////////////////////////////////////////////////////////////////////////
// Public VCL methods
///////////////////////////////////////////////////////////////////////////////


VCL::VCL(const CLFlags& flags)
  : d_flags(new CLFlags(flags)), d_nextIdx(0)
{
  // Set the dependent flags so that they are consistent

  if ((*d_flags)["translate"].getBool())
    d_flags->setFlag("printResults", false);

  IF_DEBUG( // Initialize the global debugger
	   CVC3::debugger.init(&((*d_flags)["trace"].getStrVec()),
                               &((*d_flags)["dump-trace"].getString()))
  );

  d_cm = new ContextManager();

  // Initialize the database of user assertions.  It has to be
  // initialized after d_cm.
  d_userAssertions = new(true) CDMap<Expr,UserAssertion>(getCurrentContext());

  d_em = new ExprManager(d_cm, *d_flags);

  d_tm = new TheoremManager(d_cm, d_em, *d_flags);
  d_em->setTM(d_tm);

  d_translator = new Translator(d_em,
                                (*d_flags)["translate"].getBool(),
                                (*d_flags)["real2int"].getBool(),
                                (*d_flags)["convertArith"].getBool(),
                                (*d_flags)["convert2diff"].getString(),
                                (*d_flags)["iteLiftArith"].getBool(),
                                (*d_flags)["expResult"].getString(),
                                (*d_flags)["category"].getString(),
                                (*d_flags)["convertArray"].getBool(),
                                (*d_flags)["combineAssump"].getBool());

  d_dump = d_translator->start((*d_flags)["dump-log"].getString());

  d_theoryCore = new TheoryCore(d_cm, d_em, d_tm, d_translator, *d_flags, d_statistics);
  d_theories.push_back(d_theoryCore);

  // Fast rewriting of literals is done by setting their find to true or false.
  falseExpr().setFind(d_theoryCore->reflexivityRule(falseExpr()));
  trueExpr().setFind(d_theoryCore->reflexivityRule(trueExpr()));

  d_theories.push_back(d_theoryUF = new TheoryUF(d_theoryCore));

  if ((*d_flags)["arith-new"].getBool()) {
    d_theories.push_back(d_theoryArith = new TheoryArithNew(d_theoryCore));
  }
  else {
    d_theories.push_back(d_theoryArith = new TheoryArithOld(d_theoryCore));
  }
  d_theories.push_back(d_theoryArray = new TheoryArray(d_theoryCore));
  d_theories.push_back(d_theoryRecords = new TheoryRecords(d_theoryCore));
  d_theories.push_back(d_theorySimulate = new TheorySimulate(d_theoryCore));
  d_theories.push_back(d_theoryBitvector = new TheoryBitvector(d_theoryCore));
  if ((*d_flags)["dt-lazy"].getBool()) {
    d_theories.push_back(d_theoryDatatype = new TheoryDatatypeLazy(d_theoryCore));
  }
  else {
    d_theories.push_back(d_theoryDatatype = new TheoryDatatype(d_theoryCore));
  }
  d_theories.push_back(d_theoryQuant = new TheoryQuant(d_theoryCore));

  d_translator->setTheoryCore(d_theoryCore);
  d_translator->setTheoryUF(d_theoryUF);
  d_translator->setTheoryArith(d_theoryArith);
  d_translator->setTheoryArray(d_theoryArray);
  d_translator->setTheoryQuant(d_theoryQuant);
  d_translator->setTheoryRecords(d_theoryRecords);
  d_translator->setTheorySimulate(d_theorySimulate);
  d_translator->setTheoryBitvector(d_theoryBitvector);
  d_translator->setTheoryDatatype(d_theoryDatatype);

  // Must be created after TheoryCore, since it needs it.
  // When we have more than one search engine, select one to create
  // based on flags
  const string& satEngine = (*d_flags)["sat"].getString();
  if (satEngine == "simple")
    d_se = new SearchSimple(d_theoryCore); 
  else if (satEngine == "fast")
    d_se = new SearchEngineFast(d_theoryCore);
  else if (satEngine == "sat" || satEngine == "minisat")
    d_se = new SearchSat(d_theoryCore, satEngine);
  else
    throw CLException("Unrecognized SAT solver name: "
                      +(*d_flags)["sat"].getString());

  // Initial scope level should be 1
  d_cm->push();

  d_stackLevel = new(true) CDO<int>(d_cm->getCurrentContext(), 0);

  d_theoryCore->setResourceLimit((unsigned)((*d_flags)["resource"].getInt()));

  myvcl = this;
}


VCL::~VCL()
{
  popto(0);
  d_cm->popto(0);
  delete d_stackLevel;
  free(d_stackLevel);
  d_translator->finish();
  delete d_translator;

  TRACE_MSG("delete", "Deleting SearchEngine {");
  delete d_se;
  TRACE_MSG("delete", "Finished deleting SearchEngine }");
  // This map contains expressions and theorems; delete it before
  // d_em, d_tm, and d_cm.
  TRACE_MSG("delete", "Deleting d_userAssertions {");
  delete d_userAssertions;
  free(d_userAssertions);
  TRACE_MSG("delete", "Finished deleting d_userAssertions }");
  // and set these to null so their destructors don't blow up
  d_lastQuery = Theorem3();
  d_lastQueryTCC = Theorem();
  d_lastClosure = Theorem3();
  // Delete ExprManager BEFORE TheoremManager, since Exprs use Theorems
  TRACE_MSG("delete", "Clearing d_em {");
  d_em->clear();
  d_tm->clear();
  TRACE_MSG("delete", "Finished clearing d_em }");
  TRACE_MSG("delete", "Deleting d_cm {");
  delete d_cm;
  TRACE_MSG("delete", "Finished deleting d_cm }");

  for(size_t i=0; i<d_theories.size(); ++i) {
    string name(d_theories[i]->getName());
    TRACE("delete", "Deleting Theory[", name, "] {");
    delete d_theories[i];
    TRACE("delete", "Finished deleting Theory[", name, "] }");
  }
  // TheoremManager does not call ~Theorem() destructors, and only
  // releases memory.  At worst, we'll lose some Assumptions.
  TRACE_MSG("delete", "Deleting d_tm {");
  delete d_tm;
  TRACE_MSG("delete", "Finished deleting d_tm }");

  TRACE_MSG("delete", "Deleting d_em {");
  delete d_em;
  TRACE_MSG("delete", "Finished deleting d_em }");

  TRACE_MSG("delete", "Deleting d_flags [end of ~VCL()]");
  delete d_flags;
  // No more TRACE-ing after this point (it needs d_flags)
}


void VCL::reprocessFlags() {
  if (d_se->getName() != (*d_flags)["sat"].getString()) {
    delete d_se;
    const string& satEngine = (*d_flags)["sat"].getString();
    if (satEngine == "simple")
      d_se = new SearchSimple(d_theoryCore); 
    else if (satEngine == "fast")
      d_se = new SearchEngineFast(d_theoryCore);
    else if (satEngine == "sat" || satEngine == "minisat")
      d_se = new SearchSat(d_theoryCore, satEngine);
    else
      throw CLException("Unrecognized SAT solver name: "
                        +(*d_flags)["sat"].getString());
  }

  if (d_theoryArith->getName() == "ArithmeticOld" &&
      (*d_flags)["arith-new"].getBool()) {
    delete d_theoryArith;
    d_theoryArith = new TheoryArithNew(d_theoryCore);
    d_theories[2] = d_theoryArith;
    d_translator->setTheoryArith(d_theoryArith);
  }
  else if (d_theoryArith->getName() == "ArithmeticNew" &&
           !(*d_flags)["arith-new"].getBool()) {
    delete d_theoryArith;
    d_theoryArith = new TheoryArithOld(d_theoryCore);
    d_theories[2] = d_theoryArith;
    d_translator->setTheoryArith(d_theoryArith);
  }

  //TODO: handle more flags
}

TheoryCore* VCL::core(){
  return d_theoryCore;
}

Type VCL::boolType(){
  return d_theoryCore->boolType();
}


Type VCL::realType()
{
  return d_theoryArith->realType();
}


Type VCL::intType() {
  return d_theoryArith->intType();
}


Type VCL::subrangeType(const Expr& l, const Expr& r) {
  return d_theoryArith->subrangeType(l, r);
}


Type VCL::subtypeType(const Expr& pred, const Expr& witness)
{
  return d_theoryCore->newSubtypeExpr(pred, witness);
}


Type VCL::tupleType(const Type& type0, const Type& type1)
{
  vector<Type> types;
  types.push_back(type0);
  types.push_back(type1);
  return d_theoryRecords->tupleType(types);
}


Type VCL::tupleType(const Type& type0, const Type& type1, const Type& type2)
{
  vector<Type> types;
  types.push_back(type0);
  types.push_back(type1);
  types.push_back(type2);
  return d_theoryRecords->tupleType(types);
}


Type VCL::tupleType(const vector<Type>& types)
{
  return d_theoryRecords->tupleType(types);
}


Type VCL::recordType(const string& field, const Type& type)
{
  vector<string> fields;
  vector<Type> kids;
  fields.push_back(field);
  kids.push_back(type);
  return Type(d_theoryRecords->recordType(fields, kids));
}


Type VCL::recordType(const string& field0, const Type& type0,
		     const string& field1, const Type& type1) {
  vector<string> fields;
  vector<Type> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  kids.push_back(type0);
  kids.push_back(type1);
  sort2(fields, kids);
  return Type(d_theoryRecords->recordType(fields, kids));
}


Type VCL::recordType(const string& field0, const Type& type0,
		     const string& field1, const Type& type1,
		     const string& field2, const Type& type2)
{
  vector<string> fields;
  vector<Type> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  fields.push_back(field2);
  kids.push_back(type0);
  kids.push_back(type1);
  kids.push_back(type2);
  sort2(fields, kids);
  return Type(d_theoryRecords->recordType(fields, kids));
}


Type VCL::recordType(const vector<string>& fields,
		     const vector<Type>& types)
{
  DebugAssert(fields.size() == types.size(),
	      "VCL::recordType: number of fields is different \n"
	      "from the number of types");
  // Create copies of the vectors to sort them
  vector<string> fs(fields);
  vector<Type> ts(types);
  sort2(fs, ts);
  return Type(d_theoryRecords->recordType(fs, ts));
}


Type VCL::dataType(const string& name,
                   const string& constructor,
                   const vector<string>& selectors, const vector<Expr>& types)
{
  vector<string> constructors;
  constructors.push_back(constructor);

  vector<vector<string> > selectorsVec;
  selectorsVec.push_back(selectors);

  vector<vector<Expr> > typesVec;
  typesVec.push_back(types);

  return dataType(name, constructors, selectorsVec, typesVec);
}


Type VCL::dataType(const string& name,
                   const vector<string>& constructors,
                   const vector<vector<string> >& selectors,
                   const vector<vector<Expr> >& types)
{
  return d_theoryDatatype->dataType(name, constructors, selectors, types);
}


void VCL::dataType(const vector<string>& names,
                   const vector<vector<string> >& constructors,
                   const vector<vector<vector<string> > >& selectors,
                   const vector<vector<vector<Expr> > >& types,
                   vector<Type>& returnTypes)
{
  d_theoryDatatype->dataType(names, constructors, selectors, types, returnTypes);
}


Type VCL::arrayType(const Type& typeIndex, const Type& typeData)
{
  return ::arrayType(typeIndex, typeData);
}


Type VCL::bitvecType(int n)
{
  return d_theoryBitvector->newBitvectorType(n);
}


Type VCL::funType(const Type& typeDom, const Type& typeRan)
{
  return typeDom.funType(typeRan);
}


Type VCL::funType(const vector<Type>& typeDom, const Type& typeRan) {
  DebugAssert(typeDom.size() >= 1, "VCL::funType: missing domain types");
  return Type::funType(typeDom, typeRan);
}


Type VCL::createType(const string& typeName)
{
  if(d_dump) {
    d_translator->dump(Expr(TYPE, listExpr(idExpr(typeName))));
  }
  return d_theoryCore->newTypeExpr(typeName);
}


Type VCL::createType(const string& typeName, const Type& def)
{
  if (d_dump) {
    d_translator->dump(Expr(TYPE, idExpr(typeName), def.getExpr()), true);
  }
  return d_theoryCore->newTypeExpr(typeName, def);
}


Type VCL::lookupType(const string& typeName)
{
  // TODO: check if it already exists
  return d_theoryCore->newTypeExpr(typeName);
}


Expr VCL::varExpr(const string& name, const Type& type)
{
  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr()));
  }
  return d_theoryCore->newVar(name, type);
}


Expr VCL::varExpr(const string& name, const Type& type, const Expr& def)
{
  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr(), def), true);
  }
  // Prove the TCCs of the definition
  if(getFlags()["tcc"].getBool()) {
    Type tpDef(def.getType()), tpVar(type);
    // Make sure that def is in the subtype of tpVar; that is, prove
    // FORALL (x: tpDef): x = def => typePred(tpVar)(x)
    if(tpDef != tpVar) {
      // Typecheck the base types
      if(getBaseType(tpDef) != getBaseType(type)) {
	throw TypecheckException("Type mismatch in constant definition:\n"
				 "Constant "+name+
				 " is declared with type:\n  "
				 +type.toString()
				 +"\nBut the type of definition is\n  "
				 +tpDef.toString());
      }
      TRACE("tccs", "CONST def: "+name+" : "+tpVar.toString()
	    +" := <value> : ", tpDef, ";");
      vector<Expr> boundVars;
      boundVars.push_back(boundVarExpr(name, "tcc", tpDef));
      Expr body(boundVars[0].eqExpr(def).impExpr(getTypePred(tpVar, boundVars[0])));
      Expr quant(forallExpr(boundVars, body));
      try {
        checkTCC(quant);
      } catch(TypecheckException&) {
	throw TypecheckException
	  ("Type mismatch in constant definition:\n"
	   "Constant "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\nBut the type of definition is\n  "
	   +def.getType().toString()
	   +"\n\n which is not a subtype of the constant");
      }
    }
  }
  return d_theoryCore->newVar(name, type, def);
}


Expr VCL::boundVarExpr(const string& name, const string& uid, 
		       const Type& type) {
  return d_em->newBoundVarExpr(name, uid, type);
}


Expr VCL::lookupVar(const string& name, Type* type)
{
  return d_theoryCore->lookupVar(name, type);
}


Type VCL::getType(const Expr& e)
{
  return e.getType();
}


Type VCL::getBaseType(const Expr& e)
{
  return d_theoryCore->getBaseType(e);
}


Type VCL::getBaseType(const Type& t)
{
  return d_theoryCore->getBaseType(t);
}


Expr VCL::getTypePred(const Type&t, const Expr& e)
{
  return d_theoryCore->getTypePred(t, e);
}


Expr VCL::stringExpr(const string& str) {
  return getEM()->newStringExpr(str);
}


Expr VCL::idExpr(const string& name) {
  return Expr(ID, stringExpr(name));
}


Expr VCL::listExpr(const vector<Expr>& kids) {
  return Expr(RAW_LIST, kids, getEM());
}


Expr VCL::listExpr(const Expr& e1) {
  return Expr(RAW_LIST, e1);
}


Expr VCL::listExpr(const Expr& e1, const Expr& e2) {
  return Expr(RAW_LIST, e1, e2);
}


Expr VCL::listExpr(const Expr& e1, const Expr& e2, const Expr& e3) {
  return Expr(RAW_LIST, e1, e2, e3);
}


Expr VCL::listExpr(const string& op, const vector<Expr>& kids) {
  vector<Expr> newKids;
  newKids.push_back(idExpr(op));
  newKids.insert(newKids.end(), kids.begin(), kids.end());
  return listExpr(newKids);
}


Expr VCL::listExpr(const string& op, const Expr& e1) {
  return Expr(RAW_LIST, idExpr(op), e1);
}


Expr VCL::listExpr(const string& op, const Expr& e1,
		   const Expr& e2) {
  return Expr(RAW_LIST, idExpr(op), e1, e2);
}


Expr VCL::listExpr(const string& op, const Expr& e1,
		   const Expr& e2, const Expr& e3) {
  vector<Expr> kids;
  kids.push_back(idExpr(op));
  kids.push_back(e1);
  kids.push_back(e2);
  kids.push_back(e3);
  return listExpr(kids);
}


void VCL::printExpr(const Expr& e) {
  printExpr(e, cout);
}


void VCL::printExpr(const Expr& e, ostream& os) {
  os << e << endl;
}


Expr VCL::parseExpr(const Expr& e) {
  return d_theoryCore->parseExprTop(e);
}


Type VCL::parseType(const Expr& e) {
  return Type(d_theoryCore->parseExpr(e));
}


Expr VCL::importExpr(const Expr& e)
{
  return d_em->rebuild(e);
}


Type VCL::importType(const Type& t)
{
  return Type(d_em->rebuild(t.getExpr()));
}


Expr VCL::trueExpr()
{
  return d_em->trueExpr();
}


Expr VCL::falseExpr()
{
  return d_em->falseExpr();
}


Expr VCL::notExpr(const Expr& child)
{
  return !child;
}


Expr VCL::andExpr(const Expr& left, const Expr& right)
{
  return left && right;
}


Expr VCL::andExpr(const vector<Expr>& children)
{
  if (children.size() == 0)
    throw Exception("andExpr requires at least one child");
  return Expr(AND, children);
}


Expr VCL::orExpr(const Expr& left, const Expr& right)
{
  return left || right;
}


Expr VCL::orExpr(const vector<Expr>& children)
{
  if (children.size() == 0)
    throw Exception("orExpr requires at least one child");
  return Expr(OR, children);
}


Expr VCL::impliesExpr(const Expr& hyp, const Expr& conc)
{
  return hyp.impExpr(conc);
}


Expr VCL::iffExpr(const Expr& left, const Expr& right)
{
  return left.iffExpr(right);
}


Expr VCL::eqExpr(const Expr& child0, const Expr& child1)
{
  return child0.eqExpr(child1);
}


Expr VCL::iteExpr(const Expr& ifpart, const Expr& thenpart, const Expr& elsepart)
{
  return ifpart.iteExpr(thenpart, elsepart);
}


Op VCL::createOp(const string& name, const Type& type)
{
  if (!type.isFunction())
    throw Exception("createOp: expected function type");
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr()));
  }
  return d_theoryCore->newFunction(name, type,
                                   getFlags()["trans-closure"].getBool());
}


Op VCL::createOp(const string& name, const Type& type, const Expr& def)
{
  if (!type.isFunction())
    throw TypecheckException
	  ("Type error in createOp:\n"
	   "Constant "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\n which is not a function type");
  if (getBaseType(type) != getBaseType(def.getType()))
    throw TypecheckException
	  ("Type mismatch in createOp:\n"
	   "Function "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\nBut the type of definition is\n  "
	   +def.getType().toString()
	   +"\n\n which does not match");
  if(d_dump) {
    d_translator->dump(Expr(CONST, idExpr(name), type.getExpr(), def), true);
  }
  // Prove the TCCs of the definition
  if(getFlags()["tcc"].getBool()) {
    Type tpDef(def.getType());
    // Make sure that def is within the subtype; that is, prove
    // FORALL (xs: argType): typePred_{return_type}(def(xs))
    if(tpDef != type) {
      vector<Expr> boundVars;
      for (int i = 0; i < type.arity()-1; ++i) {
        boundVars.push_back(d_em->newBoundVarExpr(type[i]));
      }
      Expr app = Expr(def.mkOp(), boundVars);
      Expr body(getTypePred(type[type.arity()-1], app));
      Expr quant(forallExpr(boundVars, body));
      Expr tcc = quant.andExpr(d_theoryCore->getTCC(quant));
      // Query the subtyping formula
      bool typesMatch = true;
      try {
        checkTCC(tcc);
      } catch (TypecheckException&) {
        typesMatch = false;
      }
      if(!typesMatch) {
	throw TypecheckException
	  ("Type mismatch in createOp:\n"
	   "Function "+name+
	   " is declared with type:\n  "
	   +type.toString()
	   +"\nBut the definition is\n  "
	   +def.toString()
	   +"\n\nwhose type could not be proved to be a subtype");
      }
    }
  }
  return d_theoryCore->newFunction(name, type, def);
}


Expr VCL::funExpr(const Op& op, const Expr& child)
{
  return Expr(op, child);
}


Expr VCL::funExpr(const Op& op, const Expr& left, const Expr& right)
{
  return Expr(op, left, right);
}


Expr VCL::funExpr(const Op& op, const Expr& child0, const Expr& child1, const Expr& child2)
{
  return Expr(op, child0, child1, child2);
}


Expr VCL::funExpr(const Op& op, const vector<Expr>& children)
{
  return Expr(op, children);
}


Expr VCL::ratExpr(int n, int d)
{
  DebugAssert(d != 0,"denominator cannot be 0");
  return d_em->newRatExpr(Rational(n,d));
}


Expr VCL::ratExpr(const string& n, const string& d, int base)
{
  return d_em->newRatExpr(Rational(n.c_str(), d.c_str(), base));
}


Expr VCL::ratExpr(const string& n, int base)
{
  string::size_type pos = n.rfind(".");
  if (pos == string::npos) {
    return d_em->newRatExpr(Rational(n.c_str(), base));
  }
  string afterdec = n.substr(pos+1);
  string beforedec = n.substr(0, pos);
  if (afterdec.size() == 0 || beforedec.size() == 0) {
    throw Exception("Cannot convert string to rational: "+n);
  }
  pos = beforedec.rfind(".");
  if (pos != string::npos) {
    throw Exception("Cannot convert string to rational: "+n);
  }
  Rational r = Rational(beforedec.c_str(), base);
  Rational fracPart = Rational(afterdec.c_str(), base);
  r = r + (fracPart / pow(afterdec.size(), base));
  return d_em->newRatExpr(r);
}


Expr VCL::uminusExpr(const Expr& child)
{
  return -child;
}


Expr VCL::plusExpr(const Expr& left, const Expr& right)
{
  return left + right;
}


Expr VCL::minusExpr(const Expr& left, const Expr& right)
{
  return left - right;
}


Expr VCL::multExpr(const Expr& left, const Expr& right)
{
  return left * right;
}


Expr VCL::powExpr(const Expr& x, const Expr& n)
{
  return ::powExpr(n, x);
}


Expr VCL::divideExpr(const Expr& num, const Expr& denom)
{
  return ::divideExpr(num,denom);
}


Expr VCL::ltExpr(const Expr& left, const Expr& right)
{
  return ::ltExpr(left, right);
}


Expr VCL::leExpr(const Expr& left, const Expr& right)
{
  return ::leExpr(left, right);
}


Expr VCL::gtExpr(const Expr& left, const Expr& right)
{
  return ::gtExpr(left, right);
}


Expr VCL::geExpr(const Expr& left, const Expr& right)
{
  return ::geExpr(left, right);
}


Expr VCL::recordExpr(const string& field, const Expr& expr)
{
  vector<string> fields;
  vector<Expr> kids;
  kids.push_back(expr);
  fields.push_back(field);
  return d_theoryRecords->recordExpr(fields, kids);
}


Expr VCL::recordExpr(const string& field0, const Expr& expr0,
		     const string& field1, const Expr& expr1)
{
  vector<string> fields;
  vector<Expr> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  kids.push_back(expr0);
  kids.push_back(expr1);
  sort2(fields, kids);
  return d_theoryRecords->recordExpr(fields, kids);
}


Expr VCL::recordExpr(const string& field0, const Expr& expr0,
		     const string& field1, const Expr& expr1,
		     const string& field2, const Expr& expr2)
{
  vector<string> fields;
  vector<Expr> kids;
  fields.push_back(field0);
  fields.push_back(field1);
  fields.push_back(field2);
  kids.push_back(expr0);
  kids.push_back(expr1);
  kids.push_back(expr2);
  sort2(fields, kids);
  return d_theoryRecords->recordExpr(fields, kids);
}


Expr VCL::recordExpr(const vector<string>& fields,
		     const vector<Expr>& exprs)
{
  DebugAssert(fields.size() > 0, "VCL::recordExpr()");
  DebugAssert(fields.size() == exprs.size(),"VCL::recordExpr()");
  // Create copies of the vectors to sort them
  vector<string> fs(fields);
  vector<Expr> es(exprs);
  sort2(fs, es);
  return d_theoryRecords->recordExpr(fs, es);
}


Expr VCL::recSelectExpr(const Expr& record, const string& field)
{
  return d_theoryRecords->recordSelect(record, field);
}


Expr VCL::recUpdateExpr(const Expr& record, const string& field,
			const Expr& newValue)
{
  return d_theoryRecords->recordUpdate(record, field, newValue);
}


Expr VCL::readExpr(const Expr& array, const Expr& index)
{
  return Expr(READ, array, index);
}


Expr VCL::writeExpr(const Expr& array, const Expr& index, const Expr& newValue)
{
  return Expr(WRITE, array, index, newValue);
}


Expr VCL::newBVConstExpr(const std::string& s, int base)
{
  return d_theoryBitvector->newBVConstExpr(s, base);
}


Expr VCL::newBVConstExpr(const std::vector<bool>& bits)
{
  return d_theoryBitvector->newBVConstExpr(bits);
}


Expr VCL::newBVConstExpr(const Rational& r, int len)
{
  return d_theoryBitvector->newBVConstExpr(r, len);
}


Expr VCL::newConcatExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newConcatExpr(t1, t2);
}


Expr VCL::newConcatExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newConcatExpr(kids);
}


Expr VCL::newBVExtractExpr(const Expr& e, int hi, int low)
{
  return d_theoryBitvector->newBVExtractExpr(e, hi, low);
}


Expr VCL::newBVNegExpr(const Expr& t1)
{
  return d_theoryBitvector->newBVNegExpr(t1);
}


Expr VCL::newBVAndExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVAndExpr(t1, t2);
}


Expr VCL::newBVAndExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVAndExpr(kids);
}


Expr VCL::newBVOrExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVOrExpr(t1, t2);
}


Expr VCL::newBVOrExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVOrExpr(kids);
}


Expr VCL::newBVXorExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVXorExpr(t1, t2);
}


Expr VCL::newBVXorExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVXorExpr(kids);
}


Expr VCL::newBVXnorExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVXnorExpr(t1, t2);
}


Expr VCL::newBVXnorExpr(const std::vector<Expr>& kids)
{
  return d_theoryBitvector->newBVXnorExpr(kids);
}


Expr VCL::newBVNandExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVNandExpr(t1, t2);
}


Expr VCL::newBVNorExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVNorExpr(t1, t2);
}


Expr VCL::newBVLTExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVLTExpr(t1, t2);
}


Expr VCL::newBVLEExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVLEExpr(t1, t2);
}


Expr VCL::newBVSLTExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSLTExpr(t1, t2);
}


Expr VCL::newBVSLEExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSLEExpr(t1, t2);
}


Expr VCL::newSXExpr(const Expr& t1, int len)
{
  return d_theoryBitvector->newSXExpr(t1, len);
}


Expr VCL::newBVUminusExpr(const Expr& t1)
{
  return d_theoryBitvector->newBVUminusExpr(t1);
}


Expr VCL::newBVSubExpr(const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVSubExpr(t1, t2);
}


Expr VCL::newBVPlusExpr(int numbits, const std::vector<Expr>& k)
{
  return d_theoryBitvector->newBVPlusExpr(numbits, k);
}


Expr VCL::newBVMultExpr(int numbits, const Expr& t1, const Expr& t2)
{
  return d_theoryBitvector->newBVMultExpr(numbits, t1, t2);
}


Expr VCL::newFixedLeftShiftExpr(const Expr& t1, int r)
{
  return d_theoryBitvector->newFixedLeftShiftExpr(t1, r);
}


Expr VCL::newFixedConstWidthLeftShiftExpr(const Expr& t1, int r)
{
  return d_theoryBitvector->newFixedConstWidthLeftShiftExpr(t1, r);
}


Expr VCL::newFixedRightShiftExpr(const Expr& t1, int r)
{
  return d_theoryBitvector->newFixedRightShiftExpr(t1, r);
}


Expr VCL::tupleExpr(const vector<Expr>& exprs) {
  DebugAssert(exprs.size() > 0, "VCL::tupleExpr()");
  return d_theoryRecords->tupleExpr(exprs);
}


Expr VCL::tupleSelectExpr(const Expr& tuple, int index)
{
  return d_theoryRecords->tupleSelect(tuple, index);
}


Expr VCL::tupleUpdateExpr(const Expr& tuple, int index, const Expr& newValue)
{
  return d_theoryRecords->tupleUpdate(tuple, index, newValue);
}


Expr VCL::datatypeConsExpr(const string& constructor, const vector<Expr>& args)
{
  return d_theoryDatatype->datatypeConsExpr(constructor, args);
}


Expr VCL::datatypeSelExpr(const string& selector, const Expr& arg)
{
  return d_theoryDatatype->datatypeSelExpr(selector, arg);
}


Expr VCL::datatypeTestExpr(const string& constructor, const Expr& arg)
{
  return d_theoryDatatype->datatypeTestExpr(constructor, arg);
}


Expr VCL::forallExpr(const vector<Expr>& vars, const Expr& body) {
  DebugAssert(vars.size() > 0, "VCL::andExpr()");
  return d_em->newClosureExpr(FORALL, vars, body);
}


Expr VCL::existsExpr(const vector<Expr>& vars, const Expr& body) {
  return d_em->newClosureExpr(EXISTS, vars, body);
}


Op VCL::lambdaExpr(const vector<Expr>& vars, const Expr& body) {
  return d_em->newClosureExpr(LAMBDA, vars, body).mkOp();
}


Expr VCL::simulateExpr(const Expr& f, const Expr& s0,
		       const vector<Expr>& inputs, const Expr& n) {
  vector<Expr> kids;
  kids.push_back(f);
  kids.push_back(s0);
  kids.insert(kids.end(), inputs.begin(), inputs.end());
  kids.push_back(n);
  return Expr(SIMULATE, kids);
}


void VCL::setResourceLimit(unsigned limit)
{
  d_theoryCore->setResourceLimit(limit);
}


Theorem VCL::checkTCC(const Expr& tcc)
{
  Theorem tccThm;
  d_se->push();
  QueryResult res = d_se->checkValid(tcc, tccThm);
  switch (res) {
    case VALID:
      d_lastQueryTCC = tccThm;
      d_se->pop();
      break;
    case INVALID:
      throw TypecheckException("Failed TCC:\n\n  "
                               +tcc.toString()
                               +"\n\nWhich simplified to:\n\n  "
                               +simplify(tcc).toString()
                               +"\n\nAnd the last formula is not valid "
                               "in the current context.");
    case ABORT:
      throw TypecheckException("Budget exceeded:\n\n  "
                               "Unable to verify TCC:\n\n  "                               
                               +tcc.toString()
                               +"\n\nWhich simplified to:\n\n  "
                               +simplify(tcc).toString());
    case UNKNOWN:
      throw TypecheckException("Result unknown:\n\n  "
                               "Unable to verify TCC:\n\n  "
                               +tcc.toString()
                               +"\n\nWhich simplified to:\n\n  "
                               +simplify(tcc).toString()
                               +"\n\nAnd the last formula is unknown "
                               "in the current context.");
    default:
      FatalAssert(false, "Unexpected case");
  }
  return tccThm;
}


void VCL::assertFormula(const Expr& e)
{
  // Typecheck the user input
  if(!e.getType().isBool()) {
    throw TypecheckException("Non-BOOLEAN formula in ASSERT:\n  "
			     +Expr(ASSERT, e).toString()
			     +"\nDerived type of the formula:\n  "
			     +e.getType().toString());
  }

  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    if (d_translator->dumpAssertion(e)) return;
  }

  TRACE("assetFormula", "VCL::assertFormula(", e, ") {");
  // See if e was already asserted before
  if(d_userAssertions->count(e) > 0) {
    TRACE_MSG("assertFormula", "VCL::assertFormula[repeated assertion] => }");
    return;
  }
  // Check the validity of the TCC
  Theorem tccThm;
  if(getFlags()["tcc"].getBool()) {
    Expr tcc(d_theoryCore->getTCC(e));
    tccThm = checkTCC(tcc);
  }

  Theorem thm = d_se->newUserAssumption(e);
  (*d_userAssertions)[e] = UserAssertion(thm, tccThm, d_nextIdx++);
  TRACE_MSG("assertFormula", "VCL::assertFormula => }");
}


void VCL::registerAtom(const Expr& e)
{
  //TODO: add to interactive interface
  d_se->registerAtom(e);
}


Expr VCL::getImpliedLiteral()
{
  //TODO: add to interactive interface
  Theorem thm = d_se->getImpliedLiteral();
  if (thm.isNull()) return Expr();
  return thm.getExpr();
}


Expr VCL::simplify(const Expr& e) {
  //TODO: add to interactive interface
  return simplifyThm(e).getRHS();
}


Theorem VCL::simplifyThm(const Expr& e)
{
  e.getType();
  Theorem res = d_theoryCore->getExprTrans()->preprocess(e);
  Theorem simpThm =  d_theoryCore->simplify(res.getRHS());
  res = d_theoryCore->transitivityRule(res, simpThm);
  return res;
}


QueryResult VCL::query(const Expr& e)
{
  TRACE("query", "VCL::query(", e,") {");
  // Typecheck the user input
  if(!e.getType().isBool()) {
    throw TypecheckException("Non-BOOLEAN formula in QUERY:\n  "
			     +Expr(QUERY, e).toString()
			     +"\nDerived type of the formula:\n  "
			     +e.getType().toString());
  }

  if(d_dump) {
    if (d_translator->dumpQuery(e)) return UNKNOWN;
  }

  // Check the validity of the TCC
  Theorem tccThm = d_se->getCommonRules()->trueTheorem();
  if(getFlags()["tcc"].getBool()) {
    Expr tcc(d_theoryCore->getTCC(e));
    // FIXME: we have to guarantee that the TCC of 'tcc' is always valid
    tccThm = checkTCC(tcc);
  }
  Theorem res;
  QueryResult qres = d_se->checkValid(e, res);
  switch (qres) {
    case VALID:
      d_lastQuery = d_se->getCommonRules()->queryTCC(res, tccThm);
      break;
    default:
      d_lastQueryTCC = Theorem();
      d_lastQuery = Theorem3();
      d_lastClosure = Theorem3();
  }
  TRACE("query", "VCL::query => ", 
        qres == VALID ? "VALID" :
        qres == INVALID ? "INVALID" :
        qres == ABORT ? "ABORT" : "UNKNOWN", " }");

  if (d_dump) d_translator->dumpQueryResult(qres);

  return qres;
}


QueryResult VCL::checkUnsat(const Expr& e)
{
  return query(e.negate());
}


QueryResult VCL::checkContinue()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(CONTINUE), true);
  }
  vector<Expr> assertions;
  d_se->getCounterExample(assertions);
  Theorem thm;
  if (assertions.size() == 0) {
    return d_se->restart(falseExpr(), thm);
  }
  Expr eAnd = assertions.size() == 1 ? assertions[0] : andExpr(assertions);
  return d_se->restart(!eAnd, thm);
}


QueryResult VCL::restart(const Expr& e)
{
  if (d_dump) {
    d_translator->dump(Expr(RESTART, e), true);
  }
  Theorem thm;
  return d_se->restart(e, thm);
}


void VCL::returnFromCheck()
{
  //TODO: add to interactive interface
  d_se->returnFromCheck();
}


void VCL::getUserAssumptions(vector<Expr>& assumptions)
{
  // TODO: add to interactive interface
  d_se->getUserAssumptions(assumptions);
}


void VCL::getInternalAssumptions(vector<Expr>& assumptions)
{
  // TODO: add to interactive interface
  d_se->getInternalAssumptions(assumptions);
}


void VCL::getAssumptions(vector<Expr>& assumptions)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(ASSUMPTIONS), true);
  }
  d_se->getAssumptions(assumptions);
}


void VCL::getAssumptionsUsed(vector<Expr>& assumptions)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_ASSUMPTIONS), true);
  }
  Theorem thm = d_se->lastThm();
  if (thm.isNull()) return;
  thm.getLeafAssumptions(assumptions);
}


void VCL::getCounterExample(vector<Expr>& assertions, bool inOrder)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(COUNTEREXAMPLE), true);
  }
  if (!(*d_flags)["translate"].getBool())
    d_se->getCounterExample(assertions, inOrder);
}


void VCL::getConcreteModel(ExprMap<Expr> & m)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(COUNTERMODEL), true);
  }
  if (!(*d_flags)["translate"].getBool())
    d_se->getConcreteModel(m);
}


bool VCL::inconsistent(vector<Expr>& assumptions)
{
  // TODO: add to interactive interface
  if (d_theoryCore->inconsistent()) {
    // TODO: do we need local getAssumptions?
    getAssumptions(d_theoryCore->inconsistentThm().getAssumptionsRef(),
		   assumptions);
    return true;
  }
  return false;
}


bool VCL::incomplete() {
  // TODO: add to interactive interface
  // Return true only after a failed query
  return (d_lastQuery.isNull() && d_theoryCore->incomplete());
}


bool VCL::incomplete(vector<string>& reasons) {
  // TODO: add to interactive interface
  // Return true only after a failed query
  return (d_lastQuery.isNull() && d_theoryCore->incomplete(reasons));
}


Proof VCL::getProof()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_PROOF), true);
  }

  if(d_lastQuery.isNull())
    throw EvalException
      ("Method getProof() (or command DUMP_PROOF)\n"
       " must be called only after a Valid QUERY");
  return d_se->getProof();
}


Expr VCL::getTCC(){
  static Expr null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_TCC), true);
  }
  if(d_lastQueryTCC.isNull()) return null;
  else return d_lastQueryTCC.getExpr();
}


void VCL::getAssumptionsTCC(vector<Expr>& assumptions)
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_TCC_ASSUMPTIONS), true);
  }
  if(d_lastQuery.isNull())
    throw EvalException
      ("Method getAssumptionsTCC() (or command DUMP_TCC_ASSUMPTIONS)\n"
       " must be called only after a Valid QUERY");
  getAssumptions(d_lastQueryTCC.getAssumptionsRef(), assumptions);
}


Proof VCL::getProofTCC() {
  static Proof null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_TCC_PROOF), true);
  }
  if(d_lastQueryTCC.isNull()) return null;
  else return d_lastQueryTCC.getProof();
}


Expr VCL::getClosure() {
  static Expr null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_CLOSURE), true);
  }
  if(d_lastClosure.isNull() && !d_lastQuery.isNull()) {
    // Construct the proof of closure and cache it in d_lastClosure
    d_lastClosure = deriveClosure(d_lastQuery);
  }
  if(d_lastClosure.isNull()) return null;
  else return d_lastClosure.getExpr();
}


Proof VCL::getProofClosure() {
  static Proof null;
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(DUMP_CLOSURE_PROOF), true);
  }
  if(d_lastClosure.isNull() && !d_lastQuery.isNull()) {
    // Construct the proof of closure and cache it in d_lastClosure
    d_lastClosure = deriveClosure(d_lastQuery);
  }
  if(d_lastClosure.isNull()) return null;
  else return d_lastClosure.getProof();
}


int VCL::stackLevel()
{
  return d_stackLevel->get();
}


void VCL::push()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(PUSH), true);
  }
  d_se->push();
  d_stackLevel->set(stackLevel()+1);
}


void VCL::pop()
{
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(POP), true);
  }
  if (stackLevel() == 0) {
    throw EvalException
      ("POP called with no previous call to PUSH");
  }
  int level = stackLevel();
  while (level == stackLevel())
    d_se->pop();
}


void VCL::popto(int toLevel)
{
  // Check if the ofstream is open (as opposed to the command line flag)
  if(d_dump) {
    d_translator->dump(Expr(POPTO, ratExpr(toLevel, 1)), true);
  }
  if (toLevel < 0) toLevel = 0;
  while (stackLevel() > toLevel) {
    d_se->pop();
  }
}


int VCL::scopeLevel()
{
  return d_cm->scopeLevel();
}


void VCL::pushScope()
{
  throw EvalException ("Scope-level push/pop is no longer supported");
  d_cm->push();
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(PUSH_SCOPE), true);
  }
  IF_DEBUG(if((*d_flags)["dump-trace"].getString() != "")
	   dumpTrace(scopeLevel()));
}


void VCL::popScope()
{
  throw EvalException ("Scope-level push/pop is no longer supported");
  if(d_dump) {
    d_translator->dump(d_em->newLeafExpr(POP_SCOPE), true);
  }
  if (scopeLevel() == 1) {
    cout << "Cannot POP from scope level 1" << endl;
  }
  else d_cm->pop();
  IF_DEBUG(if((*d_flags)["dump-trace"].getString() != "")
	   dumpTrace(scopeLevel()));
}


void VCL::poptoScope(int toLevel)
{
  throw EvalException ("Scope-level push/pop is no longer supported");
  if(d_dump) {
    d_translator->dump(Expr(POPTO_SCOPE, ratExpr(toLevel, 1)), true);
  }
  if (toLevel < 1) {
    d_cm->popto(0);
    d_cm->push();
  }
  else d_cm->popto(toLevel);
  IF_DEBUG(if((*d_flags)["dump-trace"].getString() != "")
	   dumpTrace(scopeLevel()));
}


Context* VCL::getCurrentContext()
{
  return d_cm->getCurrentContext();
}


void VCL::loadFile(const string& fileName, InputLanguage lang,
		   bool interactive) {
  // TODO: move these?
  Parser parser(this, lang, interactive, fileName);
  VCCmd cmd(this, &parser);
  cmd.processCommands();
}


void VCL::loadFile(istream& is, InputLanguage lang,
		   bool interactive) {
  // TODO: move these?
  Parser parser(this, lang, is, interactive);
  VCCmd cmd(this, &parser);
  cmd.processCommands();
}


unsigned long VCL::printMemory()
{
  cout << "VCL: " <<
    sizeof(VCL) + d_theories.size() * sizeof(Theory*)
       << endl;

  cout << "Context: " << d_cm->getMemory() << endl;
  return 0;
//   d_em->printMemory();
//   d_tm->printMemory();
//   d_translator->printMemory();
//   d_se->printMemory();

//   d_theoryCore->printMemory();
  
}
