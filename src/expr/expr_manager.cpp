/*****************************************************************************/
/*!
 * \file expr_manager.cpp
 * 
 * Author: Sergey Berezin
 * 
 * Created: Wed Dec  4 14:20:56 2002
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

#include "expr_manager.h"
#include "command_line_flags.h"
#include "expr_stream.h"
#include "pretty_printer.h"
#include "memory_manager_malloc.h"
#include "memory_manager_chunks.h"

using namespace CVC3;

using namespace std;

// File-local function which registers all the commonly declared
// kinds (defined below)
static void registerKinds(ExprManager& em);

// Constructor
ExprManager::ExprManager(ContextManager* cm, const CLFlags& flags)
  // Initial number of buckets is 1024 (it's kinda arbitrary)
  : d_cm(cm), d_index(0), d_flagCounter(1), d_prettyPrinter(NULL),
    d_printDepth(&(flags["print-depth"].getInt())),
    d_withIndentation(&(flags["indent"].getBool())),
    d_indent(0), d_indentTransient(0),
    d_lineWidth(&(flags["width"].getInt())),
    d_inputLang(&(flags["lang"].getString())),
    d_outputLang(&(flags["output-lang"].getString())),
    d_dagPrinting(&(flags["dagify-exprs"].getBool())),
    d_mmFlag(flags["mm"].getString()),
    d_exprSet(1024, HashEV(this), EqEV()),
    d_mm(EXPR_VALUE_TYPE_LAST),
    d_simpCacheTagCurrent(1), d_disableGC(false), d_postponeGC(false),
    d_typeComputer(NULL)
{
  // Initialize the notifier
  d_notifyObj = new ExprManagerNotifyObj(this, d_cm->getCurrentContext());

  // Initialize core memory managers
  if(d_mmFlag == "chunks") {
    d_mm[EXPR_VALUE] = new MemoryManagerChunks(sizeof(ExprValue));
    d_mm[EXPR_NODE] = new MemoryManagerChunks(sizeof(ExprNode));
    d_mm[EXPR_APPLY] = new MemoryManagerChunks(sizeof(ExprApply));
    d_mm[EXPR_STRING] = new MemoryManagerChunks(sizeof(ExprString));
    d_mm[EXPR_RATIONAL] = new MemoryManagerChunks(sizeof(ExprRational));
    d_mm[EXPR_UCONST] = new MemoryManagerChunks(sizeof(ExprVar));
    d_mm[EXPR_SYMBOL] = new MemoryManagerChunks(sizeof(ExprSymbol));
    d_mm[EXPR_BOUND_VAR] = new MemoryManagerChunks(sizeof(ExprBoundVar));
    d_mm[EXPR_CLOSURE] = new MemoryManagerChunks(sizeof(ExprClosure));
    d_mm[EXPR_SKOLEM] = new MemoryManagerChunks(sizeof(ExprSkolem));
    d_mm[EXPR_THEOREM] = new MemoryManagerChunks(sizeof(ExprTheorem));
  } else {
    d_mm[EXPR_VALUE] = new MemoryManagerMalloc();
    d_mm[EXPR_NODE] = new MemoryManagerMalloc();
    d_mm[EXPR_APPLY] = new MemoryManagerMalloc();
    d_mm[EXPR_STRING] = new MemoryManagerMalloc();
    d_mm[EXPR_RATIONAL] = new MemoryManagerMalloc();
    d_mm[EXPR_UCONST] = new MemoryManagerMalloc();
    d_mm[EXPR_SYMBOL] = new MemoryManagerMalloc();
    d_mm[EXPR_BOUND_VAR] = new MemoryManagerMalloc();
    d_mm[EXPR_CLOSURE] = new MemoryManagerMalloc();
    d_mm[EXPR_SKOLEM] = new MemoryManagerMalloc();
    d_mm[EXPR_THEOREM] = new MemoryManagerMalloc();
  }
  registerKinds(*this);
  
  d_bool = newLeafExpr(BOOLEAN);
  d_false = newLeafExpr(FALSE_EXPR);
  d_false.setType(Type::typeBool(this));
  d_true = newLeafExpr(TRUE_EXPR);
  d_true.setType(Type::typeBool(this));

  IF_DEBUG(d_inRebuild = false);
}

// Destructor
ExprManager::~ExprManager() {
  FatalAssert(d_emptyVec.size()==0, "~ExprManager()");
  delete d_notifyObj;
  // Make sure garbage collector doesn't get in the way
  d_disableGC = false;		//  clear() will assert this.
  clear();
  d_disableGC = true;
  // Destroy memory managers
  TRACE_MSG("delete", "~ExprManager: deleting d_mm's {");
  for(size_t i=0; i<d_mm.size(); ++i)
    delete d_mm[i];

  TRACE_MSG("delete", "~ExprManager: finished deleting d_mm's }");
}


void ExprManager::clear() {
  FatalAssert(isActive(), "ExprManager::clear()");
  // Make ExprManager inactive, but keep all the Exprs intact
  // Remove all internal expressions.
  d_disableGC = true;

  TRACE("delete", "clear: number of remaining Exprs: ",
	d_exprSet.size(), flush);

  FatalAssert(d_nullExpr.isNull(), "ExprManager::clear()");

  // Set class-local Exprs to Null
  d_bool = Expr();
  d_false = Expr();
  d_true = Expr();

  // Save all the pointers, clear the hash set, then free the
  // pointers.  Erasing one pointer at a time requires rehashing,
  // which will segfault if some pointers are already deleted.
  vector<ExprValue*> exprs;
  exprs.reserve(d_exprSet.size());
  TRACE_MSG("delete", "clear:() collecting exprs { ");
  IF_DEBUG(int n(0));
  for(ExprValueSet::iterator i=d_exprSet.begin(), iend=d_exprSet.end();
      i!=iend; ++i) {
    TRACE("delete", "expr[", n++, "]");
    exprs.push_back(*i);
  }
  TRACE_MSG("delete", "clear(): finished collecting exprs }");
  d_exprSet.clear();
  TRACE_MSG("delete", "clear(): deleting exprs { ");
  for(vector<ExprValue*>::iterator i=exprs.begin(), iend=exprs.end();
      i!=iend; ++i) {
    ExprValue *pExpr= *i;
    size_t tp(pExpr->getMMIndex()); // which memory manager to use
    delete (pExpr);
    d_mm[tp]->deleteData(pExpr);
  }
  TRACE_MSG("delete", "clear(): finished deleting exprs }");

}


bool ExprManager::isActive() { return !d_disableGC; }


// Garbage collect the ExprValue pointer
void ExprManager::gc(ExprValue* ev) {
  if(!d_disableGC) {
    d_exprSet.erase(ev);
    if(d_postponeGC) d_postponed.push_back(ev);
    else {
      size_t tp(ev->getMMIndex());
      delete ev;
      d_mm[tp]->deleteData(ev);
    }
  }
}

void
ExprManager::resumeGC() {
  d_postponeGC = false; 
  while(d_postponed.size()>0) {
    ExprValue* ev = d_postponed.back();
    size_t tp(ev->getMMIndex());
    d_postponed.pop_back();
    delete ev;
    d_mm[tp]->deleteData(ev);
  }
}


// Rebuild the Expr with this ExprManager if it belongs to another
// ExprManager
Expr ExprManager::rebuild(const Expr& e) {
  //  TRACE("expr", "rebuild(", e, ") {");
  // Shouldn't rebuild a Null Expr (it's a bug)
  DebugAssert(!e.isNull(), "ExprManager::rebuild called on Null Expr");
  // Both ExprManagers must be active
  DebugAssert(isActive() && e.getEM()->isActive(),
	      "ExprManager::rebuild is called on inactive ExprManager");
  // If e has the same ExprManager, no rebuilding is necessary
  if(e.isNull() || (e.getEM() == this)) {
    //    TRACE_MSG("expr", "rebuild (same EM) => }");
    return e;
  }
  // Gotta rebuild
  DebugAssert(!d_inRebuild, "ExprManager::rebuild()");
  IF_DEBUG(ScopeWatcher sw(&d_inRebuild));
  // First, clear the cache
  if(d_rebuildCache.size() > 0) d_rebuildCache.clear();
  Expr res = rebuildRec(e);
  // Leave no trail behind (free up Exprs)
  if(d_rebuildCache.size() > 0) d_rebuildCache.clear();
  //  TRACE("expr", "rebuild => ", e, " }");
  return res;
}


Expr ExprManager::rebuildRec(const Expr& e) {
  DebugAssert(d_inRebuild, "ExprManager::rebuildRec("+e.toString()+")");
  // Check cache
  ExprHashMap<Expr>::iterator j=d_rebuildCache.find(e),
    jend=d_rebuildCache.end();
  if(j!=jend) return (*j).second;
  
  ExprValue* ev = e.d_expr->rebuild(this);
  // Uniquify the pointer
  ExprValueSet::iterator i(d_exprSet.find(ev)), iend(d_exprSet.end());
  if(i != iend) {
    MemoryManager* mm = getMM(ev->getMMIndex());
    delete ev;
    mm->deleteData(ev);
    ev = *i;
  } else {
    ev->setIndex(nextIndex());
    installExprValue(ev);
  }
  // Use non-uniquifying Expr() constructor
  Expr res(ev);
  // Cache the result
  d_rebuildCache[e] = res;

  // Rebuild the type too
  Type t;
  if (!e.d_expr->d_type.isNull()) {
    t = Type(rebuildRec(e.d_expr->d_type.getExpr()));
  }
  if (ev->d_type.isNull()) ev->d_type = t;
  else if (ev->d_type != t) {
    throw Exception("Types don't match in rebuildRec");
  }

  return res;
}


ExprValue* ExprManager::newExprValue(ExprValue* ev) {
  DebugAssert(isActive(), "ExprManager::newExprValue(ExprValue*)");
  ExprValueSet::iterator i(d_exprSet.find(ev)), iend(d_exprSet.end());
  if(i != iend) return (*i);
  // No such ExprValue.  Create a clean copy, insert it into the set
  // and return the new pointer.
  ExprValue* p_ev = ev->copy(this, nextIndex());
  installExprValue(p_ev);
  return p_ev;
}


// ExprValue* ExprManager::newExprValue(const Expr& op,
// 				     const vector<Expr>& kids) {
//   // Check if op and kids have the same ExprManager
//   DebugAssert(isActive(), "ExprManager::newExprValue(op, kids)");
//   DebugAssert(this == op.getEM(),
// 	      "ExprManager::newExprValue(op, kids): op is from a wrong "
// 	      "ExprManager/ValidityChecker, call importExpr() first:\n"
// 	      +op.toString());
//   IF_DEBUG(
//     for(vector<Expr>::const_iterator i=kids.begin(), iend=kids.end();
// 	i!=iend; ++i)
//       DebugAssert(!i->isNull() && (i->getEM() == this),
// 		  "ExprManager::newExprValue(op, kids): the child is"
// 		  " from a wrong instance of ExprManager/ValidityChecker,"
// 		  "call importExpr() first:\n"
// 		  +i->toString());
//     );
//   ExprValue* res = op.d_expr->copy(this, kids);
//   ExprValueSet::iterator i(d_exprSet.find(res)), iend(d_exprSet.end());
//   if(i != iend) {
//     MemoryManager* mm = getMM(res->getMMIndex());
//     delete res;
//     mm->deleteData(res);
//     return (*i);
//   } else {
//     res->setIndex(nextIndex());
//     installExprValue(res);
//     return res;
//   }
// }


void ExprManager::installExprValue(ExprValue* p_ev)
{
  DebugAssert(isActive(), "ExprManager::installExprValue(ExprValue*)");
//   int maxHeight = 0;
//   p_ev->d_highestKid = 0;
//   for (unsigned i = 0; i < p_ev->arity(); i++)
//   {
//     int height = p_ev->getKids()[i].getHeight();
//     if (height > maxHeight)
//     {
//       maxHeight = height;
//       p_ev->d_highestKid = i;
//     }
//   }

//   if (p_ev->d_kind == ITE && p_ev->arity() == 3)
//   {
//     if (p_ev->getKids()[1].getHeight() > p_ev->getKids()[2].getHeight())
//       p_ev->d_highestKid = 1;
//     else
//       p_ev->d_highestKid = 2;
//   }

//   switch (p_ev->d_kind) {
//   case NOT: case AND: case OR: case ITE: case IFF: case IMPLIES:
//     maxHeight++;
//   }
//   p_ev->d_height = maxHeight;

  d_exprSet.insert(p_ev);
}

//! Set initial indentation.  Returns the previous permanent value.
int 
ExprManager::indent(int n, bool permanent) {
  int ret(d_indent);
  d_indentTransient = n;
  if(permanent) d_indent = n;
  return ret;
}

//! Increment the current transient indentation by n
/*! If the second argument is true, sets the result as permanent.
  \return previous permanent value. */
int
ExprManager::incIndent(int n, bool permanent) {
  int ret(d_indent);
  d_indentTransient += n;
  if(permanent) d_indent = d_indentTransient;
  return ret;
}

// Various options
InputLanguage
ExprManager::getInputLang() const {
  return getLanguage(*d_inputLang);
}
 

InputLanguage
ExprManager::getOutputLang() const {
  const std::string* langPtr
    = (*d_outputLang == "")? d_inputLang : d_outputLang;
  return getLanguage(*langPtr);
}


// Register a new kind.  The kind may already be regestered under
// the same name, but if the name is different, it's an error.
void ExprManager::newKind(int kind, const string &name, bool isType) {
  if(d_kindMap.count(kind) == 0) {
    d_kindMap[kind] = name;
    if(isType) d_typeKinds.insert(kind);
  }
  else if(d_kindMap[kind] != name) {
    DebugAssert(false, "CVC3::ExprManager::newKind(kind = "
		+ int2string(kind) + ", name = " + name
		+ "): \n" + 
		"this kind is already registered with a different name: "
		+ d_kindMap[kind]);
  }
  if(d_kindMapByName.count(name) == 0)
    d_kindMapByName[name] = kind;
  else if(d_kindMapByName[name] != kind) {
    DebugAssert(false, "CVC3::ExprManager::newKind(kind = "
		+ int2string(kind) + ", name = " + name
		+ "): \n" + 
		"this kind name is already registered with a different index: "
		+ int2string(d_kindMapByName[name]));
  }
}

// Register a printer
void ExprManager::registerPrettyPrinter(PrettyPrinter& printer) {
  DebugAssert(d_prettyPrinter==NULL, "ExprManager:registerPrettyPrinter():"
	      " printer is already registered");
  d_prettyPrinter = &printer;
}

// Unregister a printer
void ExprManager::unregisterPrettyPrinter() {
  FatalAssert(d_prettyPrinter!=NULL, "ExprManager:unregisterPrettyPrinter():"
	      " printer is not registered");
  d_prettyPrinter = NULL;
}


const string& ExprManager::getKindName(int kind) {
  DebugAssert(d_kindMap.count(kind) > 0,
	      ("CVC3::ExprManager::getKindName(kind = "
	       + int2string(kind) + "): kind is not registered.").c_str());
  return d_kindMap[kind];
}

int ExprManager::getKind(const string& name) {
  std::hash_map<std::string, int, HashString>::iterator
    i=d_kindMapByName.find(name),
    iend=d_kindMapByName.end();
  if(i==iend) return NULL_KIND;
  else return (*i).second;
}


size_t ExprManager::registerSubclass(size_t sizeOfSubclass) {
  size_t idx(d_mm.size());
  if(d_mmFlag == "chunks")
    d_mm.push_back(new MemoryManagerChunks(sizeOfSubclass));
  else
    d_mm.push_back(new MemoryManagerMalloc());

  FatalAssert(d_mm.back() != NULL, "Out of memory");
  return idx;
}


void ExprManager::computeType(const Expr& e) {
  DebugAssert(d_typeComputer, "No type computer installed");
  d_typeComputer->computeType(e);
  DebugAssert(!e.getType().getExpr().isNull(), "Type not set by computeType");
}


void ExprManager::checkType(const Expr& e) {
  DebugAssert(d_typeComputer, "No type computer installed");
  if (!e.isValidType()) d_typeComputer->checkType(e);
  DebugAssert(e.isValidType(), "Type not checked by checkType");
}


// Kind registration macro
#define REG(k) em.newKind(k, #k)
#define REG_TYPE(k) em.newKind(k, #k, true)

static void registerKinds(ExprManager& em) {
  // Register type kinds
  REG_TYPE(BOOLEAN);
  //  REG(TUPLE_TYPE);
  REG_TYPE(ANY_TYPE);
  REG_TYPE(ARROW);
  REG_TYPE(TYPE);
  REG_TYPE(TYPEDECL);
  REG_TYPE(TYPEDEF);
  REG_TYPE(SUBTYPE);

  // Register expression (non-type) kinds 
  REG(NULL_KIND);

  REG(RAW_LIST);
  REG(STRING_EXPR);
  REG(RATIONAL_EXPR);
  REG(TRUE_EXPR);
  REG(FALSE_EXPR);
  
  REG(EQ);
  REG(NEQ);
  
  REG(NOT);
  REG(AND);
  REG(OR);
  REG(XOR);
  REG(IFF);
  REG(IMPLIES);

  REG(AND_R);
  REG(IFF_R);
  REG(ITE_R);

  REG(ITE);
  
  REG(FORALL);
  REG(EXISTS);
  
  REG(UFUNC);
  REG(APPLY);

  REG(ASSERT);
  REG(QUERY);
  REG(CHECKSAT);
  REG(CONTINUE);
  REG(RESTART);
  REG(DBG);
  REG(TRACE);
  REG(UNTRACE);
  REG(OPTION);
  REG(HELP);
  REG(TRANSFORM);
  REG(PRINT);
  REG(CALL);
  REG(ECHO);
  REG(INCLUDE);
  REG(DUMP_PROOF);
  REG(DUMP_ASSUMPTIONS);
  REG(DUMP_SIG);
  REG(DUMP_TCC);
  REG(DUMP_TCC_ASSUMPTIONS);
  REG(DUMP_TCC_PROOF);
  REG(DUMP_CLOSURE);
  REG(DUMP_CLOSURE_PROOF);
  REG(WHERE);
  REG(ASSERTIONS);
  REG(ASSUMPTIONS);
  REG(COUNTEREXAMPLE);
  REG(COUNTERMODEL);
  REG(PUSH);
  REG(POP);
  REG(POPTO);
  REG(PUSH_SCOPE);
  REG(POP_SCOPE);
  REG(POPTO_SCOPE);
  REG(CONTEXT);
  REG(FORGET);
  REG(GET_TYPE);
  REG(CHECK_TYPE);
  REG(GET_CHILD);
  REG(SUBSTITUTE);
  REG(SEQ);

  // Kinds used mostly in the parser

  REG(TCC);
  REG(ID);
  REG(VARDECL);
  REG(VARDECLS);


  REG(BOUND_VAR);
  REG(BOUND_ID);

  REG(SKOLEM_VAR);
  REG(THEOREM_KIND);

//   REG(UPDATE);
//   REG(UPDATE_SELECT);

//   REG(RECORD_TYPE);
//   REG(RECORD);
//   REG(RECORD_SELECT);
//   REG(RECORD_UPDATE);

//   REG(TUPLE);
//   REG(TUPLE_SELECT);
//   REG(TUPLE_UPDATE);

//   REG(SUBRANGE);

//   REG(SCALARTYPE);
//   REG(DATATYPE);
//   REG(THISTYPE);
//   REG(CONSTRUCTOR);
//   REG(SELECTOR);
//   REG(TESTER);
  //  REG(DATATYPE_UPDATE);

  REG(IF);
  REG(IFTHEN);
  REG(ELSE);
  REG(COND);

  REG(LET);
  REG(LETDECLS);
  REG(LETDECL);

  REG(LAMBDA);
  REG(SIMULATE);

  REG(CONST);
  REG(VARLIST);
  REG(UCONST);
  REG(DEFUN);

  // Arithmetic types and operators
//   REG(REAL);
//   REG(INT);

//   REG(UMINUS);
//   REG(PLUS);
//   REG(MINUS);
//   REG(MULT);
//   REG(DIVIDE);
//   REG(POW);
//   REG(INTDIV);
//   REG(MOD);
//   REG(LT);
//   REG(LE);
//   REG(GT);
//   REG(GE);
//   REG(IS_INTEGER);
//   REG(NEGINF);
//   REG(POSINF);
//   REG(FLOOR);
}


void ExprManagerNotifyObj::notifyPre() {
  d_em->postponeGC();
}


void ExprManagerNotifyObj::notify() {
  d_em->resumeGC();
}
